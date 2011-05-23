{-# LANGUAGE ImplicitParams, NamedFieldPuns #-}
import Data.SBV
import Data.Set (toList)
import Data.List (sort, nub)
import Data.Bits
import Data.Monoid
import Control.Monad.Trans (MonadIO, liftIO)
import qualified Data.Char
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex (parseRegex)
import Test.QuickCheck (quickCheck)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import System.Environment

type Len = Int
type Str = [SWord8]
type Offset = SWord8

maxHits = 30
minLength = 0
maxLength = 100
maxRepeat = 3

defaultRegex = "abc$"
parse r = case parseRegex r of
    Right (pattern, _) -> pattern
    Left x -> error $ show x

possibleLengths :: Pattern -> IntSet
possibleLengths pat = case pat of
    PGroup _ p -> possibleLengths p
    PCarat{} -> zero
    PDollar{} -> zero
    PQuest p -> possibleLengths p `mappend` zero
    PDot{} -> one
    POr ps -> mconcat (map possibleLengths ps)
    PChar{} -> one
    PConcat [] -> mempty
    PConcat ps -> foldl1 sumSets (map possibleLengths ps)
        where
        sumSets s1 s2 = IntSet.unions [ IntSet.map (+elm) s2 | elm <- IntSet.elems s1 ]
    PAny {} -> one
    PAnyNot {} -> one
    PEscape {} -> one -- XXX Capture
    {-
    {getPatternChar = ch} -> case ch of
        'n' -> cond (ord '\n' .== cur)
        't' -> cond (ord '\t' .== cur)
        'd' -> oneOf ['0'..'9']
        'w' -> oneOf $ '_' : ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z']
        _ | Data.Char.isDigit ch -> 
            let from = readCapture captureAt num
                len = readCapture captureLen num
                num = Data.Char.ord ch - Data.Char.ord '0'
             in ite (matchCapture (from :: SWord8) len 0) s{ pos = pos+len } __FAIL__
          | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
          | otherwise  -> cond (ord ch .== cur)
    -}
    PBound low (Just high) p -> manyTimes p low high
    PBound low _ p -> manyTimes p low (low+maxRepeat)
    PPlus p -> manyTimes p 1 (maxRepeat+1)
    PStar _ p -> manyTimes p 0 maxRepeat
    _ -> error $ show pat
    where
    one = IntSet.singleton 1
    zero = IntSet.singleton 0
    manyTimes :: Pattern -> Int -> Int -> IntSet
    manyTimes p low high = let lenP = possibleLengths p in 
        IntSet.unions [ IntSet.map (*i) lenP | i <- [low..high] ]

exactMatch :: (?pat :: Pattern) => Len -> Symbolic SBool
exactMatch len = do
    str <- mkFreeVars len
    initialBits <- free "bits"
    let Status{ ok, pos, bits } = let ?str = str in match Status
            { ok = true
            , pos = 0
            , bits = initialBits
            , captureAt = minBound
            , captureLen = minBound
            }
    return (bits .== 0 &&& pos .== toEnum len &&& ok)

data Status = Status
    { ok :: SBool
    , pos :: Offset
    , bits :: SWord64
    , captureAt :: Captures
    , captureLen :: Captures
    }

type Captures = SWord64
type Idx = Word8

instance Mergeable Status where
  symbolicMerge t s1 s2 = Status
    { ok = symbolicMerge t (ok s1) (ok s2)
    , pos = symbolicMerge t (pos s1) (pos s2)
    , bits = symbolicMerge t (bits s1) (bits s2)
    , captureAt = symbolicMerge t (captureAt s1) (captureAt s2)
    , captureLen = symbolicMerge t (captureLen s1) (captureLen s2)
    }

choice :: (?str :: Str, ?pat :: Pattern) => SWord64 -> [SWord64 -> Status] -> Status
choice _ [] = error "X"
choice bits [a] = a bits
choice bits [a, b] = ite (lsb bits) (a bits') (b bits')
    where
    bits' = bits `shiftR` 1
choice bits xs = ite (lsb bits)
    (choice bits' $ take half xs)
    (choice bits' $ drop half xs)
    where
    half = length xs `div` 2
    bits' = bits `shiftR` 1

writeCapture :: Captures -> Int -> SWord8 -> Captures
writeCapture cap idx val = foldl writeBit cap ([0..7] `zip` blastLE val)
    where
    writeBit c (i, bit) = setBitTo c (idx * 8 + i) bit

readCapture cap idx = fromBitsLE [ bitValue cap (idx * 8 + i) | i <- [ 0..7 ] ]
    
match :: (?str :: Str, ?pat :: Pattern) => Status -> Status
match s@Status{ ok, pos, bits, captureAt, captureLen } = ite (isFailedMatch ||| isOutOfBounds) __FAIL__ $ case ?pat of
    PGroup (Just idx) p -> let s'@Status{ pos = pos' } = next p in s'
        { captureAt = writeCapture captureAt idx pos
        , captureLen = writeCapture captureLen idx (pos' - pos)
        }
    PGroup _ p -> next p
    PCarat{} -> ite ((pos .== 0) ||| (charAt (pos-1) .== ord '\n')) s __FAIL__
    PDollar{} -> ite ((pos .== toEnum (length ?str)) ||| (charAt (pos+1) .== ord '\n')) s __FAIL__
    PQuest p -> choice bits [\b -> let ?pat = p in match s{ bits = b }, const s]
    PDot{} -> cond (cur .>= ord ' ' &&& cur .<= ord '~')
    POr [p] -> next p
    POr ps -> choice bits $ map (\p -> \b -> let ?pat = p in match s{ bits = b }) ps
    PChar{ getPatternChar = ch } -> cond (ord ch .== cur)
    PConcat [p] -> next p
    PConcat ps -> step ps s
        where
        step [] s' = s'
        step (p:ps) s' = 
            let s''@Status{ ok } = let ?pat = p in match s'
                res = step ps s''
             in ite ok res __FAIL__
    PAny {getPatternSet = pset} -> case pset of
        PatternSet (Just cset) _ _ _ -> oneOf $ toList cset
        _ -> error "TODO"
    PAnyNot {getPatternSet = pset} -> case pset of
        PatternSet (Just cset) _ _ _ -> noneOf $ toList cset
        _ -> error "TODO"
    PEscape {getPatternChar = ch} -> case ch of
        'n' -> cond (ord '\n' .== cur)
        't' -> cond (ord '\t' .== cur)
        'd' -> oneOf ['0'..'9']
        'w' -> oneOf $ '_' : ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z']
        _ | Data.Char.isDigit ch -> 
            let from = readCapture captureAt num
                len = readCapture captureLen num
                num = Data.Char.ord ch - Data.Char.ord '0'
             in ite (matchCapture (from :: SWord8) len 0) s{ pos = pos+len } __FAIL__
          | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
          | otherwise  -> cond (ord ch .== cur)
    PBound low (Just high) p -> manyTimes p [low..high]
    PBound low _ p -> manyTimes p [low..low+maxRepeat]
    PPlus p ->
        let s'@Status{ ok = ok, pos = pos'} = next p
            res = let ?pat = PStar True p in match s'
         in ite ok res s'
    PStar _ p -> next $ PBound 0 Nothing p
    _ -> error $ show ?pat
    where
    next p = let ?pat = p in match s
    isOutOfBounds = pos .> toEnum (length ?str)
    isFailedMatch = bnot ok
    manyTimes :: (?pat :: Pattern, ?str :: Str) => Pattern -> [Int] -> Status
    manyTimes p times = choice bits $
        map (\iter -> \b -> let ?pat = PConcat (replicate iter p) in match s{ bits = b }) times
    cur = charAt pos
    charAt = select ?str 0
    cond b = ite b s{ pos = pos+1 } __FAIL__
    oneOf cs = cond $ bOr [ ord ch .== cur | ch <- cs ]
    noneOf cs = cond $ bAnd ((cur .>= ord ' ') : (cur .<= ord '~') : [ ord ch ./= cur | ch <- cs ])
    ord = toEnum . Data.Char.ord
    matchCapture :: SWord8 -> SWord8 -> SWord8 -> SBool
    matchCapture from len off = (len .<= off) |||
        (charAt (pos+off) .== charAt (from+off) &&& matchCapture from len (off+1))
    __FAIL__ = s{ ok = false, pos = maxBound, bits = maxBound }

main = do
    args <- getArgs
    case args of
        [] -> do
            prog <- getProgName
            if prog == "<interactive>" then run defaultRegex else do
                fail $ "Usage: " ++ prog ++ " regex [regex...]"
        (r:_) -> run r

run regex = do
    let ?pat = parse regex
    let lens = IntSet.toAscList $ possibleLengths ?pat
    tryWith lens 0

tryWith :: (?pat :: Pattern) => [Int] -> Int -> IO ()
tryWith [] acc = return ()
tryWith (len:lens) acc = if len > maxLength then return () else do
    allRes <- allSat $ exactMatch len
    case allRes of 
        AllSatResult [] -> tryWith lens acc
        AllSatResult xs -> do
            let models = (take (maxHits - acc) $ sort $ map getModel $ take maxHits xs)
            mapM_ disp' models
            let acc' = length models + acc
            if (acc' >= maxHits) then return () else tryWith lens acc'
    where
    fst' :: ([Word8], [Bool]) -> [Word8]
    fst' = fst

disp' :: ([Word8], Word64) -> IO ()
disp' (str, choices) = do
    putStr (show choices)
    putStr "\t["
    putStr $ map chr str
    putStr "]\n"
    where
    chr :: Word8 -> Char
    chr = Data.Char.chr . fromEnum

disp :: [Word8] -> IO ()
disp str = do
    putStrLn $ map chr str
    where
    chr :: Word8 -> Char
    chr = Data.Char.chr . fromEnum
