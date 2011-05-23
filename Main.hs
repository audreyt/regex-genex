{-# LANGUAGE ImplicitParams, NamedFieldPuns #-}
import Data.SBV
import Data.Set (toList)
import Data.List (sort, nub)
import Data.Bits
import Data.Monoid
import System.IO
import Control.Monad (foldM)
import Control.Monad.State
import Control.Monad.Trans (MonadIO, liftIO)
import qualified Data.Char
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex (parseRegex)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import System.Environment

type Len = Int
type Str = [SWord8]
type Offset = SWord8
type Flips = SWord64
type Captures = SWord64

maxHits = 100
minLength = 0
maxLength = 100
maxRepeat = 3 -- 7 and 15 are also good

lengths p = IntSet.toList . fst $ runState (possibleLengths $ parse p) mempty

defaultRegex = "a(b|c)d{2,3}e*"
parse r = case parseRegex r of
    Right (pattern, _) -> pattern
    Left x -> error $ show x

type GroupLens = IntMap IntSet

possibleLengths :: Pattern -> State GroupLens IntSet
possibleLengths pat = case pat of
    PGroup (Just idx) p -> do
        lenP <- possibleLengths p
        modify $ IntMap.insert idx lenP
        return lenP
    PGroup _ p -> possibleLengths p
    PCarat{} -> zero
    PDollar{} -> zero
    PQuest p -> fmap (`mappend` IntSet.singleton 0) $ possibleLengths p
    PDot{} -> one
    POr ps -> fmap mconcat $ mapM possibleLengths ps
    PChar{} -> one
    PConcat [] -> return mempty
    PConcat ps -> fmap (foldl1 sumSets) (mapM possibleLengths ps)
        where
        sumSets s1 s2 = IntSet.unions [ IntSet.map (+elm) s2 | elm <- IntSet.elems s1 ]
    PAny {} -> one
    PAnyNot {} -> one
    PEscape {getPatternChar = ch}
        | ch `elem` "ntdwsWSD" -> one
        | ch `elem` "b" -> zero
        | Data.Char.isDigit ch -> gets (IntMap.findWithDefault (error $ "No such capture: " ++ [ch]) (charToDigit ch))
        | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
        | otherwise -> one
    PBound low (Just high) p -> manyTimes p low high
    PBound low _ p -> manyTimes p low (low+maxRepeat)
    PPlus p -> manyTimes p 1 (maxRepeat+1)
    PStar _ p -> manyTimes p 0 maxRepeat
    _ -> error $ show pat
    where
    one = return $ IntSet.singleton 1
    zero = return $ IntSet.singleton 0
    manyTimes p low high = do
        lenP <- possibleLengths p
        return $ IntSet.unions [ IntSet.map (*i) lenP | i <- [low..high] ]

charToDigit ch = Data.Char.ord ch - Data.Char.ord '0'

exactMatch :: (?pats :: [Pattern]) => Len -> Symbolic SBool
exactMatch len = do
    str <- mkFreeVars len
    initialBits <- free "bits"
    let ?str = str
    let initialStatus = Status
            { ok = true
            , pos = toEnum len
            , bits = initialBits
            , captureAt = minBound
            , captureLen = minBound
            }
        runPat s pat = let ?pat = pat in
            ite (ok s &&& pos s .== toEnum len)
                (match s{ pos = 0, captureAt = minBound, captureLen = minBound })
                s{ ok = false, pos = maxBound, bits = maxBound }
    let finalStatus = foldl runPat initialStatus ?pats
    return $
        (bits finalStatus .== 0 &&& pos finalStatus .== toEnum len &&& ok finalStatus)

data Status = Status
    { ok :: SBool
    , pos :: Offset
    , bits :: Flips
    , captureAt :: Captures
    , captureLen :: Captures
    }

type Idx = Word8

instance Mergeable Status where
  symbolicMerge t s1 s2 = Status
    { ok = symbolicMerge t (ok s1) (ok s2)
    , pos = symbolicMerge t (pos s1) (pos s2)
    , bits = symbolicMerge t (bits s1) (bits s2)
    , captureAt = symbolicMerge t (captureAt s1) (captureAt s2)
    , captureLen = symbolicMerge t (captureLen s1) (captureLen s2)
    }

choice :: (?str :: Str, ?pat :: Pattern) => Flips -> [Flips -> Status] -> Status
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
    PCarat{} -> ite (isBegin ||| (charAt (pos-1) .== ord '\n')) s __FAIL__
    PDollar{} -> ite (isEnd ||| (charAt (pos+1) .== ord '\n')) s __FAIL__
    PQuest p -> choice bits [\b -> let ?pat = p in match s{ bits = b }, const s]
    PDot{} -> cond isDot
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
        'd' -> cond (ord '0' .<= cur &&& ord '9' .>= cur)
        'w' -> cond (isWordCharAt pos)
        's' -> cond isWhiteSpace
        'W' -> cond (isDot &&& bnot (isWordCharAt pos))
        'S' -> cond (isDot &&& bnot isWhiteSpace)
        'b' -> ite isWordBoundary s __FAIL__
        _ | Data.Char.isDigit ch -> 
            let from = readCapture captureAt num
                len = readCapture captureLen num
                num = charToDigit ch
             in ite (matchCapture (from :: SWord8) len 0) s{ pos = pos+len } __FAIL__
          | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
          | otherwise  -> cond (ord ch .== cur)
    PBound low (Just high) p -> let s'@Status{ ok = ok' } = (let ?pat = PConcat (replicate low p) in match s) in
        ite ok' (let ?pat = p in manyTimes s' $ high - low) s'
    PBound low _ p -> let ?pat = (PBound low (Just $ low+maxRepeat) p) in match s
    PPlus p ->
        let s'@Status{ ok = ok, pos = pos'} = next p
            res = let ?pat = PStar True p in match s'
         in ite ok res s'
    PStar _ p -> next $ PBound 0 Nothing p
    _ -> error $ show ?pat
    where
    next p = let ?pat = p in match s
    isDot = (cur .>= ord ' ' &&& cur .<= ord '~')
    isOutOfBounds = pos .> toEnum (length ?str)
    isFailedMatch = bnot ok
    manyTimes s n
        | n <= 0 = s
        | otherwise = let s'@Status{ ok = ok' } = match s in
            ite ok' (choice bits [\b -> s{ bits = b }, \b -> manyTimes s'{ bits = b } (n-1)]) s
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
    isEnd = (pos .== toEnum (length ?str))
    isBegin = (pos .== 0)
    isWhiteSpace = cur .== 32 ||| (9 .<= cur &&& 13 .>= cur &&& 11 ./= cur)
    isWordCharAt at = let char = charAt at in
        (char .>= ord 'A' &&& char .<= ord 'Z')
            |||
        (char .>= ord 'a' &&& char .<= ord 'z')
            |||
        (char .== ord '_')
    isWordBoundary = case length ?str of
        0 -> false
        _ -> (isEnd &&& isWordCharAt (pos-1)) |||
             (isBegin &&& isWordCharAt pos) |||
             (isWordCharAt (pos-1) <+> isWordCharAt pos)

main = do
    hSetBuffering stdout NoBuffering
    args <- getArgs
    case args of
        [] -> do
            prog <- getProgName
            if prog == "<interactive>" then run defaultRegex else do
                fail $ "Usage: " ++ prog ++ " regex [regex...]"
        rx -> runMany rx

runMany regexes = do
    let ?pats = map parse regexes
    let lens = IntSet.toAscList $ foldl1 IntSet.intersection (map lenOf ?pats)
    tryWith lens 0
    where
    lenOf p = fst $ runState (possibleLengths p) mempty

run :: String -> IO ()
run regex = runMany [regex]

tryWith :: (?pats :: [Pattern]) => [Int] -> Int -> IO ()
tryWith [] acc = return ()
tryWith (len:lens) acc = if len > maxLength then return () else do
    AllSatResult allRes <- allSat $ exactMatch len
    showResult allRes acc
    where
    showResult [] a = tryWith lens a
    showResult (r:rs) a = do
        disp' $ getModel r
        if (a+1 >= maxHits) then return () else showResult rs (a+1)

disp' :: ([Word8], Word64) -> IO ()
disp' (str, choices) = do
    print $ map chr str
    {-
    putStr (show choices)
    putStr "\t["
    putStr $ map chr str
    putStr "]\n"
    -}
    where
    chr :: Word8 -> Char
    chr = Data.Char.chr . fromEnum

disp :: [Word8] -> IO ()
disp str = do
    putStrLn $ map chr str
    where
    chr :: Word8 -> Char
    chr = Data.Char.chr . fromEnum
