{-# LANGUAGE ImplicitParams, NamedFieldPuns, ParallelListComp, PatternGuards #-}
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
type SChar = SWord8
type Str = [SChar]
type Offset = SWord8
type Flips = SWord64
type Captures = SWord64

maxHits = 65535
minLength = 0
maxLength = 255
maxRepeat = 3 -- 7 and 15 are also good

lengths p = IntSet.toList . fst $ runState (possibleLengths $ parse p) mempty
minLen p = IntSet.findMin . fst $ runState (possibleLengths p) mempty

defaultRegex = "a(b|c)d{2,3}e*"
parse r = case parseRegex r of
    Right (pattern, _) -> pattern
    Left x -> error $ show x

type GroupLens = IntMap IntSet
type BackReferences = IntSet

simplify :: (?refs :: BackReferences) => Pattern -> Pattern
simplify pat = case pat of
    PGroup (Just idx) p -> if idx `IntSet.member` ?refs then PGroup (Just idx) (simplify p) else simplify p
    PGroup _ p -> simplify p
    PQuest p -> case simplify p of
        PEmpty -> PEmpty
        p'     -> PQuest p'
    POr [] -> PEmpty
    POr [p] -> simplify p
    POr ps -> POr (map simplify ps)
    PConcat [] -> PEmpty
    PConcat [p] -> simplify p
    PConcat ps -> case concatMap (fromConcat . simplify) ps of
        [] -> PEmpty
        ps' -> PConcat ps'
        where
        fromConcat (PConcat ps) = ps
        fromConcat PEmpty       = []
        fromConcat p            = [p]
    PBound low (Just high) p
        | high == low -> simplify $ PConcat (replicate low (simplify p))
    PBound low high p -> PBound low high (simplify p)
    PPlus p -> PPlus (simplify p)
    PStar x p -> PStar x (simplify p)
    _ -> pat

possibleLengths :: Pattern -> State (GroupLens, BackReferences) IntSet
possibleLengths pat = case pat of
    _ | isOne pat -> one
    PGroup (Just idx) p -> do
        lenP <- possibleLengths p
        modify $ \(g, b) -> (IntMap.insert idx lenP g, b)
        return lenP
    PGroup _ p -> possibleLengths p
    PCarat{} -> zero
    PDollar{} -> zero
    PQuest p -> fmap (`mappend` IntSet.singleton 0) $ possibleLengths p
    POr ps -> fmap mconcat $ mapM possibleLengths ps
    PConcat [] -> zero
    PConcat ps -> fmap (foldl1 sumSets) (mapM possibleLengths ps)
    PEscape {getPatternChar = ch}
        | ch `elem` "ntrfaedwsWSD" -> one
        | ch `elem` "b" -> zero
        | Data.Char.isDigit ch -> do
            let num = charToDigit ch
            modify $ \(g, b) -> (g, IntSet.insert num b)
            gets $ (IntMap.findWithDefault (IntSet.singleton 0) num) . fst
        | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
        | otherwise -> one
    PBound low (Just high) p -> manyTimes p low high
    PBound low _ p -> manyTimes p low (low+maxRepeat)
    PPlus p -> manyTimes p 1 (maxRepeat+1)
    PStar _ p -> manyTimes p 0 maxRepeat
    PEmpty -> zero
    _ -> error $ show pat
    where
    one = return $ IntSet.singleton 1
    zero = return $ IntSet.singleton 0
    sumSets s1 s2 = IntSet.unions [ IntSet.map (+elm) s2 | elm <- IntSet.elems s1 ]
    manyTimes p low high = do
        lenP <- possibleLengths p
        return $ IntSet.unions [ foldl sumSets (IntSet.singleton 0) (replicate i lenP) | i <- [low..high] ]

charToDigit ch = Data.Char.ord ch - Data.Char.ord '0'

exactMatch :: (?pats :: [Pattern]) => Len -> Symbolic SBool
exactMatch len = do
    str <- mkFreeVars len
    initialFlips <- free "flips"
    let ?str = str
    let initialStatus = Status
            { ok = true
            , pos = toEnum len
            , flips = initialFlips
            , captureAt = minBound
            , captureLen = minBound
            }
        runPat s pat = let ?pat = pat in
            ite (ok s &&& pos s .== toEnum len)
                (match s{ pos = 0, captureAt = minBound, captureLen = minBound })
                s{ ok = false, pos = maxBound, flips = maxBound }
    let finalStatus@Status{ ok, pos, flips } = foldl runPat initialStatus ?pats
    return (flips .== 0 &&& pos .== toEnum len &&& ok)

data Status = Status
    { ok :: SBool
    , pos :: Offset
    , flips :: Flips
    , captureAt :: Captures
    , captureLen :: Captures
    }

instance Mergeable Status where
  symbolicMerge t s1 s2 = Status
    { ok = symbolicMerge t (ok s1) (ok s2)
    , pos = symbolicMerge t (pos s1) (pos s2)
    , flips = symbolicMerge t (flips s1) (flips s2)
    , captureAt = symbolicMerge t (captureAt s1) (captureAt s2)
    , captureLen = symbolicMerge t (captureLen s1) (captureLen s2)
    }

choice :: (?str :: Str, ?pat :: Pattern) => Flips -> [Flips -> Status] -> Status
choice _ [] = error "X"
choice flips [a] = a flips
choice flips [a, b] = ite (lsb flips) (b flips') (a flips')
    where
    flips' = flips `shiftR` 1
    {-
choice flips (x:xs) = ite (lsb flips) (choice flips' xs) (x flips')
    where
    flips' = flips `shiftR` 1
    -}
choice flips xs = select (map ($ flips') xs) __FAIL__ thisFlip
    where
    __FAIL__ = Status{ ok = false, pos = maxBound, flips = maxBound, captureAt = minBound, captureLen = minBound }
    bits = log2 $ length xs
    half = length xs `div` 2
    flips' = flips `shiftR` bits
    thisFlip = (flips `shiftL` (64 - bits)) `shiftR` (64 - bits)

log2 1 = 0
log2 n = 1 + log2 ((n + 1) `div` 2)

writeCapture :: Captures -> Int -> Offset -> Captures
writeCapture cap idx val = foldl writeBit cap ([0..7] `zip` blastLE val)
    where
    writeBit c (i, bit) = setBitTo c (idx * 8 + i) bit

readCapture cap idx = fromBitsLE [ bitValue cap (idx * 8 + i) | i <- [ 0..7 ] ]
    
isOne PChar{} = True
isOne PDot{} = True
isOne PAny {} = True
isOne PAnyNot {} = True
isOne (PGroup Nothing p) = isOne p
isOne PEscape {getPatternChar = ch}
    | ch `elem` "ntrfaedwsWSD" = True
    | ch `elem` "b" = False
    | Data.Char.isDigit ch = False
    | Data.Char.isAlpha ch = error $ "Unsupported escape: " ++ [ch]
    | otherwise = True
isOne _ = False

matchOne :: (?pat :: Pattern) => SChar -> SBool
matchOne cur = case ?pat of
    PChar {getPatternChar = ch} -> isChar ch
    PDot{} -> isDot
    PGroup Nothing p -> let ?pat = p in matchOne cur
    PAny {getPatternSet = pset} -> case pset of
        PatternSet (Just cset) _ _ _ -> oneOf $ toList cset
        _ -> error "TODO"
    PAnyNot {getPatternSet = pset} -> case pset of
        PatternSet (Just cset) _ _ _ -> noneOf $ toList cset
        _ -> error "TODO"
    PEscape {getPatternChar = ch} -> case ch of
        'n' -> isChar '\n'
        't' -> isChar '\t'
        'r' -> isChar '\r'
        'f' -> isChar '\f'
        'a' -> isChar '\a'
        'e' -> isChar '\ESC'
        'd' -> isDigit
        'w' -> isWordChar
        's' -> isWhiteSpace
        'W' -> (isDot &&& bnot isWordChar)
        'S' -> (isDot &&& bnot isWhiteSpace)
        'D' -> (isDot &&& bnot isDigit)
        _   -> isChar ch
    _ -> false
    where
    ord = toEnum . Data.Char.ord
    isChar ch = cur .== ord ch
    isDot = (cur .>= ord ' ' &&& cur .<= ord '~')
    oneOf cs = bOr [ ord ch .== cur | ch <- cs ]
    noneOf cs = bAnd ((cur .>= ord ' ') : (cur .<= ord '~') : [ ord ch ./= cur | ch <- cs ])
    isDigit = (ord '0' .<= cur &&& ord '9' .>= cur)
    isWordChar = (cur .>= ord 'A' &&& cur .<= ord 'Z')
             ||| (cur .>= ord 'a' &&& cur .<= ord 'z')
             ||| (cur .== ord '_')
    isWhiteSpace = cur .== 32 ||| (9 .<= cur &&& 13 .>= cur &&& 11 ./= cur)


match :: (?str :: Str, ?pat :: Pattern) => Status -> Status
match s@Status{ ok, pos, flips, captureAt, captureLen }
  | isOne ?pat = ite (pos .>= strLen) __FAIL__ one
  | otherwise = ite (pos + (toEnum $ minLen ?pat) .> strLen) __FAIL__ $ case ?pat of
    PGroup (Just idx) p -> let s'@Status{ pos = pos' } = next p in s'
        { captureAt = writeCapture captureAt idx pos
        , captureLen = writeCapture captureLen idx (pos' - pos)
        }
    PGroup _ p -> next p
    PCarat{} -> ite (isBegin ||| (charAt (pos-1) .== ord '\n')) s __FAIL__
    PDollar{} -> ite (isEnd ||| (charAt (pos+1) .== ord '\n')) s __FAIL__
    PQuest p -> choice flips [\b -> let ?pat = p in match s{ flips = b }, \b -> s{ flips = b }]
    POr [p] -> next p
    POr ps -> choice flips $ map (\p -> \b -> let ?pat = p in match s{ flips = b }) ps
    PConcat [] -> s
    PConcat [p] -> next p
    PConcat ps
        | all isOne ps -> ite (
            ((pos + toEnum (length ps)) .<= strLen)
                &&&
            (bAnd [ let ?pat = p in matchOne (charAt (pos+i))
                  | p <- ps
                  | i <- [0..]
                  ])
        ) s{ pos = pos + toEnum (length ps) } __FAIL__
        | (ones@(_:_:_), rest) <- span isOne ps -> step [PConcat ones, PConcat rest] s
        | (nones@(_:_), rest@(_:_:_)) <- span (not . isOne) ps -> step (nones ++ [PConcat rest]) s
        | otherwise -> step ps s
        where
        step [] s' = s'
        step (p:ps) s' = 
            let s''@Status{ ok } = (let ?pat = p in match s')
                res = step ps s''
             in ite ok res __FAIL__
    PEscape {getPatternChar = ch} -> case ch of
        'b' -> ite isWordBoundary s __FAIL__
        _ | Data.Char.isDigit ch -> 
            let from = readCapture captureAt num
                len = readCapture captureLen num
                num = charToDigit ch
             in ite (matchCapture (from :: Offset) len 0) s{ pos = pos+len } __FAIL__
          | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
          | otherwise  -> cond (ord ch .== cur)
    PBound low (Just high) p -> let s'@Status{ ok = ok' } = (let ?pat = PConcat (replicate low p) in match s) in
        ite ok' (let ?pat = p in (manyTimes s' $ high - low)) s'
    PBound low _ p -> let ?pat = (PBound low (Just $ low+maxRepeat) p) in match s
    PPlus p ->
        let s'@Status{ ok = ok, pos = pos'} = next p
            res = let ?pat = PStar True p in match s'
         in ite ok res s'
    PStar _ p -> next $ PBound 0 Nothing p
    PEmpty -> s
    _ -> error $ show ?pat
    where
    one = cond $ matchOne cur
    next p = let ?pat = p in match s
    isDot = (cur .>= ord ' ' &&& cur .<= ord '~')
    isOutOfBounds = pos .> strLen
    strLen = toEnum (length ?str)
    isFailedMatch = bnot ok
    manyTimes :: (?pat :: Pattern) => Status -> Int -> Status
    manyTimes s@Status{flips} n
        | n <= 0 = s
        | otherwise = choice flips [\b -> s{ flips = b }, nextTime]
            where
            nextTime b = let s'@Status{ok,pos} = match s{ flips = b } in
                ite (pos .<= strLen &&& ok) (manyTimes s' (n-1)) s'

    cur = charAt pos
    charAt = select ?str 0
    condChar ch = cond (ord ch .== cur)
    cond b = ite b s{ pos = pos+1 } __FAIL__
    oneOf cs = cond $ bOr [ ord ch .== cur | ch <- cs ]
    noneOf cs = cond $ bAnd ((cur .>= ord ' ') : (cur .<= ord '~') : [ ord ch ./= cur | ch <- cs ])
    ord = toEnum . Data.Char.ord
    matchCapture from len off = (len .<= off) |||
        (charAt (pos+off) .== charAt (from+off) &&& matchCapture from len (off+1))
    __FAIL__ = s{ ok = false, pos = maxBound, flips = maxBound }
    isEnd = (pos .== toEnum (length ?str))
    isBegin = (pos .== 0)
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
    let p'lens = [ (p', lens)
                 | p <- [ if r == "" then PEmpty else parse r | r <- regexes ]
                 , let (lens, (_, backRefs)) = runState (possibleLengths p) mempty
                 , let p' = let ?refs = backRefs in simplify p
                 ]
    let ?pats = map fst p'lens
    -- print ?pats
    let lens = IntSet.toAscList $ foldl1 IntSet.intersection (map snd p'lens)
    tryWith (filter (<= maxLength) lens) 0

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
        disp $ getModel r
        if (a+1 >= maxHits) then return () else showResult rs (a+1)

disp :: ([Word8], Word64) -> IO ()
disp (str, choices) = do
    putStr $ show (length str) ++ "."
    let n = show choices
    putStr (replicate (8 - length n) '0')
    putStr n
    putStr "\t\t"
    print $ map chr str
    where
    chr = Data.Char.chr . fromEnum
