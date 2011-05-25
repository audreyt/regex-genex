{-# LANGUAGE ImplicitParams, NamedFieldPuns, ParallelListComp, PatternGuards #-}
module Regex.Genex (Model(..), genex, genexPrint, genexModels) where
import Data.SBV
import Data.Set (toList)
import Data.Monoid
import Control.Monad.State
import qualified Data.Char
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex (parseRegex)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import System.IO.Unsafe (unsafeInterleaveIO)

-- | Given a list of regular repressions, returns all possible strings that matches all of them.
genex :: [String] -> IO [String]
genex = genexWith getString

-- | A match consists of a string (list of codepoints), and a rank representing alternation order.
data Model = Model
    { modelChars :: [Word8]
    , modelRank :: Word64
    }
    deriving (Show, Eq, Ord)

-- | Same as @genex@, but with the entire model returned instead.
genexModels :: [String] -> IO [Model]
genexModels = genexWith (getStringWith id)

-- | Same as @genexModels@, but print the models to standard output instead.
genexPrint :: [String] -> IO ()
genexPrint = genexWith displayString

type Len = Int
type SChar = SWord8
type Str = [SChar]
type Offset = SWord8
type Flips = SWord64
type Captures = SFunArray Word8 Word8

maxHits, maxLength, maxRepeat :: Int
maxHits = 65535
maxLength = 255
maxRepeat = 3 -- 7 and 15 are also good

-- lengths p = let ?grp = mempty in IntSet.toList . fst $ runState (possibleLengths $ parse p) mempty

minLen :: (?grp :: GroupLens) => Pattern -> Int
minLen p = case p of
    PEscape {getPatternChar = ch}
        | Data.Char.isDigit ch -> let num = charToDigit ch in
            IntSet.findMin (IntMap.findWithDefault (IntSet.singleton 0) num ?grp)
    _ -> IntSet.findMin . fst $ runState (possibleLengths p) mempty

parse :: String -> Pattern
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
    PAny {getPatternSet = pset, getDoPa} -> case pset of
        PatternSet (Just cset) _ _ _ -> case toList cset of
            [ch] -> PChar { getPatternChar = ch, getDoPa }
            _    -> pat
        _ -> pat
    POr [] -> PEmpty
    POr [p] -> simplify p
    POr ps -> POr (map simplify ps)
    PConcat [] -> PEmpty
    PConcat [p] -> simplify p
    PConcat ps -> case concatMap (fromConcat . simplify) ps of
        [] -> PEmpty
        ps' -> PConcat ps'
        where
        fromConcat (PConcat ps') = ps'
        fromConcat PEmpty        = []
        fromConcat p             = [p]
    PBound low (Just high) p
        | high == low -> simplify $ PConcat (replicate low (simplify p))
    PBound low high p -> PBound low high (simplify p)
    PPlus p -> PPlus (simplify p)
    PStar x p -> PStar x (simplify p)
    _ -> pat

possibleLengths :: (?grp :: GroupLens) => Pattern -> State (GroupLens, BackReferences) IntSet
possibleLengths pat = case pat of
    _ | isOne pat -> one
    PGroup (Just idx) p -> do
        lenP <- possibleLengths p
        modify $ \(g, b) -> (IntMap.insert idx lenP g, b)
        return lenP
    PGroup _ p -> possibleLengths p
    PCarat{} -> zero
    PDollar{} -> zero
    PQuest p -> maybeGroup p (`mappend` zeroSet)
    POr ps -> fmap mconcat $ mapM possibleLengths ps
    PConcat [] -> zero
    PConcat ps -> fmap (foldl1 sumSets) (mapM possibleLengths ps)
    PEscape {getPatternChar = ch}
        | ch `elem` "ntrfaedwsWSD" -> one
        | ch `elem` "b" -> zero
        | Data.Char.isDigit ch -> do
            let num = charToDigit ch
            modify $ \(g, b) -> (g, IntSet.insert num b)
            gets $ (IntMap.findWithDefault (IntMap.findWithDefault (error $ "No such capture: " ++ [ch]) num ?grp) num) . fst
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
    zeroSet = IntSet.singleton 0
    sumSets s1 s2 = IntSet.unions [ IntSet.map (+elm) s2 | elm <- IntSet.elems s1 ]
    manyTimes p low high = maybeGroup p $ \lenP -> IntSet.unions
        [ foldl sumSets (IntSet.singleton 0) (replicate i lenP)
        | i <- [low..high]
        ]
    maybeGroup p@(PGroup (Just idx) _) f = do
        lenP <- possibleLengths p
        let lenP' = f lenP
        modify $ \(g, b) -> (IntMap.insert idx lenP' g, b)
        return lenP'
    maybeGroup p f = fmap f (possibleLengths p)

charToDigit :: Char -> Int
charToDigit ch = Data.Char.ord ch - Data.Char.ord '0'

exactMatch :: (?pats :: [(Pattern, GroupLens)]) => Len -> Symbolic SBool
exactMatch len = do
    str <- mkFreeVars len
    initialFlips <- free "flips"
    at' <- newArray_ (Just minBound)
    len' <- newArray_ (Just minBound)
    let ?str = str
    let initialStatus = Status
            { ok = true
            , pos = toEnum len
            , flips = initialFlips
            , captureAt = at'
            , captureLen = writeCapture len' 1 1
            }
        runPat s (pat, groupLens) = let ?pat = pat in let ?grp = groupLens in
            ite (ok s &&& pos s .== toEnum len)
                (match s{ pos = 0, captureAt = at', captureLen = len' })
                s{ ok = false, pos = maxBound, flips = maxBound }
    let Status{ ok, pos, flips } = foldl runPat initialStatus ?pats
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
choice flips xs = select (map ($ flips') xs) (head xs thisFlip){ ok = false } thisFlip
    where
    bits = log2 $ length xs
    flips' = flips `shiftR` bits
    thisFlip = (flips `shiftL` (64 - bits)) `shiftR` (64 - bits)

log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 ((n + 1) `div` 2)

writeCapture :: Captures -> Int -> Offset -> Captures
writeCapture cap idx val = writeArray cap (toEnum idx) val
-- writeCapture cap idx val = (take (idx-1) (cap ++ [0..])) ++ (val : drop idx cap)
{-
writeCapture cap idx val = foldl writeBit cap ([0..7] `zip` blastLE val)
    where
    writeBit c (i, bit) = setBitTo c (idx * 8 + i) bit
-}

readCapture :: Captures -> Int -> SChar
readCapture a = readArray a . toEnum
--readCapture cap idx = fromBitsLE [ bitValue cap (idx * 8 + i) | i <- [ 0..7 ] ]
    
isOne :: Pattern -> Bool
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


match :: (?str :: Str, ?pat :: Pattern, ?grp :: GroupLens) => Status -> Status
match s@Status{ pos, flips, captureAt, captureLen }
  | isOne ?pat = ite (pos .>= strLen) __FAIL__ one
  | otherwise = ite (pos + (toEnum $ minLen ?pat) .> strLen) __FAIL__ $ case ?pat of
    PGroup (Just idx) p -> let s'@Status{ pos = pos', ok = ok' } = next p in 
        ite ok' (s'
            { captureAt = writeCapture captureAt idx pos
            , captureLen = writeCapture captureLen idx (pos' - pos)
            }) __FAIL__
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
        step (p':ps') s' = 
            let s''@Status{ ok } = (let ?pat = p' in match s')
                res = step ps' s''
             in ite ok res __FAIL__
    PEscape {getPatternChar = ch} -> case ch of
        'b' -> ite isWordBoundary s __FAIL__
        _ | Data.Char.isDigit ch -> 
            let from = readCapture captureAt num
                Just defaultLen = IntMap.lookup num ?grp 
                possibleLens = IntSet.toList defaultLen
                len = case possibleLens of
                    []  -> 0
                    [l] -> toEnum l
                    _   -> readCapture captureLen num
                num = charToDigit ch
             in ite (matchCapture (from :: Offset) len 0) s{ pos = pos+len } __FAIL__
          | Data.Char.isAlpha ch -> error $ "Unsupported escape: " ++ [ch]
          | otherwise  -> cond (ord ch .== cur)
    PBound low (Just high) p -> let s'@Status{ ok = ok' } = (let ?pat = PConcat (replicate low p) in match s) in
        ite ok' (let ?pat = p in (manyTimes s' $ high - low)) s'
    PBound low _ p -> let ?pat = (PBound low (Just $ low+maxRepeat) p) in match s
    PPlus p ->
        let s'@Status{ok} = next p
            res = let ?pat = PStar True p in match s'
         in ite ok res s'
    PStar _ p -> next $ PBound 0 Nothing p
    PEmpty -> s
    _ -> error $ show ?pat
    where
    one = cond $ matchOne cur
    next p = let ?pat = p in match s
    strLen = toEnum (length ?str)
    manyTimes :: (?pat :: Pattern) => Status -> Int -> Status
    manyTimes s'@Status{ flips = flips' } n
        | n <= 0 = s'
        | otherwise = choice flips' [\b -> s'{ flips = b }, nextTime]
            where
            nextTime b = let s''@Status{ ok = ok'', pos = pos'' } = match s'{ flips = b } in
                ite (pos'' .<= strLen &&& ok'') (manyTimes s'' (n-1)) s''

    cur = charAt pos
    charAt = select ?str 0
    cond b = ite b s{ pos = pos+1 } __FAIL__
    ord = toEnum . Data.Char.ord
    matchCapture :: Offset -> Offset -> Int -> SBool
    matchCapture from len n
        | n >= (length ?str) = true
        | otherwise = (len .<= off) ||| (charAt (pos+off) .== charAt (from+off) &&& matchCapture from len (n+1))
        where
        off = toEnum n
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


displayString :: [SMTResult] -> Int -> (Int -> IO ()) -> IO ()
displayString [] a next = next a
displayString (r:rs) a next = do
    let (chars, rank) = getModel r
    putStr $ show (length (chars :: [Word8])) ++ "."
    let n = show (rank :: Word64)
    putStr (replicate (8 - length n) '0')
    putStr n
    putStr "\t\t"
    print $ map chr chars
    if (a+1 >= maxHits) then return () else
        displayString rs (a+1) next
    where
    chr = Data.Char.chr . fromEnum

genexWith :: Monoid a => ([SMTResult] -> Int -> (Int -> IO a) -> IO a) -> [[Char]] -> IO a
genexWith f regexes = do
    let ?grp = mempty
    let p'lens = [ ((p', groupLens), lens)
                 | p <- [ if r == "" then PEmpty else parse r | r <- regexes ]
                 , let (lens, (groupLens, backRefs)) = runState (possibleLengths p) mempty
                 , let p' = let ?refs = backRefs in simplify p
                 ]
    let ?pats = map fst p'lens
    let lens = IntSet.toAscList $ foldl1 IntSet.intersection (map snd p'lens)
    tryWith f (filter (<= maxLength) lens) 0

tryWith :: (?pats :: [(Pattern, GroupLens)]) => 
    Monoid a => ResultHandler a -> [Int] -> Int -> IO a
tryWith _ [] _ = return mempty
tryWith f (len:lens) acc = if len > maxLength then return mempty else do
    AllSatResult allRes <- allSat $ exactMatch len
    f allRes acc $ tryWith f lens

type ResultHandler a = [SMTResult] -> Int -> (Int -> IO a) -> IO a

getStringWith :: (Model -> a) -> [SMTResult] -> Int -> (Int -> IO [a]) -> IO [a]
getStringWith _ [] a next = next a
getStringWith f (r:rs) a next = do
    let (chars, rank) = getModel r
    rest <- if (a+1 >= maxHits) then return [] else
        unsafeInterleaveIO $ getStringWith f rs (a+1) next
    return (f (Model chars rank):rest)

getString :: [SMTResult] -> Int -> (Int -> IO [String]) -> IO [String]
getString = getStringWith $ \Model{ modelChars } -> map chr modelChars
    where
    chr = Data.Char.chr . fromEnum
