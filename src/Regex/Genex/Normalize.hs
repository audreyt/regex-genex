{-# LANGUAGE ImplicitParams, NamedFieldPuns #-}
module Regex.Genex.Normalize (normalize) where
import Data.Set (toList, Set)
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex (parseRegex)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set

type BackReferences = IntSet

-- | Normalize a regex into "strong star normal form", as defined in the paper
--   "Simplifying Regular Expressions: A Quantitative Perspective".
normalize :: BackReferences -> Pattern -> Pattern
normalize refs p = black $ let ?refs = refs in simplify p

nullable pat = case pat of
    PGroup _ p -> nullable p
    PQuest{} -> True
    POr ps -> any nullable ps
    PConcat ps -> all nullable ps
    PBound 0 _ _ -> True
    PBound _ _ _ -> False
    PStar{} -> True
    PEmpty -> True
    _ -> False

white pat = case pat of
    PQuest p -> white p
    PStar _ p -> white p
    PGroup x p -> PGroup x $ white p
    POr ps -> POr (map white ps)
    PConcat ps -> if nullable pat
        then POr (map white ps)
        else pat
    PPlus p -> if nullable pat
        then PConcat [p, white p]
        else pat
    _ -> pat

black pat = case pat of
    POr ps -> POr (map black ps)
    PConcat ps -> PConcat (map black ps)
    PGroup x p -> PGroup x $ black p
    PStar x p -> PStar x $ white (black p)
    PPlus p -> PConcat [p, PStar (nullable p) (white $ black p)]
    PBound 0 Nothing p -> PStar (nullable p) (white $ black p)
    PBound x Nothing p -> PConcat [PBound x (Just x) p, PStar (nullable p) (white $ black p)]
    PBound x y p -> PBound x y $ black p
    PQuest p -> if nullable p
        then black p
        else PQuest $ black p
    _ -> pat

parse :: String -> Pattern
parse r = case parseRegex r of
    Right (pattern, _) -> pattern
    Left x -> error $ show x

foldChars :: (Set Char, [Pattern]) -> Pattern -> (Set Char, [Pattern])
foldChars (cset, rest) pat = case pat of
    PChar { getPatternChar = ch } -> (Set.insert ch cset, rest)
    PAny {getPatternSet = PatternSet (Just cset') _ _ _} -> (Set.union cset cset', rest)
    _ -> (cset, pat:rest)

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
    POr ps -> let ps' = map simplify ps in 
        case foldl foldChars (Set.empty, []) ps' of
            (cset, rest)
                | null rest     -> anySet
                | Set.null cset -> POr rest
                | [r] <- rest   -> POr [anySet, r]
                | otherwise     -> POr [anySet, POr rest]
                where
                anySet = case Set.size cset of
                    1 -> PChar { getPatternChar = Set.findMin cset, getDoPa = toEnum 0 }
                    _ -> PAny { getPatternSet = PatternSet (Just cset) Nothing Nothing Nothing, getDoPa = toEnum 0 }
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

