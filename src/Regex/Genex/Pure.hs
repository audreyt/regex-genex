module Regex.Genex.Pure (genexPure) where
import qualified Data.Text as T
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.List (intersect, (\\))
import Control.Monad
import Control.Monad.Omega
import Regex.Genex.Normalize (normalize)
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex (parseRegex)

parse :: String -> Pattern
parse r = case parseRegex r of
    Right (pattern, _) -> pattern
    Left x -> error $ show x

genexPure :: [String] -> [String]
genexPure = map T.unpack . foldl1 intersect . map (runOmega . omega . normalize IntSet.empty . parse)

maxRepeat :: Int
maxRepeat = 3

omega :: Pattern -> Omega T.Text
omega p = case p of
    PChar{..} -> isChar getPatternChar
    PAny {getPatternSet = PatternSet (Just cset) _ _ _} -> each $ map T.singleton $ Set.toList cset
    PQuest p -> join $ each [return T.empty, omega p]
    PPlus p -> omega $ PBound 1 Nothing p
    PStar _ p -> omega $ PBound 0 Nothing p
    PBound low high p -> do
        p <- omega p
        n <- each [low..maybe (low+3) id high]
        return $ T.replicate n p
    PConcat ps -> fmap T.concat . sequence $ map omega ps
    POr xs -> foldl1 mplus $ map omega xs
    PDot{} -> notChars []
    PEscape {..} -> case getPatternChar of
        'n' -> isChar '\n'
        't' -> isChar '\t'
        'r' -> isChar '\r'
        'f' -> isChar '\f'
        'a' -> isChar '\a'
        'e' -> isChar '\ESC'
        'd' -> chars $ ['0'..'9']
        'w' -> chars $ ['0'..'9'] ++ '_' : ['a'..'z'] ++ ['A'..'Z']
        's' -> chars "\9\10\12\13\32"
        'W' -> notChars $ ['0'..'9']
        'S' -> notChars $ ['0'..'9'] ++ '_' : ['a'..'z'] ++ ['A'..'Z']
        'D' -> notChars "\9\10\12\13\32"
        ch  -> isChar ch
    _      -> error $ show p
    where
    isChar :: Char -> Omega T.Text
    isChar = return . T.singleton
    chars = each . map T.singleton
    notChars = chars . ([' '..'~'] \\)
