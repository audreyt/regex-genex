module Main where
import Regex.Genex
import System.IO
import System.Environment
import Data.Char (isDigit)

defaultRegex :: String
defaultRegex = "a(b|c)d{2,3}e*"

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    args <- getArgs
    case args of
        [] -> do
            prog <- getProgName
            if prog == "<interactive>" then run defaultRegex else do
                fail $ "Usage: " ++ prog ++ " regex [regex...]"
        rx | all isPure rx -> mapM_ ((putStr "0 " >>) . print) (genexPure rx)
           | otherwise     -> genexPrint rx
    where
    isPure [] = True
    isPure ('\\':'\\':cs) = isPure cs
    isPure ('\\':'b':_) = False
    isPure ('\\':c:cs)
        | isDigit c = False
        | otherwise = isPure cs
    isPure ('^':_) = False
    isPure ('$':_) = False
    isPure (_:cs) = isPure cs

run :: String -> IO ()
run regex = genexPrint [regex]
