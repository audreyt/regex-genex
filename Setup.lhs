#!/usr/bin/env runghc
> import Distribution.Simple
> import System.Cmd (rawSystem)
> 
> main :: IO ()
> main = defaultMainWithHooks simpleUserHooks
