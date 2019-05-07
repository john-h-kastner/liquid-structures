{- copied from github.com/nikivazou/theorem-proving-template/blob/d101b1b6960c478862ef628d603ea183be976e5e/safe-lists/tests/Test.hs -}
{-# LANGUAGE BangPatterns #-}

module Main where

import System.Exit
import System.Process

main :: IO ExitCode
main = runAllLiquid >>= exitWith


runAllLiquid :: IO ExitCode
runAllLiquid = mconcat <$> mapM runLiquid orderedSrcFiles  


orderedSrcFiles :: [String]
orderedSrcFiles = [
    "Queue/Queue.hs"
  , "Queue/BankersQueue.hs"
  , "Queue/PhysicistsQueue.hs"
  , "Heap/Heap.hs"
  , "Heap/SortedListHeap.hs"
  , "Heap/LeftistHeap.hs"
  , "Set/Set.hs"
  , "RandomAccessList/RandomAccessList.hs"
  , "RandomAccessList/SimpleRandomAccessList.hs"
  ]

runLiquid :: String -> IO ExitCode
runLiquid fname 
  = runCommand' ("cd " ++ sourceDir ++ "; stack exec -- liquid " ++ fname )

sourceDir :: String
sourceDir = "src"

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand str
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     return ec

instance Semigroup ExitCode where
  (<>) (ExitFailure i) _ = ExitFailure i 
  (<>) ExitSuccess e     = e 

instance Monoid ExitCode where
  mempty = ExitSuccess

