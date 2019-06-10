{-# LANGUAGE OverloadedStrings #-}
import Hakyll
import Text.Pandoc
--import System.Process

main :: IO ()
main = hakyll $ do
    match "_liquid-markdown/*" $ do
      route $ setExtension "html"
      compile $ myPandocCompiler
        >>= loadAndApplyTemplate "templates/default.html" defaultContext

    match "css/*" $ do
      route   idRoute
      compile compressCssCompiler

    match "templates/*" $ compile templateCompiler

myPandocCompiler = pandocCompilerWith
      (def {readerExtensions = enableExtension Ext_literate_haskell pandocExtensions})
      def
