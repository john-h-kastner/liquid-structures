{-# LANGUAGE OverloadedStrings #-}
import Hakyll
import Text.Pandoc

main :: IO ()
main = hakyll $ do
  create ["slides/slides.lhs"] $ do
    route $ setExtension "html"
    compile $ pandocCompilerWith (def {readerExtensions = enableExtension Ext_literate_haskell pandocExtensions}) defaultHakyllWriterOptions
