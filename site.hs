{-# LANGUAGE OverloadedStrings #-}

import           Data.Monoid     (mappend, (<>))
import qualified GHC.IO.Encoding as E
import           Hakyll          hiding (defaultContext)
import qualified Hakyll
import qualified Hakyll.Core.Compiler as Hakyll
import           Text.Pandoc
import           Text.Pandoc.Filter
import           System.Process
import           Control.Monad.IO.Class

data SubRoute
    = Blog
    | About
    deriving (Eq, Ord, Show)

activeLink :: SubRoute -> String
activeLink Blog  = "blog-active"
activeLink About = "about-active"

defaultContext :: SubRoute -> Context String
defaultContext route = mconcat
    [ constField "email" "sgraf1337@gmail.com"
    , constField (activeLink route) "true"
    , Hakyll.defaultContext
    ]

postCtx :: SubRoute -> Context String
postCtx route = mconcat
    [ dateField "date" "%B %e, %Y"
    , mapContext stripTags (teaserField "excerpt" "content")
    , defaultContext route
    ]

myFeedConfiguration :: FeedConfiguration
myFeedConfiguration = FeedConfiguration
    { feedTitle       = "fixpt"
    , feedDescription = "Blog about Haskell, programming lanugage semantics, theory and implementation"
    , feedAuthorName  = "Sebastian Graf"
    , feedAuthorEmail = "sgraf1337@gmail.com"
    , feedRoot        = "https://sgraf812.github.io/"
    }

myPandocCompiler = pandocCompilerWith defaultHakyllReaderOptions defaultHakyllWriterOptions
  { writerHTMLMathMethod = KaTeX defaultKaTeXURL }

main :: IO ()
main = do
    E.setLocaleEncoding E.utf8
    hakyll $ do
        match "CNAME" $ do
            route idRoute
            compile copyFileCompiler

        match "images/*" $ do
            route   idRoute
            compile copyFileCompiler

        match "assets/css/*" $ do
            route   idRoute
            compile compressCssCompiler

        match "assets/fonts/*" $ do
            route   idRoute
            compile copyFileCompiler

        match "assets/icon/*" $ do
            route   idRoute
            compile copyFileCompiler

        match "about.md" $ do
            route   $ setExtension "html"
            compile $ myPandocCompiler
                >>= loadAndApplyTemplate "templates/default.html" (defaultContext About)
                >>= relativizeUrls

        match "blog/*.md" $ do
            route $ setExtension "html"
            compile $ myPandocCompiler
                >>= saveSnapshot "content" -- we need metadata for building up the nav
                >>= loadAndApplyTemplate "templates/post.html"    (postCtx Blog)
                >>= loadAndApplyTemplate "templates/default.html" (postCtx Blog)
                >>= relativizeUrls

        match "index.html" $ do
            route idRoute
            compile $ do
                posts <- recentFirst =<< loadAllSnapshots "blog/*.md" "content"
                let indexCtx =
                        listField "posts" (postCtx Blog) (return posts) `mappend`
                        constField "title" "Home"                       `mappend`
                        defaultContext Blog

                getResourceBody
                    >>= applyAsTemplate indexCtx
                    >>= loadAndApplyTemplate "templates/default.html" indexCtx
                    >>= relativizeUrls

        match "templates/*" $ compile templateCompiler

        create ["atom.xml"] $ do
            route idRoute
            compile $ do
                let feedCtx = postCtx Blog `mappend` bodyField "description"
                posts <- fmap (take 10) . recentFirst =<<
                    loadAllSnapshots "blog/*.md" "content"
                renderAtom myFeedConfiguration feedCtx posts
