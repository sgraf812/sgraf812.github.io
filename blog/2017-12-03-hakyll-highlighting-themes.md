---
title: Hakyll Code Highlighting Themes
tags: hakyll highlighting
---

As [`Hakyll`s FAQ](https://jaspervdj.be/hakyll/tutorials/faq.html#does-hakyll-support-syntax-highlighting) points out, in order to have source code highlighting for your blog, you need appropriate CSS markup.
It would be convenient if one could choose from the wealth of themes out there, but the existing pygments styles don’t seem to work any longer.

<!--more-->

That’s probably because [`pandoc`](https://hackage.haskell.org/package/pandoc) has since deprecated [`highlighting-kate`](https://hackage.haskell.org/package/highlighting-kate) in favor of [`skylighting`](https://hackage.haskell.org/package/skylighting), which adopts a different CSS naming convention, thus invalidating all prior CSS themes.

`skylighting` has a console app for highlighting code, but it doesn’t seem to be able to just dump CSS files for its rich style database.
Fortunately, we can just pick from one of the [pre-defined styles](https://hackage.haskell.org/package/skylighting-0.4.4.1/docs/Skylighting-Styles.html) and generate the CSS with a GHCi two-liner:

```css
$ stack --resolver=nightly-2017-12-01 --install-ghc install skylighting
...
$ stack --resolver=nightly-2017-12-01 ghci
...
Prelude> import Skylighting
Prelude Skylighting> writeFile "zenburn.css" $ styleToCss zenburn
Prelude Skylighting> ^D
$ cat zenburn.css
div.sourceLine, a.sourceLine { display: inline-block; min-height: 1.25em; }
a.sourceLine { pointer-events: none; color: inherit; text-decoration: inherit; }
.sourceCode { overflow: visible; }
code.sourceCode { white-space: pre; }
@media print {
code.sourceCode { white-space: pre-wrap; }
div.sourceLine, a.sourceLine { text-indent: -1em; padding-left: 1em; }
}
pre.numberSource div.sourceLine, .numberSource a.sourceLine
  { position: relative; }
...
```

With a little more effort, you could probably access `skylighting`s whole style database, but I’m currently satisfied with the style I installed.