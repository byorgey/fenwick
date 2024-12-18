% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[nolinenum]{jfp}

% \usepackage{showkeys}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\let\Bbbk\undefined  % https://github.com/kosmikus/lhs2tex/issues/82
%include polycode.fmt

%subst pragma a = "\texttt{\string{-\#" a "\#-\string}}"

%format :--:   = "\mathrel{:\!\text{---}\!:}"
%format `inR`  = "\in"
%format inR    = "(" `inR` ")"
%format `subR` = "\subseteq"
%format subR   = "(" `subR` ")"

%format <>     = "\oplus "
%format mempty = "0 "

%format lo1
%format lo2
%format hi1
%format hi2

%format ++ = "+\!+"
%format `interleave` = "\interleaveop"
%format interleave = "(" `interleave` ")"
%format `find` = "\gnab"
%format find = "(" `find` ")"

%format pow (a) (b) = a "^ {" b "}"

%format * = "\cdot"

%format invBit = "\neg"
%format .+. = "\oplus"
%format .&. = "\land"
%format .|. = "\lor"
%format .&&. = "\owedge"
%format :. = "\mathrel{:\!.}"

%format not = "not"

%format ul(x) = "\underline{" x "}"

%format len(x) = "|" x "|"

%if false
\begin{code}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Fenwick where

import Prelude hiding (even, odd)

\end{code}
%endif

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{booktabs}   %% For formal tables: http://ctan.org/pkg/booktabs
\usepackage{todonotes}
\usepackage{enumitem}
\newcommand{\todoi}[2][]{\todo[inline, #1]{#2}}
\usepackage[backend=pgf, input, extension=pgf, outputdir=diagrams]{diagrams-latex}

\usepackage{xspace}
\usepackage{prettyref}
\usepackage{bbm}
\usepackage{stmaryrd}

\usepackage{minted}

\usepackage{thmtools, thm-restate}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{Section~\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{claim}{Claim~\ref{#1}}
\newrefformat{obs}{Observation~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\providecommand{\pref}{}
\renewcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\providecommand{\Pref}{}
\renewcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newtheorem{theorem}{Theorem}
\newtheorem{corollary}[theorem]{Corollary}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% structured proofs
\newenvironment{sproof}{%
    \begin{tabbing}
    \phantom{$\equiv$} \= \qquad\qquad\qquad\qquad\qquad \= \kill
}{
    \end{tabbing}
}
\newcommand{\stmt}[1]{\> \ensuremath{#1} \\}
\newcommand{\lstmt}[1]{\> \ensuremath{#1} }
\newcommand{\reason}[2]{\ensuremath{#1} \>\> \{ \quad #2 \quad \} \\}

\newcommand{\subpart}[1]{\llcorner #1 \lrcorner}
\newcommand{\suppart}[1]{\ulcorner #1 \urcorner}

%%% Other math stuff

\newtheorem{thm}{Theorem}[section]
\newtheorem{prop}[thm]{Proposition}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{claim}[thm]{Claim}

\theoremstyle{definition}
\newtheorem{defn}[thm]{Definition}
\newtheorem{obs}{Observation}
\newtheorem{prob}{Problem}

\theoremstyle{remark}
\newtheorem*{rem}{Remark}
\newtheorem*{ex}{Example}
\newtheorem*{nota}{Notation}

\newcommand{\bits}{\ensuremath{\mathbbm{2}}}

\newcommand{\mempty}{0}

\newcommand{\Up}{\textbf{U}\xspace}
\newcommand{\RQ}{\textbf{RQ}\xspace}

\newcommand{\ie}{\emph{i.e.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\interleaveop}{\curlyvee}

\newcommand{\N}{\mathbb{N}}
\newcommand{\Z}{\mathbb{Z}}

\newcommand{\sem}[1]{\llbracket {#1} \rrbracket}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newif\ifJFP
\JFPfalse

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\journaltitle{Journal of Functional Programming}
\cpr{Cambridge University Press}
\doival{10.1017/xxxxx}

\jnlDoiYr{2024}

\title{You Could Have Invented Fenwick Trees}
\begin{authgrp}
  \author{Brent A. Yorgey}
  \affiliation{Hendrix College \\ 1600 Washington Ave, Conway, AR
    72032, USA \\ \email{yorgey@@hendrix.edu} }
\end{authgrp}

\begin{abstract}
  \emph{Fenwick trees}, also known as \emph{binary indexed trees}, are
  a clever solution to the problem of maintaining a sequence of values
  while allowing both updates and range queries in sublinear time.
  Their implementation is concise and efficient---but also somewhat
  baffling, consisting largely of non-obvious bitwise operations on
  indices.  We begin with \emph{segment trees}, a much more
  straightforward, easy-to-verify, purely functional solution to the
  problem, and use equational reasoning to explain the implementation
  of Fenwick trees as an optimized variant, making use of a Haskell
  EDSL for operations on infinite two's complement binary numbers.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
% \begin{CCSXML}
% <ccs2012>
%    <concept>
%        <concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
%        <concept_desc>Software and its engineering~Functional languages</concept_desc>
%        <concept_significance>500</concept_significance>
%        </concept>
%    <concept>
%        <concept_id>10003752.10003809.10010031</concept_id>
%        <concept_desc>Theory of computation~Data structures design and analysis</concept_desc>
%        <concept_significance>300</concept_significance>
%        </concept>
%  </ccs2012>
% \end{CCSXML}

% \ccsdesc[500]{Software and its engineering~Functional languages}
% \ccsdesc[300]{Theory of computation~Data structures design and analysis}
%% End of generated code


% \begin{keywords}
%   keyword1, keyword2, keyword3
% \end{keywords}

\maketitle[F]

\section{Introduction}
\label{sec:intro}

Suppose we have a sequence of $n$ integers $a_1, a_2, \dots, a_n$, and
want to be able to perform arbitrary interleavings of the following
two operations, illustrated in \pref{fig:update-rq}:

\begin{itemize}
\item \emph{Update} the value at any given index\footnote{Note that we
    use $1$-based indexing here and throughout the paper, that is, the
    first item in the sequence has index $1$.  The reasons for this
    choice will become clear later.} $i$ by adding some value $v$.
\item Find the sum of all values in any given range $[i, j]$, that
  is, $a_i + a_{i+1} + \dots + a_j$.  We call this operation a
  \emph{range query}.
\end{itemize}
Note that update is phrased in terms of \emph{adding} some value $v$
to the existing value; we can also \emph{set} a given index to a new value
$v$ by adding $v - u$, where $u$ is the old value.

If we simply store the integers in a mutable array, then we can update
in constant time, but range queries require time linear in the size
of the range, since we must iterate through the entire range $[i, j]$
to add up the values.

\begin{figure}
\begin{center}
\begin{diagram}[width=150]
import FenwickDiagrams

dia = vsep 0.5
  [ drawArray draw (map (("a_"++) . show) [1 :: Int .. 8])
  , mconcat
    [ arrowV unit_Y
    , text "$\\emph{update}$" # fontSizeL 0.5 # translate (1.2 ^& (-0.5))
    ]
    # translateX (3*leafWidth)
  , drawArray draw2 [1 :: Int .. 8]
  , fromOffsets [-0.2 *^ unitY, (3 * leafWidth + boxWidth) *^ unitX, 0.2 *^ unitY]
    # translateX (boxWidth / 2 + leafSep)
  , mconcat
    [ arrowV unit_Y
    , text "$\\emph{range query}$" # fontSizeL 0.5 # translate (1.8 ^& (-0.5))
    ]
    # translateX (2.5 * leafWidth)
  , text "$a_2 + a_3 + (a_4 + v) + a_5$" # fontSizeL 0.6
    # translateX (2.5 * leafWidth)
  ]
  where
    draw2 4 = text (mathify "a_4 + v") # fontSizeL 0.3
    draw2 n = draw ("a_" ++ show n)
\end{diagram}
\end{center}
\caption{Update and range query operations} \label{fig:update-rq}
\end{figure}

In order to improve the running time of range queries, we could try to
cache (at least some of) the range sums.  However, this must be done
with care, since the cached sums must be kept up to date when updating
the value at an index.  For example, a straightforward approach would
be to use an array $P$ where $P_i$ stores the prefix sum
$a_1 + \dots + a_i$; $P$ can be precomputed in linear time via a scan.
Now range queries are fast: we can obtain $a_i + \dots + a_j$ in
constant time by computing $P_j - P_{i-1}$ (for convenience we set
$P_0 = 0$ so this works even when $i=1$).  Unfortunately, it is update
that now takes linear time, since changing $a_i$ requires updating
$P_j$ for every $j \geq i$.

Is it possible to design a data structure that allows \emph{both}
operations to run in sublinear time?  (You may wish to pause and think
about it before reading the next paragraph!)  This is not just
academic: the problem was originally considered in the context of
\emph{arithmetic coding} \citep{rissanen1979arithmetic,
  bird2002arithmetic}, a family of techniques for turning messages
into sequences of bits for storage or transmission.  In order to
minimize the bits required, one generally wants to assign shorter bit
sequences to more frequent characters, and vice versa; this leads to
the need to maintain a dynamic table of character frequencies.  We
\emph{update} the table every time a new character is processed, and
\emph{query} the table for cumulative frequencies in order to
subdivide a unit interval into consecutive segments proportional to
the frequency of each character \citep{fenwick1994new, ryabko1989fast}.

So, can we get both operations to run in sublinear time?  The answer,
of course, is yes.  One simple technique is to divide the sequence
into $\sqrt n$ buckets, each of size $\sqrt n$, and create an
additional array of size $\sqrt n$ to cache the sum of each bucket.
Updates still run in $O(1)$, since we simply have to update the value
at the given index and the corresponding bucket sum.
Range queries now run in $O(\sqrt n)$ time: to find the sum
$a_i + \dots + a_j$, we manually add the values from $a_i$ to the end
of its bucket, and from $a_j$ to the beginning of its bucket; for all
the buckets in between we can just look up their sum.

We can make range queries even faster, at the cost of making updates
slightly slower, by introducing additional levels of caching.  For
example, we can divide the sequence into $\sqrt[3] n$ ``big buckets'',
and then further subdivide each big bucket into $\sqrt[3] n$ ``small
buckets'', with each small bucket holding $\sqrt[3] n$ values.  The
sum of each bucket is cached; now each update requires modifying three
values, and range queries run in $O(\sqrt[3] n)$ time.

In the limit, we end up with a binary divide-and-conquer approach to
caching range sums, with both update and range query taking $O(\lg n)$
time.  In particular, we can make a balanced binary tree where the
leaves store the sequence itself, and every internal node stores the
sum of its children.  (This will be a familiar idea to many functional
programmers; for example, finger trees
\citep{Hinze-Paterson:FingerTree, apfelmus:fingertree} use a similar sort of caching scheme.)  The
resulting data structure is popularly known as a \emph{segment
  tree}\footnote{There is some confusion of terminology here.  As of
  this writing, the Wikipedia article on \emph{segment trees}
  \citep{wiki:SegmentTree} is about an interval data structure used in
  computational geometry.  However, most of the Google search results
  for ``segment tree'' are from the world of competitive programming,
  where it refers to the data structure considered in this paper (see,
  for example, \citet[\S 2.8]{CP4} or \citet{cp-alg}). The two data structures are largely
  unrelated.}, presumably because each internal node ultimately caches
the sum of a (contiguous) \emph{segment} of the underlying sequence.
\pref{fig:segment-tree} shows a segment tree built on a sample array
of length $n=16$ (for simplicity, we will assume that $n$ is a power
of two, although it is easy to generalize to situations where it is
not). Each leaf of the tree corresponds to an array entry; each
internal node is drawn with a grey bar showing the segment of the
underlying array of which it is the sum.

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree

  dia :: Diagram B
  dia = sampleArray
    # mkSegTree
    # fmap getSum
    # drawSegTree def
\end{diagram}
\end{center}
\caption{A segment tree} \label{fig:segment-tree}
\end{figure}

Let's see how we can use a segment tree to implement the two required
operations so that they run in logarithmic time.

\begin{itemize}
\item To update the value at index $i$, we also need to update any
  cached range sums which include it.  These are exactly the nodes
  along the path from the leaf at index $i$ to the root of the tree;
  there are $O(\lg n)$ such nodes.  \pref{fig:segment-tree-update}
  illustrates this update process for the example segment tree from
  \pref{fig:segment-tree}; updating the entry at index 5 requires
  modifying only the shaded nodes along the path from the root to the
  updated entry.

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***))

  dia :: Diagram B
  dia = sampleArray
    # map ((,) (Any False))
    # mkSegTree
    # update 5 (Any True, Sum 3)
    # fmap (getAny *** getSum)
    # drawSegTree (mkSTOpts showUpdateOpts)
\end{diagram}
\end{center}
\caption{Updating a segment tree} \label{fig:segment-tree-update}
\end{figure}

\item To perform a range query, we descend through the tree while
  keeping track of the range covered by the current node.
  \begin{itemize}
  \item If the range of the current node is wholly contained within
    the query range, return the value of the current
    node.
  \item If the range of the current node is disjoint from the query
    range, return $0$.
  \item Otherwise, recursively query both children and return the sum of the
    results.
  \end{itemize}
\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree (mkSTOpts showRangeOpts)
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
    where
      i = 4
      j = 11
      n = length sampleArray
\end{diagram}
\end{center}
\caption{Performing a range query on a segment tree} \label{fig:segment-tree-range-query}
\end{figure}
\pref{fig:segment-tree-range-query} illustrates the process of
computing the sum of the range $[4 \dots 11]$.  Blue nodes are the
ones we recurse through; green nodes are those whose range is wholly
contained in the query range, and are returned without recursing
further; grey nodes are disjoint from the query range and return zero.
The final result in this example is the sum of values at the green
nodes, $1 + 1 + 5 + -2 = 5$ (it is easily verified that this is in
fact the sum of values in the range $[4 \dots 11]$).

On this small example tree, it may seem that we visit a significant
fraction of the total nodes, but in general, we visit no more than
about $4 \lg n$.  \pref{fig:big-range-query} makes this more
clear.  Only one blue node in the entire tree can have two blue
children, and hence each level of the tree can contain at most two
blue nodes and two non-blue nodes. We essentially perform two binary
searches, one to find each endpoint of the query range.
\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray4
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree (mkSTOpts (showRangeOpts' False False))
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
    where
      i = 12
      j = 42
      n = length sampleArray4
\end{diagram}
\end{center}
\caption{Performing a range query on a larger segment tree} \label{fig:big-range-query}
\end{figure}
\end{itemize}

Segment trees are a very nice solution to the problem: as we will see
in \pref{sec:seg-trees}, they fit well in a functional language;
they also lend themselves to powerful generalizations such as lazily
propagated range updates and persistent update history via shared
immutable structure \citep{cp-alg}.

\term{Fenwick trees}, or \term{binary indexed trees}
\citep{fenwick1994new, cp-alg-fenwick}, are an alternative solution to the problem.
What they lack in generality, they make up for with an extremely small
memory footprint---they require literally nothing more than an array
storing the values in the tree---and a blazing fast implementation.
In other words, they are perfect for applications such as low-level
coding/decoding routines where we don't need any of the advanced
features that segment trees offer, and want to squeeze out every last
bit of performance.

\pref{fig:fenwick-java} shows a typical implementation of Fenwick
trees in Java. As you can see, the implementation is incredibly
concise, and consists mostly of some small loops doing just a few
arithmetic and bit operations per iteration.  It is not at all clear
what this code is doing, or how it works!  Upon closer inspection, the
\mintinline{java}{range}, \mintinline{java}{get}, and
\mintinline{java}{set} functions are straightforward, but the other
functions are a puzzle. We can see that both the
\mintinline{java}{prefix} and \mintinline{java}{update} functions call
another function \mintinline{java}{LSB}, which for some reason
performs a bitwise logical AND of an integer and its negation.  In
fact, \mintinline{java}{LSB(x)} computes the \emph{least significant
  bit} of $x$, that is, it returns the smallest $2^k$ such that the
$k$th bit of $x$ is a one.  However, it is not obvious how the
implementation of \mintinline{java}{LSB} works, nor how and why least
significant bits are being used to compute updates and prefix sums.

\begin{figure}
  \inputminted[fontsize=\footnotesize]{java}{FenwickTree.java}
  \caption{Implementing Fenwick trees with bit tricks}
  \label{fig:fenwick-java}
\end{figure}

Our goal is \emph{not} to write elegant functional code for
this---already solved!---problem.  Rather, our goal will be to use a
functional domain-specific language for bit strings, along with
equational reasoning, to \emph{derive} and \emph{explain} this
baffling imperative code from first principles---a demonstration of
the power of functional thinking and equational reasoning to
understand code written even in other, non-functional languages.
After developing more intuition for segment trees
(\pref{sec:seg-trees}), we will see how Fenwick trees can be viewed as
a variant on segment trees (\pref{sec:fenwick}).  We will then take a
detour into two's complement binary encoding, develop a suitable DSL
for bit manipulations, and explain the implementation of the
\mintinline{java}{LSB} function (\pref{sec:twos-complement}).  Armed
with the DSL, we will then derive functions for converting back and
forth between Fenwick trees and standard binary trees
(\pref{sec:convert}).  Finally, we will be able to derive functions
for moving within a Fenwick tree by converting to binary tree indices,
doing the obvious operations to effect the desired motion within the
binary tree, and then converting back.  Fusing away the conversions
via equational reasoning will finally reveal the hidden LSB function,
as expected (\pref{sec:fenwick-ops}).

This paper was produced from a literate Haskell document; the source
is available from GitHub, at \url{https://github.com/byorgey/fenwick/blob/master/Fenwick.lhs}.

\section{Segment Trees}
\label{sec:seg-trees}

\pref{fig:haskell-segtree} exhibits a simple implementation of a
segment tree in Haskell, using some utilities for working with index
ranges shown in \pref{fig:ranges}.  We store a segment tree as a
recursive algebraic data type, and implement |update| and |rq| using
code that directly corresponds to the recursive descriptions given in
the previous section; |get| and |set| can then also be implemented in
terms of them.  It is not hard to generalize this code to work for
segment trees storing values from either an arbitrary commutative
monoid if we don't need the |set| operation---or from an arbitrary
Abelian group (\ie commutative monoid with inverses) if we do need
|set|---but we keep things simple since the generalization doesn't add
anything to our story.

\begin{figure}
\begin{code}

type Index = Int
data Range = Index :--: Index    -- ($a$ |:--:| $b$) represents the closed interval $[a,b]$
  deriving (Eq, Show)

subR :: Range -> Range -> Bool
(lo1 :--: hi1) `subR` (lo2 :--: hi2) = lo2 <= lo1 && hi1 <= hi2

inR :: Index -> Range -> Bool
k `inR` i = (k :--: k) `subR` i

disjoint :: Range -> Range -> Bool
disjoint (lo1 :--: hi1) (lo2 :--: hi2) = hi1 < lo2 || hi2 < lo1

\end{code}
  \caption{Range utilities}
  \label{fig:ranges}
\end{figure}

\begin{figure}
\begin{spec}

data SegTree where
  Empty   :: SegTree
  Branch  :: Integer -> Range -> SegTree -> SegTree -> SegTree

update :: Index -> Integer -> SegTree -> SegTree
update _ _ Empty = Empty
update i v b@(Branch a rng l r)
  | i `inR` rng  = Branch (a + v) rng (update i v l) (update i v r)
  | otherwise    = b

rq :: Range -> SegTree -> Integer
rq _ Empty = 0
rq q (Branch a rng l r)
  | disjoint rng q  = 0
  | rng `subR` q    = a
  | otherwise       = rq q l + rq q r

get :: Index -> SegTree -> Integer
get i = rq (i :--: i)

set :: Index -> Integer -> SegTree -> SegTree
set i v t = update i (v - get i t) t

\end{spec}
\caption{Simple segment tree implementation in Haskell} \label{fig:haskell-segtree}
\end{figure}

Although this implementation is simple and relatively straightforward
to understand, compared to simply storing the sequence of values in an
array, it incurs a good deal of overhead.  We can be more clever in
our use of space by storing all the nodes of a segment tree in an
array, using the standard left-to-right breadth-first indexing scheme
illustrated in \pref{fig:bt-indexing} (for example, this scheme, or
something like it, is commonly used to implement binary heaps).  The
root has label $1$; every time we descend one level we append an extra
bit: $0$ when we descend to the left child and $1$ when we descend to
the right.  Thus, the index of each node expressed in binary records
the sequence of left-right choices along the path to that node from
the root.  Going from a node to its children is as simple as doing a
left bit-shift and optionally adding 1; going from a node to its
parent is a right bit-shift.  This defines a bijection from the
positive natural numbers to the nodes of an infinite binary tree.  If
we label the segment tree array with $s_1 \dots s_{2n-1}$, then $s_1$
stores the sum of all the $a_i$, $s_2$ stores the sum of the first
half of the $a_i$, $s_3$ stores the sum of the second half, and so on.
$a_1 \dots a_n$ themselves are stored as $s_n \dots s_{2n-1}$.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromJust)

-- bt depth root
bt :: Int -> Int -> BTree Int
bt 0 _ = Empty
bt d r = BNode r (bt (d-1) (2*r)) (bt (d-1) (2*r+1))

dia = bt 4 1
  # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
  # fromJust
  # renderTree dn (~~)

dn i = text ("$" ++ show i ++ "$") <> circle 1 # fc white
  \end{diagram}
  \caption{Indexing a binary tree}
  \label{fig:bt-indexing}
\end{figure}

The important point is that since descending recursively through the
tree corresponds to simple operations on indices, all the algorithms
we have discussed can be straightforwardly transformed into
code that works with a (mutable) array: for example, instead of storing
a reference to the current subtree, we store an integer index; every
time we want to descend to the left or right we simply double the
current index or double and add one; and so on.  Working with tree
nodes stored in an array presents an additional opportunity: rather
than being forced to start at the root and recurse downwards, we can
start at a particular index of interest and move \emph{up} the tree
instead.

So how do we get from segment trees to Fenwick trees?  We start with
an innocuous-seeming observation: \emph{not all the values stored in a
  segment tree are necessary}.  Of course, all the non-leaf nodes are
``unnecessary'' in the sense that they represent cached range sums
which could easily be recomputed from the original sequence.  That's
the whole point: caching these ``redundant'' sums trades off space for
time, allowing us to perform arbitrary updates and range queries
quickly, at the cost of doubling the required storage space.

But that's not what I mean! In fact, there is a different set of
values we can forget about, but in such a way that we still retain the
logarithmic running time for updates and range queries. Which values,
you ask?  Simple: just forget the data stored in \emph{every node
  which is a right child}. \pref{fig:deactivate-right} shows the same
example tree we have been using, but with the data deleted from every
right child.  Note that ``every right child'' includes both leaves and
internal nodes: we forget the data associated to \emph{every} node
which is the right child of its parent.  We will refer to the nodes
with discarded data as \emph{inactive} and the remaining nodes (that
is, left children and the root) as \emph{active}.  We also say that a
tree with all its right children inactivated in this way has been
\emph{thinned}.

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), first, second)

  dia :: Diagram B
  dia = sampleArray
    # mkSegTree
    # deactivate
    # drawSegTree (mkSTOpts (showInactiveOpts False))
\end{diagram}
\end{center}
\caption{Inactivating all right children in a segment tree} \label{fig:deactivate-right}
\end{figure}

Updating a thinned segment tree is easy: just update the same nodes as
before, ignoring any updates to inactive nodes.  But how do we answer
range queries?  It's not too hard to see that there is enough
information remaining to reconstruct the information that was
discarded (you might like to try convincing yourself of this: can you
deduce what values must go in the greyed-out nodes in
\pref{fig:deactivate-right}, without peeking at any previous
figures?).  However, in and of itself, this observation does not give
us a nice algorithm for computing range sums.

It turns out the key is to think about \emph{prefix sums}.  As we saw
in the introduction and the implementation of
\mintinline{java}{range} in \pref{fig:fenwick-java}, if we can compute
the prefix sum $P_k = a_1 + \dots + a_k$ for any $k$, then we can
compute the range sum $a_i + \dots + a_j$ as $P_j - P_{i-1}$.

\begin{theorem}
  Given a thinned segment tree, the sum of \emph{any prefix} of the
  original array (and hence also any range sum) can be computed, in
  logarithmic time, using only the values of active nodes.
\end{theorem}
\begin{proof}
  Surprisingly, in the special case of prefix queries, the original
  range query algorithm described in \pref{sec:intro} and implemented
  in \pref{fig:haskell-segtree} works unchanged!  That is to say, the
  base case in which the range of the current node is wholly contained
  within the query range---and we thus return the value of the current
  node---will only ever happen at active nodes.

  First, the root itself is active, and hence querying the full range
  will work.  Next, consider the case where we are at a node and
  recurse on both children.  The left child is always active, so we
  only need to consider the case where we recurse to the right.  It is
  impossible that the range of the right child will be wholly
  contained in the query range: since the query range is always a
  prefix of the form $[1,j]$, if the right child's range is wholly
  contained in $[1,j]$ then the left child's range must be as
  well---which means that the parent node's range (which is the union
  of its children's ranges) would also be wholly contained in the
  query range.  But in that case we would simply return the parent's
  value without recursing into the right child.  Thus, when we do
  recurse into a right child, we might end up returning $0$, or we
  might recurse further into both grandchildren, but in any case we
  will never try to look at the value of the right child itself.
\end{proof}

\pref{fig:segment-tree-prefix-query} illustrates performing a prefix
query on a segment tree.  Notice that visited right children are only ever
blue or grey; the only green nodes are left children.
\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree (mkSTOpts (showRangeOpts' False False))
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
    where
      i = 1
      j = 11
      n = length sampleArray
\end{diagram}
\end{center}
\caption{Performing a prefix query on a segment tree} \label{fig:segment-tree-prefix-query}
\end{figure}

\section{Fenwick trees}
\label{sec:fenwick}

How should we actually store a thinned segment tree in memory?  If we
stare at \pref{fig:deactivate-right} again, one strategy suggests
itself: simply take every active node and ``slide'' it down and to the
right until it lands in an empty slot in the underlying array, as
illustrated in \pref{fig:sliding-right}.  This sets up a one-to-one
correspondence between active nodes and indices in the range
$1 \dots n$.  Another way to understand this indexing scheme is to use
a postorder traversal of the tree, skipping over inactive nodes and
giving consecutive indices to active nodes encountered during the
traversal.  We can also visualize the result by drawing the tree in a
``right-leaning'' style (\pref{fig:right-leaning}), vertically
aligning each active node with the array slot where it is stored.

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), first, second)

  dia :: Diagram B
  dia = vsep 0.5
    [ sampleArray
      # mkSegTree
      # deactivate
      # drawSegTree opts
    , arrowV (2 *^ unit_Y)
    , sampleArray
    # mkFenwickArray
    # drawArray (draw . getSum)
    # centerX
    ]

  opts = (mkSTOpts (showInactiveOpts False))
    { drawEdge = drawSlidingEdges }
\end{diagram}
\end{center}
\caption{Sliding active values down a thinned segment tree} \label{fig:sliding-right}
\end{figure}

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
import FenwickDiagrams
import SegTree

dia :: Diagram B
dia = sampleArray
  # mkSegTree
  # deactivate
  # drawSegTree stOpts

stOpts = (mkSTOpts nOpts)
  { leanRight = True }

nOpts = (showInactiveOpts False)
  { leanRightN = True }
\end{diagram}
\end{center}
\caption{Right-leaning drawing of a thinned segment tree, vertically
  aligning nodes with their storage
  location} \label{fig:right-leaning}
\end{figure}

This method of storing the active nodes from a thinned segment tree in
an array is precisely a \emph{Fenwick tree}. I will also sometimes
refer to it as a \emph{Fenwick array}, when I want to particularly
emphasize the underlying array data structure.  Although it is
certainly a clever use of space, the big question is how to implement
the update and range query operations.  Our implementations of these
operations for segment trees worked by recursively descending through
the tree, either directly if the tree is stored as a recursive data
structure, or using simple operations on indices if the tree is stored
in an array. However, when storing the active nodes of a thinned tree
in a Fenwick array, it is not \emph{a priori} obvious what operations
on array indices will correspond to moving around the tree.  In order
to attack this problem, we first take a detour through a
domain-specific language for two's complement binary values.

\section{Two's Complement Binary} \label{sec:twos-complement}

The bit tricks usually employed to implement Fenwick trees rely on a
\emph{two's complement} representation of binary numbers, which allow
positive and negative numbers to be represented in a uniform way; for
example, a value consisting of all 1 bits represents $-1$.  We
therefore turn now to developing a domain-specific language, embedded
in Haskell, for manipulating two's complement binary representations.

First, we define a type of bits, with functions for inversion,
logical conjunction, and logical disjunction:

\begin{code}

data Bit = O | I  deriving (Eq, Ord, Show, Enum)

invBit :: Bit -> Bit
invBit = \case {O -> I; I -> O}

(.&.), (.|.) :: Bit -> Bit -> Bit
O  .&. _  = O
I  .&. b  = b

I  .|. _  = I
O  .|. b  = b

\end{code}

Next, we must define bit strings, \ie sequences of bits.  Rather than
fix a specific bit width, it will be much more elegant to work with
\emph{infinite} bit strings.\footnote{Some readers may recognize
  infinite two's complement bit strings as \term{$2$-adic} numbers, that
  is, $p$-adic numbers for the specific case $p = 2$, but nothing in
  our story depends on understanding the connection.} It is tempting
to use standard Haskell lists to represent potentially infinite bit
strings, but this leads to a number of problems. For example, equality
of infinite lists is not decidable, and there is no way in general to
convert from an infinite list of bits back to an |Integer|---how would
we know when to stop?  In fact, these practical problems stem from a
more fundamental one: infinite lists of bits are actually a bad
representation for two's complement bit strings, because of ``junk'',
that is, infinite lists of bits which do not correspond to values in
our intended semantic domain. For example, |cycle [I,O]| is an
infinite list which alternates between |I| and |O| forever, but it
does not represent a valid two's complement encoding of an integer.
Even worse are non-periodic lists, such as the one with |I| at every
prime index and |O| everywhere else.

In fact, the bit strings we want are the \emph{eventually constant}
ones, that is, strings which eventually settle down to an infinite
tail of all zeros (which represent nonnegative integers) or all ones
(which represent negative integers).  Every such string has a finite
representation, so directly encoding eventually constant bit strings
in Haskell not only gets rid of the junk but also leads to elegant,
terminating algorithms for working with them.

\begin{code}

data Bits where
  Rep   :: Bit -> Bits
  Snoc  :: !Bits -> Bit -> Bits

\end{code}

%if false
\begin{code}

instance Eq Bits where
  Rep x == Rep y = x == y
  (xs :. x) == (ys :. y) = x == y && xs == ys

\end{code}
%endif

|Rep b| represents an infinite sequence of bit |b|, whereas |Snoc bs
b| represents the bit string |bs| followed by a final bit |b|. We use
|Snoc|, rather than |Cons|, to match the way we usually write bit
strings, with the least significant bit last.  Note also the use of a
\term{strictness annotation} on the |Bits| field of |Snoc|; this is to
rule out infinite lists of bits using only |Snoc|, such as
|bs = Snoc (Snoc bs O) I|.  In other words, the only way to make a
non-bottom value of type |Bits| is to have a finite sequence of |Snoc|
finally terminated by |Rep|.

Although we have eliminated junk values, one remaining problem is that
there can be multiple distinct representations of the same value.  For
example, |Snoc (Rep O) O| and |Rep O| both represent the infinite bit
string containing all zeros. However, we can solve this with a
carefully constructed \emph{bidirectional pattern synonym} \citep{pickering2016pattern}.

\begin{code}

toSnoc :: Bits -> Bits
toSnoc (Rep a) = Snoc (Rep a) a
toSnoc as = as

pattern (:.) :: Bits -> Bit -> Bits
pattern (:.) bs b <- (toSnoc -> Snoc bs b)
  where
    Rep b :. b' | b == b' = Rep b
    bs :. b = Snoc bs b

{-# COMPLETE (:.) #-}
\end{code}

Matching with the pattern |(bs :. b)| uses a \term{view pattern}
\citep{erwig2001pattern} to potentially expand a |Rep| one step into a
|Snoc|, so that we can pretend |Bits| values are always constructed
with |(:.)|.  Conversely, constructing a |Bits| with |(:.)| will do
nothing if we happen to snoc an identical bit |b| onto an existing
|Rep b|.  This ensures that as long as we stick to using |(:.)| and
never directly use |Snoc|, |Bits| values will always be
\emph{normalized} so that the terminal |Rep b| is immediately followed
by a different bit.  Finally, we mark the pattern |(:.)| as
\verb|COMPLETE| on its own, since matching on |(:.)| is indeed
sufficient to handle every possible input of type |Bits|.  However, in
order to obtain terminating algorithms we will often include one or
more special cases for |Rep|.

Let's begin with some functions for converting |Bits| to and from
|Integer|, and for displaying |Bits| (intended only for testing).

\begin{code}

toBits :: Int -> Bits
toBits n
  | n == 0 = Rep O
  | n == -1 = Rep I
  | otherwise  = toBits (n `div` 2) :. toEnum (n `mod` 2)

fromBits :: Bits -> Int
fromBits (Rep O) = 0
fromBits (Rep I) = -1
fromBits (bs :. b) = 2 * fromBits bs + fromEnum b

instance Show Bits where
  show = reverse . go
   where
    go (Rep b) = replicate 3 (showBit b) ++ "..."
    go (bs :. b) = showBit b : go bs

    showBit = ("01"!!) . fromEnum

\end{code}
%$

Let's try it out, using QuickCheck \citep{claessen2000quickcheck} to
verify our conversion functions:

\begin{verbatim}
ghci> Rep O :. O :. I :. O :. I
...000101
ghci> Rep I :. O :. I
...11101
ghci> toBits 26
...00011010
ghci> toBits (-30)
...11100010
ghci> fromBits (toBits (-30))
-30
ghci> quickCheck $ \x -> fromBits (toBits x) == x
+++ OK, passed 100 tests.
\end{verbatim}

We can now begin implementing some basic operations on |Bits|.  First,
incrementing and decrementing can be implemented recursively as
follows:

\begin{code}

inc :: Bits -> Bits
inc (Rep I)    = Rep O
inc (bs :. O)  = bs :. I
inc (bs :. I)  = inc bs :. O

dec :: Bits -> Bits
dec (Rep O)    = Rep I
dec (bs :. I)  = bs :. O
dec (bs :. O)  = dec bs :. I

\end{code}

The \emph{least significant bit}, or LSB, of a sequence of bits can be
defined as follows:
\begin{code}

lsb :: Bits -> Bits
lsb (Rep O)    = Rep O
lsb (bs :. O)  = lsb bs :. O
lsb (_ :. I)   = Rep O :. I

\end{code}
Note that we add a special case for |Rep O| to ensure that |lsb| is
total. Technically, |Rep O| does not have a least significant bit, so
defining |lsb (Rep O) = Rep O| seems sensible.

\begin{verbatim}
ghci> toBits 26
"...00011010"
ghci> lsb $ toBits 26
"...00010"
ghci> toBits 24
"...00011000"
ghci> lsb $ toBits 24
"...0001000"
\end{verbatim}

Bitwise logical conjunction can be defined straightforwardly.  Note
that we only need two cases; if the finite parts of the inputs have
different lengths, matching with |(:.)| will automatically expand the
shorter one to match the longer one.
\begin{code}

(.&&.) :: Bits -> Bits -> Bits
Rep x .&&. Rep y = Rep (x .&. y)
(xs :. x) .&&. (ys :. y) = (xs .&&. ys) :. (x .&. y)

\end{code}
Bitwise inversion is likewise straightforward.
\begin{code}

inv :: Bits -> Bits
inv (Rep b) = Rep (invBit b)
inv (bs :. b) = inv bs :. invBit b

\end{code}
The above functions follow familiar patterns.  We could easily
generalize to eventually constant streams over an arbitrary element
type, and then implement |(.&&.)| in terms of a generic |zipWith| and |inv|
in terms of |map|.  However, for the present purpose we do not need
the extra generality.

We implement addition with the usual carry-propagation algorithm,
along with some special cases for |Rep|.
\begin{code}

(.+.) :: Bits -> Bits -> Bits
xs         .+. Rep O      = xs
Rep O      .+. ys         = ys
Rep I      .+. Rep I      = Rep I :. O
Snoc xs I  .+. Snoc ys I  = inc (xs .+. ys) :. O
Snoc xs x  .+. Snoc ys y  = (xs .+. ys) :. (x .|. y)

\end{code}
It is not too hard to convince ourselves that this definition of
addition is terminating and yields correct results; but we can also be
fairly confident by just trying it with QuickCheck:

\begin{verbatim}
ghci> quickCheck $ \x y -> fromBits (toBits x .+. toBits y) == x + y
+++ OK, passed 100 tests.
\end{verbatim}

Finally, the following definition of negation is probably familiar to
anyone who has studied two's complement arithmetic; I leave it as an
exercise for the interested reader to prove that |x .+. neg x == Rep
O| for all |x :: Bits|.
\begin{code}

neg :: Bits -> Bits
neg = inc . inv

\end{code}

We now have the tools to resolve the first mystery of the Fenwick tree
implementation.
\begin{thm}
  For all |x :: Bits|, \[ |lsb x = x .&&. neg x|. \]
\end{thm}
\begin{proof}
By induction on |x|.
\begin{itemize}
\item First, if |x = Rep O|, it is an easy calculation to verify that
  |lsb x = x .&&. neg x = Rep O|.
\item Likewise, if |x = Rep I|, both |lsb x| and |x .&&. neg x| reduce
  to |Rep O :. I|.
\item If |x = xs :. O|, then |lsb x = lsb (xs :. O) = lsb xs
  :. O|
  by definition, whereas
  \begin{sproof}
    \stmt{|(xs :. O) .&&. neg (xs :. O)|}
    \reason{=}{Definition of |neg|}
    \stmt{|(xs :. O) .&&. inc (inv (xs :. O))|}
    \reason{=}{Definition of |inv| and |invBit|}
    \stmt{|(xs :. O) .&&. inc (inv xs :. I)|}
    \reason{=}{Definition of |inc|}
    \stmt{|(xs :. O) .&&. (inc (inv xs) :. O)|}
    \reason{=}{Definition of |.&&.| and |neg|}
    \stmt{|(xs .&&. neg xs) :. O|}
    \reason{=}{Induction hypothesis}
    \stmt{|lsb xs :. O|}
  \end{sproof}
\item Next, if |x = xs :. I|, then |lsb (xs :. I) = Rep O :. I| by
  definition, whereas
  \begin{sproof}
    \stmt{|(xs :. I) .&&. neg (xs :. I)|}
    \reason{=}{Definition of |neg|}
    \stmt{|(xs :. I) .&&. inc (inv (xs :. I))|}
    \reason{=}{Definition of |inv| and |invBit|}
    \stmt{|(xs :. I) .&&. inc (inv xs :. O))|}
    \reason{=}{Definition of |inc|}
    \stmt{|(xs :. I) .&&. (inv xs :. I)|}
    \reason{=}{Definition of |.&&.|}
    \stmt{|(xs .&&. inv xs) :. I|}
    \reason{=}{Bitwise AND of $xs$ and its inverse is |Rep O|}
    \stmt{|Rep O :. I|}
  \end{sproof}
\end{itemize}
\vspace{-3\baselineskip}
\end{proof}

For the last equality we need a lemma that |xs .&&. inv xs = Rep O|, which
should be intuitively clear and can easily be proved by induction as
well.

Finally, in order to express the index conversion functions we will
develop in the next section, we need a few more things in our DSL.
First, some functions to set and clear individual bits, and to test
whether particular bits are set:

\begin{code}

setTo :: Bit -> Int -> Bits -> Bits
setTo b' 0 (bs :. _) = bs :. b'
setTo b' k (bs :. b) = setTo b' (k-1) bs :. b

set, clear :: Int -> Bits -> Bits
set = setTo I
clear = setTo O

test :: Int -> Bits -> Bool
test 0 (bs :. b) = b == I
test n (bs :. _) = test (n-1) bs

even, odd :: Bits -> Bool
odd = test 0
even = not . odd

\end{code}

The only other things we will need are left and right shift, and a
generic |while| combinator that iterates a given function, returning
the first iterate for which a predicate is false.

\begin{code}

shr :: Bits -> Bits
shr (bs :. _) = bs

shl :: Bits -> Bits
shl = (:. O)

while :: (a -> Bool) -> (a -> a) -> a -> a
while p f x
  | p x        = while p f (f x)
  | otherwise  = x

\end{code}

\section{Index Conversion} \label{sec:convert}

Before deriving our index conversion functions we must deal with one
slightly awkward fact.  In a traditional binary tree indexing scheme,
as shown in \pref{fig:bt-indexing}, the root has index $1$, every left
child is twice its parent, and every right child is one more than
twice its parent.  Recall that in a thinned segment tree, the root
node and every left child are active, with all right children being
inactive.  This makes the root an awkward special case---all active
nodes have an even index, \emph{except} the root, which has index $1$.
This makes it more difficult to check whether we are at an active
node---it is not enough to simply look at the least significant bit.

One easy way to fix this is simply to give the root index $2$, and
then proceed to label the rest of the nodes using the same
scheme---every left child is twice its parent, and every right child
is one more than twice its parent.  This results in the indexing shown
in \pref{fig:bt-indexing-two}, as if we had just taken the left
subtree of the tree rooted at $1$, and ignored the right subtree.  Of
course, this means about half the possible indices are omitted---but
that's not a problem, since we will only use these indices as an
intermediate step which will eventually get fused away.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import Diagrams.Prelude hiding (Empty)
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromJust)

-- bt depth root
bt :: Int -> Int -> BTree Int
bt 0 _ = Empty
bt d r = BNode r (bt (d-1) (2*r)) (bt (d-1) (2*r+1))

dia = bt 4 2
  # symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 4)
  # fromJust
  # renderTree dn (~~)

dn i = text ("$" ++ show i ++ "$") <> circle 1 # fc white
  \end{diagram}
  \caption{Indexing a binary tree with $2$ at the root}
  \label{fig:bt-indexing-two}
\end{figure}

\pref{fig:bt-both} shows a binary tree where nodes have been numbered
in two different ways: the left side of each node shows the node's
binary tree index (with the root having index $2$).  The right side of
each node shows its index in the Fenwick array, if it has one (inactive
nodes simply have their right half greyed out).  The table underneath
shows the mapping from Fenwick array indices (top row) to binary tree
indices (bottom row).  As a larger example, \pref{fig:bt-both-big}
shows the same thing on a binary tree one level deeper.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import FenwickDiagrams
import Control.Monad.State (evalState)

dia :: Diagram B
dia = evalState (bt 4 2 True) 1 # drawRightLeaning dn
  \end{diagram}

  \vspace{0.25in}

  \begin{tabular}{cccccccc}
    \textcolor{blue}{1} & \textcolor{blue}{2} & \textcolor{blue}{3}  & \textcolor{blue}{4} & \textcolor{blue}{5} & \textcolor{blue}{6} & \textcolor{blue}{7} & \textcolor{blue}{8} \\
    16 & 8 & 18 & 4 & 20 & 10 & 22 & 2
  \end{tabular}
  \caption{Binary tree labelled with both binary and Fenwick indexing} \label{fig:bt-both}
\end{figure}

\begin{figure}
  \centering
  \begin{diagram}[width=350]
import FenwickDiagrams
import Control.Monad.State (evalState)

dia :: Diagram B
dia = evalState (bt 5 2 True) 1 # drawRightLeaning dn
  \end{diagram}

  \vspace{0.25in}

  \begin{tabular}{cccccccccccccccc}
  \textcolor{blue}{1} & \textcolor{blue}{2} & \textcolor{blue}{3} & \textcolor{blue}{4} & \textcolor{blue}{5} & \textcolor{blue}{6} & \textcolor{blue}{7} & \textcolor{blue}{8} & \textcolor{blue}{9} & \textcolor{blue}{10} & \textcolor{blue}{11} & \textcolor{blue}{12} & \textcolor{blue}{13} & \textcolor{blue}{14} & \textcolor{blue}{15} & \textcolor{blue}{16}
  \\
  32 & 16 & 34 & 8 & 36 & 18 & 38 & 4 & 40 & 20 & 42 & 10 & 44 & 22 & 46 & 2
  \end{tabular}
  \caption{Binary tree labelled with both binary and Fenwick indexing} \label{fig:bt-both-big}
\end{figure}

Our goal is to come up with a way to calculate the binary index for a
given Fenwick index or vice versa. Staring at the table in
\pref{fig:bt-both-big}, a few patterns stand out.  Of course, all the
numbers in the bottom row are even, which is precisely because the
binary tree is numbered in such a way that all active nodes have an
even index.  Second, we can see the even numbers $32, 34 \dots 46$, in
order, in all the odd positions.  These are exactly the leaves of the
tree, and indeed, every other node in the Fenwick array will be a leaf
from the original tree.  Alternating with these, in the even
positions, are the numbers $16\;\; 8\;\; 18\;\; 4 \dots$, which
correspond to all the non-leaf nodes; but these are exactly the
sequence of binary indices from the bottom row of the table in
\pref{fig:bt-both}---since the internal nodes in a tree of height 4
themselves constitute a tree of height 3, with the nodes occurring in
the same order.

These observations lead to the recurrence shown in \pref{fig:seqrec}
for the sequence $b_n$ of binary indices for the nodes stored in a
Fenwick array of length $2^n$: $b_0$ is just the singleton sequence
$[2]$, and otherwise $b_n$ is the even numbers
$2^{n+1}, 2^{n+1} + 2, \dots, 2^{n+1} + 2^n - 2$ interleaved with $b_{n-1}$.

\begin{figure}
\centering

%if false
\begin{code}

ul :: a -> a
ul = id

class Exponentiable a where
  pow :: a -> Int -> a

instance Exponentiable Int where
  pow = (^)

instance Exponentiable (a -> a) where
  pow _ 0 = id
  pow f k = pow f (k-1) . f

\end{code}
%endif

\begin{code}

interleave :: [a] -> [a] -> [a]
[] `interleave` _ = []
(x : xs) `interleave` ys = x : (ys `interleave` xs)

b :: Int -> [Int]
b 0 = [2]
b n = map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)

\end{code}

\caption{Recurrence for sequence of binary tree indices in a Fenwick
  array}
  \label{fig:seqrec}
\end{figure}

We can check that this does in fact reproduce the observed sequence
for $n = 4$:

\begin{verbatim}
ghci> b 4
[32,16,34,8,36,18,38,4,40,20,42,10,44,22,46,2]
\end{verbatim}

Let |s ! k| denote the $k$th item in the list $s$ (counting from 1),
as defined in \pref{fig:index-interleave}.  The same figure also lists
two easy lemmas about the interaction between indexing and
interleaving, namely, |(xs `interleave` ys) ! (2*j) = ys ! j| and
|(xs `interleave` ys) ! (2*j - 1) = xs!j| (as long as |xs| and |ys|
have equal lengths).  With these in hand, we can
define the Fenwick to binary index conversion function as
\[ |f2b n k = b n ! k|. \]
%if false
\begin{code}

f2b n k = b n ! k

\end{code}
%endif
Of course, since $b_n$ is of length $2^n$, this function is only
defined on the range $[1, 2^n]$.

\begin{figure}
  \centering
\begin{code}

(a : _) ! 1 = a
(_ : as) ! k = as ! (k-1)

\end{code}

\begin{spec}
-- If |len(xs) == len(ys)|:
(xs `interleave` ys) ! (2*j)      = ys ! j
(xs `interleave` ys) ! (2*j - 1)  = xs ! j
\end{spec}

  \caption{Indexing and interleaving}
  \label{fig:index-interleave}
\end{figure}

We can now simplify the  definition of |f2b| as follows. First of all, for even
inputs, we have

\begin{sproof}
  \stmt{|f2b n (2*j)|}
  \reason{=}{Definition of |f2b|}
  \stmt{|b n ! (2 * j)|}
  \reason{=}{Definition of |b|}
  \stmt{|(map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)) ! (2 * j)|}
  \reason{=}{|`interleave`-!| lemma}
  \stmt{b (n-1) ! j}
  \reason{=}{Definition of |f2b|}
  \stmt{|f2b (n-1) j|.}
\end{sproof}
Whereas for odd inputs,
\begin{sproof}
  \stmt{|f2b n (2*j-1)|}
  \reason{=}{Definition of |f2b|}
  \stmt{|b n ! (2 * j-1)|}
  \reason{=}{Definition of |b|}
  \stmt{|(map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)) ! (2*j-1)|}
  \reason{=}{|`interleave`-!| lemma}
  \stmt{|map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] ! j|}
  \reason{=}{Definition of |map|, algebra}
  \stmt{|2 * (pow 2 n + j - 1)|}
  \reason{=}{algebra}
  \stmt{|pow 2 (n+1) + 2j-2|}
\end{sproof}
Thus we have
\[ |f2b n k| = \begin{cases} |f2b (n-1) (k/2)| & k \text{ even} \\ 2^{n+1}
    + k - 1 & k \text{ odd} \end{cases} \] Note that when $n = 0$ we
must have $k = 1$, and hence $|f2b 0 1| = 2^0 + 1 - 1 = 1$, as
required, so this definition is valid for all $n \geq 0$.  Now factor
$k$ uniquely as $2^a \cdot b$ where $b$ is odd.  Then by induction we
can see that
\[ |f2b n (pow 2 a * b) = f2b (n - a) b| = 2^{n-a+1} + b - 1. \] So,
in other words, computing |f2b| consists of repeatedly dividing by 2
(\ie right bit shifts) as long as the input is even, and then finally
decrementing and adding a power of $2$.  However, knowing what power
of $2$ to add at the end depends on knowing how many times we shifted.
A better way to think of it is to add $2^{n+1}$ at the
\emph{beginning}, and then let it be shifted along with everything
else.  Thus, we have the following definition of |f2b'| using our
|Bits| DSL.  Defining |shift n = while even shr . set n| separately
will make some of our proofs more compact later.

\begin{code}

shift :: Int -> Bits -> Bits
shift n = while even shr . set n

f2b' :: Int -> Bits -> Bits
f2b' n = dec . shift (n+1)

\end{code}

%if false
\begin{code}

infix 4 ===
(===) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f === g = \x -> f x == g x

\end{code}
%endif

For example, we can verify that this produces identical results to
|f2b 4| on the range $[1, 2^4]$ (for convenience, we define |(f === g)
k = f k == g k|):
\begin{Verbatim}
ghci> all (f2b 4 === fromBits . f2b' 4 . toBits) [1 .. 2^4]
True
\end{Verbatim}

We now turn to deriving |b2f n|, which converts back from binary to
Fenwick indices. |b2f n| should be a left inverse to |f2b n|, that is,
for any $k \in [1, 2^n]$ we should have |b2f n (f2b n k) == k|. If $k$
is an input to |f2b|, we have $k = 2^a \cdot b \leq 2^n$, and so
$b-1 < 2^{n-a}$.  Hence, given the output
$|f2b n k| = m = 2^{n-a+1} + b - 1$, the highest bit of $m$ is
$2^{n-a+1}$, and the rest of the bits represent $b-1$.  So, in
general, given some $m$ which is the output of |f2b n|, we can write
it uniquely as $m = 2^c + d$ where $d < 2^{c-1}$; then
\[ |b2f n (pow 2 c + d) = pow 2 (n-c+1) * (d+1)|. \] In other words,
given the input $2^c + d$, we subtract off the highest bit $2^c$,
increment, then left shift $n-c+1$ times.  Again, though, there is a
simpler way: we can increment first (note since $d < 2^{c-1}$,
incrementing cannot disturb the bit at $2^c$), then left shift enough
times to bring the leftmost bit into position $n+1$, and finally
remove it.  That is:

\begin{code}

unshift :: Int -> Bits -> Bits
unshift n = clear n . while (not . test n) shl

b2f' :: Int -> Bits -> Bits
b2f' n = unshift (n+1) . inc

\end{code}

Verifying:
\begin{verbatim}
ghci> all (fromBits . b2f' 4 . f2b' 4 . toBits === id) [1 .. 2^4]
True
\end{verbatim}

\section{Deriving Fenwick Operations} \label{sec:fenwick-ops}

We can now finally derive the required operations on Fenwick array
indices for moving through the tree, by starting with operations on a
binary indexed tree and conjugating by conversion to and from Fenwick
indices.  First, in order to fuse away the resulting conversion, we
will need a few lemmas.

\begin{lem}[shr-inc-dec] \label{lem:incshr}
  For all |bs :: Bits| which are |odd| (that is, end with |I|),
  \begin{itemize}
  \item |(shr . dec) bs = shr bs|
  \item |(shr . inc) bs = (inc . shr) bs|
  \end{itemize}
\end{lem}
\begin{proof}
  Both are immediate by definition.
\end{proof}

\begin{lem}[while-inc-dec] \label{lem:incwhile}
  The following both hold for all |Bits| values:
  \begin{itemize}
  \item |inc . while odd shr = while even shr . inc|
  \item |dec . while even shr = while odd shr . dec|
  \end{itemize}
\end{lem}
\begin{proof}
  Easy proof by induction on |Bits|.  For example, for the |inc| case,
  the functions on both sides discard consecutive 1 bits and then flip
  the first 0 bit to a 1.
\end{proof}

Finally, we will need a lemma about shifting zero bits in and out of
the right side of a value.

\begin{lem}[shl-shr] \label{lem:shlshr}
  For all $0 < x < 2^{n+2}$,
  \[ |(while (not . test (n+1)) shl . while even shr) x = while (not . test (n+1)) shl x|. \]
\end{lem}
\begin{proof}
  Intuitively, this says that if we first shift out all the zero bits
  and then left shift until bit $n+1$ is set, we could get the same
  result by forgetting about the right shifts entirely; shifting out
  zero bits and then shifting them back in should be the identity.

  Formally, the proof is by induction on |x|.  If |x = xs :. I| is odd, the equality is
  immediate since |while even shr x = x|. Otherwise, if |x = xs :. O|,
  on the left-hand side the |O| is immediately discarded by |shr|,
  whereas on the right-hand side |xs :. O = shl xs|, and the extra
  |shl| can be absorbed into the |while| since $|xs| < 2^{n+1}$.  What
  remains is simply the induction hypothesis.
\end{proof}

With these lemmas under our belt, let's see how to move around a
Fenwick array in order to implement |update| and |query|; we'll begin
with |update|. When implementing the |update| operation, we need to start at a leaf
and follow the path up to the root, updating all the active nodes
along the way.  In fact, for any given leaf, its closest active parent
is precisely the node stored in the slot that used to correspond to
that leaf (see \pref{fig:right-leaning}).  So to update index $i$, we
just need to start at index $i$ in the Fenwick array, and then
repeatedly find the closest active parent, updating as we go.  Recall
that the imperative code for |update| works this way, apparently
finding the closest active parent at each step by adding the LSB of
the current index:
\inputminted[fontsize=\footnotesize,firstline=8,lastline=10]{java}{FenwickTree.java}
\noindent
Let's see how to derive this behavior.

To find the closest active parent of a node under a binary indexing
scheme, we first move up to the immediate parent (by dividing the
index by two, \ie performing a right bit shift); then continue moving
up to the next immediate parent as long as the current node is a right
child (\ie has an odd index).  This yields the definition:

\begin{code}

activeParentBinary :: Bits -> Bits
activeParentBinary = while odd shr . shr

\end{code}

This is why we used the slightly strange indexing scheme with the root
having index $2$---otherwise this definition would not work for any
node whose active parent is the root!

Now, to derive the corresponding operation on Fenwick indices, we
conjugate by conversion to and from Fenwick indices, and compute as
follows.  To make the computation easier to read, the portion being
rewritten is underlined at each step.

\begin{sproof}
  \stmt{|b2f' n . activeParentBinary . f2b' n|}
  \reason{=}{expand definitions}
  \stmt{|unshift (n+1) . ul(inc . while odd shr) . shr . dec . shift (n+1)|}
  \reason{=}{\pref{lem:incwhile} (while-inc-dec)}
  \stmt{|unshift (n+1) . while even shr . inc . ul(shr . dec) . shift (n+1)|}
  \reason{=}{\pref{lem:incshr} (shr-inc-dec); |shift (n+1) x| is always odd}
  \stmt{|unshift (n+1) . while even shr . ul(inc . shr) . shift (n+1)|}
  \reason{=}{\pref{lem:incshr} (shr-inc-dec)}
  \stmt{|unshift (n+1) . ul(while even shr . shr) . inc . shift (n+1)|}
  \reason{=}{|while even shr . shr = while even shr| on an even input}
  \stmt{|ul(unshift (n+1)) . while even shr . inc . shift (n+1)|}
  \reason{=}{Definition of |unshift|}
  \stmt{|clear (n+1) . ul(while (not . test (n+1)) shl . while even shr) . inc . ul(shift (n+1))|}
  \reason{=}{\pref{lem:shlshr} (shl-shr); definition of |shift|}
  \stmt{|clear (n+1) . while (not . test (n+1)) shl . inc . while even shr . set (n+1)|}
\end{sproof}
In the final step, since the input $x$ satisfies $x \leq 2^n$, we have
$|inc . shift (n+1)| < 2^{n+2}$, so \pref{lem:shlshr} applies.

Reading from right to left, the pipeline we have just computed
performs the following steps:
\begin{enumerate}
\item Set bit $n+1$
\item Shift out consecutive zeros until finding the least significant
  $1$ bit
\item Increment
\item Shift zeros back in to bring the most significant bit back to position $n+1$,
  then clear it.
\end{enumerate}

\begin{figure}
\begin{center}
\begin{diagram}[width=100]
  import Fenwick
  import Diagrams.Prelude hiding (Empty)
  import Prelude hiding (even)

  type FBits = (Int, [Style V2 Double], Bits)

  drawBits :: FBits -> Diagram B
  drawBits (0, _, _) = mempty
  drawBits (n, [], bs :. b) = drawBits (n-1, [], bs) |||||| drawBit mempty b
  drawBits (n, (s:ss), bs :. b) = drawBits (n-1, ss, bs) |||||| drawBit s b

  bitColor O = grey
  bitColor I = blue

  drawBit :: Style V2 Double -> Bit -> Diagram B
  drawBit s b = mconcat
    [ text (show (fromEnum b)) # applyStyle s # fc (bitColor b)
    , square 1
    ]

  drawSteps :: [(FBits, Maybe String)] -> Diagram B
  drawSteps = vsep 0.5 . map drawStep

  drawStep :: (FBits, Maybe String) -> Diagram B
  drawStep (bs, Nothing) = drawBits bs # centerX
  drawStep (bs, Just s) = vsep 0.5
    [ drawBits bs # centerX
    , hsep 0.5
      [ arrowV unit_Y # centerY
      , alignedText 0 0.5 s # fontSizeL 0.7
      ]
      # alignL
    ]

  sentinelStyle n = replicate (n-1) mempty ++ [mempty # fc red]

  dia = drawSteps
    [ ((8, [], toBits 52), Just "set sentinel bit")
    , ((8, sentinelStyle 8, toBits 52 .+. toBits (2^7)), Just "shift right")
    , ((8, sentinelStyle 6, while even shr (toBits 52 .+. toBits (2^7))), Just "increment")
    , ((8, sentinelStyle 6, inc (while even shr (toBits 52 .+. toBits (2^7)))), Just "shift left")
    , ((8, sentinelStyle 8, toBits 56 .+. toBits (2^7)), Just "unset sentinel bit")
    , ((8, [], toBits 56), Nothing)
    ]
\end{diagram}
\end{center}
\caption{Adding LSB with a sentinel bit + shifts} \label{fig:bitspipeline}
\end{figure}

Intuitively, this does look a lot like adding the LSB!  In general, to
find the LSB, one must shift through consecutive $0$ bits until
finding the first $1$; the question is how to keep track of how many
$0$ bits were shifted on the way.  The |lsb| function itself keeps
track via the recursion stack; after finding the first $1$ bit, the
recursion stack unwinds and re-snocs all the $0$ bits recursed through
on the way.  The above pipeline represents an alternative approach:
set bit $n+1$ as a ``sentinel'' to keep track of how much we have
shifted; right shift until the first $1$ is literally in the ones
place, at which point we increment; and then shift all the $0$ bits
back in by doing left shifts until the sentinel bit gets back to
the $n+1$ place. One example of this process is illustrated in
\pref{fig:bitspipeline}. Of course, this only works for values that are
sufficiently small that the sentinel bit will not be disturbed
throughout the operation.

To make this more formal, we begin by defining a helper function
|atLSB|, which does an operation ``at the LSB'', that is, it shifts
out 0 bits until finding a 1, applies the given function, then
restores the 0 bits.
\newpage
\begin{code}

atLSB :: (Bits -> Bits) -> Bits -> Bits
atLSB _ (Rep O) = Rep O
atLSB f (bs :. O) = atLSB f bs :. O
atLSB f bs = f bs

\end{code}

\begin{lem}[add-lsb] \label{lem:addlsb}
  For all |x :: Bits|, |x + lsb x = atLSB inc x| and |x - lsb x =
  atLSB dec x|.
\end{lem}

\begin{proof}
  Straightforward induction on $x$.
\end{proof}

We can formally relate the ``shifting with a sentinel'' scheme to
the use of |atLSB|, with the following (admittedly rather technical)
lemma:

\begin{restatable}[sentinel]{lem}{sentinel} \label{lem:sentinel-scheme} Let $n \geq 1$ and let |f
  :: Bits -> Bits| be a function such that
  \begin{enumerate}
  \item |(f . set (n+1)) x = (set (n+1) . f) x| for any $0 < x < 2^n$, and
  \item $|f x| < 2^{n+1}$ for any $0 < x < 2^n + 2^{n-1}$.
  \end{enumerate}
  Then for all $0 < x < 2^n$,
  \[ |(unshift (n+1) . f . shift (n+1)) x = atLSB f x|. \]
\end{restatable}

The proof is rather tedious and not all that illuminating, so we omit
it
\ifJFP
(an extended version including a full proof may be found on the
author's website, at \url{http://ozark.hendrix.edu/~yorgey/pub/Fenwick-ext.pdf}).
\else
here (a detailed proof can be found in an appendix).
\fi
However, we do note that both |inc| and
|dec| fit the criteria for |f|: incrementing or decrementing some
$0 < x < 2^n$ cannot affect the $(n+1)$st bit as long as $n \geq 1$,
and the result of incrementing or decrementing a number less than
$2^n + 2^{n-1}$ will be a number less than $2^{n+1}$.  We can
now put all the pieces together show that adding the LSB at each step
is the correct way to implement |update|.

\begin{thm}
  Adding the LSB is the correct way to move up a Fenwick-indexed tree
  to the nearest active parent, that is,
  \[ |activeParentFenwick = b2f' n . activeParentBinary . f2b' n = \x
    -> x + lsb x| \] everywhere on the range $[1, 2^n)$. (We exclude
  $2^n$ since it corresponds to the root of the tree under a Fenwick
  indexing scheme.)
\end{thm}
\begin{proof}
\begin{sproof}
  \stmt{|b2f' n . activeParentBinary . f2b' n|}
  \reason{=}{Previous calculation}
  \stmt{|unshift (n+1) . inc . shift (n+1)|}
  \reason{=}{\pref{lem:sentinel-scheme} (sentinel)}
  \stmt{|atLSB inc|}
  \reason{=}{\pref{lem:addlsb} (add-lsb)}
  \stmt{|\x -> x + lsb x|}
\end{sproof}
\vspace{-3\baselineskip}
\end{proof}

We can carry out a similar process to derive an implementation for
prefix query (which supposedly involves \emph{subtracting} the LSB).
Again, if we want to compute the sum of $[1, j]$, we can start at
index $j$ in the Fenwick array, which stores the sum of the unique
segment ending at $j$.  If the node at index $j$ stores the segment
$[i,j]$, we next need to find the unique node storing a segment that
ends at $i-1$.  We can do this repeatedly, adding up segments as we
go.

\begin{figure}
\begin{center}
\begin{diagram}[width=300]
  import FenwickDiagrams
  import SegTree
  import Data.Monoid
  import Control.Arrow ((***), second)

  dia :: Diagram B
  dia = vsep 0.7
    [ sampleArray
      # mkSegTree
      # rq' i j
      # fst
      # drawSegTree opts
    , (fst (leafX i n) ^& 0) ~~ (snd (leafX j n) ^& 0)
      # lc green
      # applyStyle defRangeStyle
    ]
      <> (arrowBetween' arrOpts (5 ^& (-2)) (0 ^& (-2))) # lw veryThick
      <> (arrowBetween' arrOpts (3.5 ^& (-6)) (1.5 ^& (-6))) # lw veryThick
    where
      i = 1
      j = 11
      n = length sampleArray

      de (_, (Recurse, _)) x _ y
        || location x ^. _x > location y ^. _x =
             beneath (arrowBetween' arrOpts (location y) (location x) # lw veryThick
                      <> (location x ~~ location y))
      de _ x _ y = beneath (location x ~~ location y)

      arrOpts = with & gaps .~ local 0.5

      opts :: SegTreeOpts (Visit, Sum Int) B
      opts = (mkSTOpts (showRangeOpts' False False) :: SegTreeOpts (Visit, Sum Int) B)
        { drawEdge = de
        }
\end{diagram}
\end{center}
\caption{Moving up a segment tree to find successive prefix
  segments} \label{fig:segment-tree-prefix-query-up}
\end{figure}

      % drawSTOpts :: SegTreeOpts (Visit, Sum Int) B
      % drawSTOpts = STOpts
      %   { drawNode = drawNode' (undefined :: DrawNodeOpts (Visit, Sum Int) B)
      %         -- SegNode (Visit, Sum Int) -> Int -> Int -> QDiagram B V2 Double Any
      %   , drawEdge = drawEdgeDef
      %   , stVSep = 1
      %   , leanRight = False
      %   }


Staring at \pref{fig:segment-tree-prefix-query-up} for inspiration, we
can see that what we want to do is find the \emph{left sibling} of our
\emph{closest inactive parent}, that is, we go up until finding the
first ancestor which is a right child, then go to its left sibling.
Under a binary indexing scheme, this can be implemented simply as:

\begin{code}

prevSegmentBinary :: Bits -> Bits
prevSegmentBinary = dec . while even shr

\end{code}

\begin{thm}
  Subtracting the LSB is the correct way to move up a Fenwick-indexed
  tree to the to active node covering the segment previous to the
  current one, that is,
  \[ |prevSegmentFenwick = b2f' n . prevSegmentBinary . f2b' n = \x ->
    x - lsb x| \]
  everywhere on the range $[1, 2^n)$.
\end{thm}
\begin{proof}
\begin{sproof}
  \stmt{|b2f' n . prevSegmentBinary . f2b' n|}
  \reason{=}{expand definitions}
  \stmt{|unshift (n+1) . ul(inc . dec) . while even shr . dec . shift (n+1)|}
  \reason{=}{|inc . dec = id|}
  \stmt{|ul(unshift (n+1)) . while even shr . dec . shift (n+1)|}
  \reason{=}{Definition of |unshift|}
  \stmt{|clear (n+1) . ul(while (not . test (n+1)) shl . while even shr) . dec . shift (n+1)|}
  \reason{=}{\pref{lem:shlshr} (shl-shr)}
  \stmt{|ul(clear (n+1) . while (not . test (n+1)) shl) . dec . shift
    (n+1)|}
  \reason{=}{Definition of |unshift|}
  \stmt{|unshift (n+1) . dec . shift (n+1)|}
  \reason{=}{\pref{lem:sentinel-scheme} (sentinel)}
  \stmt{|atLSB dec|}
  \reason{=}{\pref{lem:addlsb} (add-lsb)}
  \stmt{|\x -> x - lsb x|}
\end{sproof}
\vspace{-3\baselineskip}
\end{proof}

\section{Conclusion}

Historically, to my knowledge, Fenwick trees were not actually
developed as an optimization of segment trees as presented here.  This
has merely been a fictional---but hopefully illuminating---alternate
history of ideas, highlighting the power of functional thinking,
domain-specific languages, and equational reasoning to explore
relationships between different structures and algorithms.  As future
work, it would be interesting to explore some of the mentioned
generalizations of segment trees, to see whether one can derive
Fenwick-like structures that support additional operations.

\section*{Acknowledgments}

Thanks to the anonymous JFP reviewers for their helpful feedback,
which resulted in a much improved presentation.  Thanks also to Penn PL
Club for the opportunity to present an early version of this work.
\bigskip

\noindent \textbf{Conflicts of Interest}. None

\bibliographystyle{JFPlike}
\bibliography{fenwick}

\ifJFP
\else
\section*{Appendix}

For completeness, we include here a proof of
\pref{lem:sentinel-scheme}, which shows that for functions $f$
satisfying suitable conditions, |atLSB f| has the same effect as the
``sentinel scheme'' where we set a sentinel bit, shift to bring the
LSB to the ones place, perform $f$, then shift back.  To complete the
proof of this lemma we first need a few more.

\begin{lem} \label{lem:clearshl}
  |clear (n+1) . shl = shl . clear n|
\end{lem}
\begin{proof}
  Immediate by a simple computation.
\end{proof}

\begin{lem} \label{lem:shlwhile}
 For all $n \geq 0$ and $0 < x < 2^{n+1}$, \[ |(while (not . test (n+1)) shl) x = (shl
   . while (not . test n) shl) x|. \]
\end{lem}
\begin{proof}
  Intuitively, if $x$ is small enough, we can either keep shifting
  left until bit $n+1$ is set, or we can shift left until bit $n$ is
  set and then shift left one additional time.

  Formally, the proof is by induction on the size of $2^{n+1} - x$.
  First, if $2^n \leq x < 2^{n+1}$, then bit $n$ of $x$ must be $1$, and both
  sides will be equal to |shl x|.  Otherwise, suppose $x < 2^n$.  Then
  \begin{sproof}
    \stmt{|(while (not . test (n+1)) shl) x|}
    \reason{=}{$x < 2^{n+1}$}
    \stmt{|(while (not . test (n+1)) shl) (shl x)|}
    \reason{=}{Induction hypothesis, since $2^{n+1} - |shl x| < 2^{n+1} - x$}
    \stmt{|(shl . while (not . test n) shl) (shl x)|}
    \reason{=}{$x < 2^n$}
    \stmt{|(shl . while (not . test n) shl) x|}
  \end{sproof}
\vspace{-3\baselineskip}
\end{proof}

Now we can finally prove \pref{lem:sentinel-scheme}, which we restate
here for convenience.

\sentinel*

\begin{proof}
  By induction on $x$.  First, suppose |x = xs :. I|.  In that case,
  |atLSB f (xs :. I) = f (xs :. I)|, and
  \begin{sproof}
    \stmt{|(unshift (n+1) . f . ul(shift (n+1))) (xs :. I)|}
    \reason{=}{Definition of |shift|}
    \stmt{|(unshift (n+1) . f . while even shr . ul(set (n+1))) (xs :. I)|}
    \reason{=}{Definition of |set|}
    \stmt{|(unshift (n+1) . f . ul(while even shr)) (set n xs :. I)|}
    \reason{=}{|while even f y = y| on odd |y|}
    \stmt{|(unshift (n+1) . f) (ul(set n xs) :. I)|}
    \reason{=}{Definition of |set|}
    \stmt{|(unshift (n+1) . ul(f . set (n+1))) (xs :. I)|}
    \reason{=}{|f| commutes with |set (n+1)| on input $< 2^n$}
    \stmt{|(ul(unshift (n+1)) . set (n+1) . f) (xs :. I)|}
    \reason{=}{Definition of |unshift|}
    \stmt{|(clear (n+1) . ul(while (not . test (n+1)) shl . set (n+1)) . f) (xs :. I)|}
    \reason{=}{|not . test (n+1)| is false on output of |set (n+1)|}
    \stmt{|(ul(clear (n+1) . set (n+1)) . f) (xs :. I)|}
    \reason{=}{|clear (n+1)| and |set (n+1)| are inverse, since $|f x| < 2^{n+1}$}
    \stmt{|f (xs :. I)|}
  \end{sproof}
  Next, if |x = xs :. O|, |atLSB f (xs :. O) = atLSB f xs :. O|.  For
  the left-hand side, we can compute:
  \begin{sproof}
    \stmt{|(unshift (n+1) . f . ul(shift (n+1))) (xs :. O)|}
    \reason{=}{Definition of |shift|}
    \stmt{|(unshift (n+1) . f . while even shr . ul(set (n+1))) (xs :. O)|}
    \reason{=}{Definition of |set|}
    \stmt{|(unshift (n+1) . f . while even shr) (ul(set n xs :. O))|}
    \reason{=}{Definition of |while| and |even|}
    \stmt{|(ul(unshift (n+1)) . f . ul(while even shr . set n)) xs|}
    \reason{=}{Definition of |unshift| and |shift|}
    \stmt{|(clear (n+1) . ul(while (not . test (n+1)) shl) . f . shift n) xs|}
  \end{sproof}
  At this point we would like to rewrite |while (not . test (n+1))
  shl| by pulling out one iteration of |shl|. Since
  $|x = xs :. O| < 2^n$, we have $|xs| < 2^{n-1}$ and
  $|shift n xs| < 2^n + 2^{n-1}$ (recall that |shift n = while even
  shr . set n| sets the $n$th bit and then can only make the number
  smaller by doing repeated right shifts). Hence by assumption
  $|f (shift n xs)| < 2^{n+1}$, and we may apply \pref{lem:shlwhile}.
  \begin{sproof}
    \stmt{|(clear (n+1) . ul(while (not . test (n+1)) shl) . f . shift n) xs|}
    \reason{=}{\pref{lem:shlwhile}}
    \stmt{|(ul(clear (n+1) . shl) . while (not . test n) shl . f . shift n) xs|}
    \reason{=}{\pref{lem:clearshl}}
    \stmt{|(shl . ul(clear n . while (not . test n) shl) . f . shift n) xs|}
    \reason{=}{Definition of |unshift|}
    \stmt{|(shl . unshift n . f . shift n) xs|}
    \reason{=}{Induction hypothesis}
    \stmt{|shl (atLSB f xs)|}
    \reason{=}{Definition of |shl|}
    \stmt{|atLSB f xs :. O|}
  \end{sproof}
\vspace{-3\baselineskip}
\end{proof}
\fi

\end{document}
