% -*- mode: LaTeX; compile-command: "./build.sh" -*-

%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[acmsmall]{acmart}\settopmatter{}


%% Journal information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmJournal{PACMPL}
\acmVolume{1}
\acmNumber{ICFP} % CONF = POPL or ICFP or OOPSLA
\acmArticle{1}
\acmYear{2021}
\acmMonth{8}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2018}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Note: Authors migrating a paper from PACMPL format to traditional
%% SIGPLAN proceedings format must update the '\documentclass' and
%% topmatter commands above; see 'acmart-sigplanproc-template.tex'.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\let\Bbbk\undefined  % https://github.com/kosmikus/lhs2tex/issues/82
%include polycode.fmt

%format :--:   = "\mathrel{:\!\!\text{---}\!\!:}"
%format `inR`  = "\in"
%format inR    = "(" `inR` ")"
%format `subR` = "\subseteq"
%format subR   = "(" `subR` ")"

%format <>     = "+ "
%format mempty = "0 "

%format lo1
%format lo2
%format hi1
%format hi2

%format `interleave` = "\interleaveop"
%format interleave = "(" `interleave` ")"

%format pow (a) (b) = a "^ {" b "}"

%format * = "\cdot"

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
% \usepackage{subdepth}   %% Unify positioning of all subscripts

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{section~\ref{#1}}
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
\newcommand{\mempty}{0}

\newcommand{\Up}{\textbf{U}\xspace}
\newcommand{\RQ}{\textbf{RQ}\xspace}

\newcommand{\ie}{\emph{i.e.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\interleaveop}{\curlyvee}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

%% Title information
\title{You Could Have Invented Fenwick Trees (Functional Pearl)}
   %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
% \titlenote{with title note}             %% \titlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
% \subtitle{Subtitle}                     %% \subtitle is optional
% \subtitlenote{with subtitle note}       %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Brent A. Yorgey}
% \authornote{with author1 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
% \orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  % \position{Position1}
  \department{Department of Mathematics and Computer Science}
  \institution{Hendrix College}            %% \institution is required
  \streetaddress{1600 Washington Ave.}
  \city{Conway}
  \state{AR}
  \postcode{72032}
  \country{USA}                    %% \country is recommended
}
\email{yorgey@@hendrix.edu}          %% \email is recommended


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
  \emph{Fenwick trees}, also known as \emph{bit-indexed trees}, are a
  clever solution to the problem of maintaining a sequence of values
  while allowing both updates and range queries in sublinear time.
  Their implementation is concise and efficient---but also somewhat
  baffling, consisting largely of nonobvious bitwise operations on
  indices.  In this functional pearl, we begin with \emph{segment
    trees}, a much more straightforward, easy-to-verify, purely
  functional solution to the problem, and use equational reasoning to
  derive the implementation of Fenwick trees as an optimized variant
  of segment trees.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


\section{Introduction}

Suppose we have a sequence of $n$ integers $a_1, a_2, \dots, a_n$, and
want to be able to perform two operations:

\begin{itemize}
\item \emph{Update} the value at index $i$ to a new value $v$.
\item Find the sum of all values in a particular range $[i, j]$, that
  is, $a_i + a_{i+1} + \dots + a_j$.  We call this operation a
  \emph{range query}.
\end{itemize}

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
  , text "$a_2 + a_3 + x + a_5$" # fontSizeL 0.6
    # translateX (2.5 * leafWidth)
  ]
  where
    draw2 4 = draw "x"
    draw2 n = draw ("a_" ++ show n)
\end{diagram}
\end{center}
\caption{Update and range query operations} \label{fig:update-rq}
\end{figure}

If we simply store the integers in a mutable array, then we can update
in constant time, but a range query requires time linear in the size
of the range, since we must iterate through the entire range $[i, j]$
to add up the values.

In order to improve the running time of a range query, one obvious
idea is to somehow cache (at least some of the) range sums.  However,
this must be done with care, since the cached sums must also be
updated appropriately when updating.  For example, a straightforward
approach would be to use an array $P$ where $P_i$ stores the prefix
sum $a_1 + \dots + a_i$; $P$ can be precomputed in linear time via a
scan.  Now range queries are fast: we can obtain $a_i + \dots + a_j$
in constant time by computing $P_j - P_{i-1}$ (for convenience we set
$P_0 = 0$ so this works even when $i=1$).  Unfortunately, it is update
that now takes linear time, since changing $a_i$ requires updating
$P_j$ for every $j \geq i$.

Is it possible to get \emph{both} operations to run in sublinear time?
This is more than just academic: the problem was originally considered
in the context of \emph{arithmetic coding}, a family of techniques for
turning messages into sequences of bits for storage or transmission.
In order to minimize the bits required, one generally wants to assign
shorter bit sequences to more frequent characters, and vice versa;
this leads to the need to maintain a dynamic table of character
frequencies.  We \emph{update} the table every time a new character is
processed, and query the table for \emph{cumulative frequencies} in
order to subdivide a unit interval into consecutive segments
proportional to the frequency of each character.  \todoi{cite Fenwick,
original Russian paper.  not a tutorial on arithmetic coding.}

\todo{Mention sqrt decomposition: $O(1)$ update, $O(\sqrt n)$ range queries}

The answer, of course, is yes: we can get both operations to run in
logarithmic time if we use a divide-and-conquer approach to caching
range sums.  In particular, we can make a balanced binary tree where
the leaves store the sequence itself, and every internal node stores
the sum of its children.  (This will be a familiar idea to many
functional programmers; for example, finger trees
\citep{Hinze-Paterson:FingerTree} use a similar sort of scheme.)  The
resulting data structure is popularly known as a \emph{segment
  tree}\footnote{There is some confusion of terminology here.  As of
  this writing, the Wikipedia article on \emph{segment trees}
  \citep{wiki:SegmentTree} is about an interval data structure used in
  computational geometry.  However, most of the Google search results
  for ``segment tree'' are from the world of competitive programming,
  where it refers to the data structure considered in this paper (see,
  for example, \citet[\S 2.4.3] {CP3}).  The two are largely
  unrelated.}, presumably because each internal node ultimately caches
the sum of a (contiguous) \emph{segment} of the underlying sequence.
\pref{fig:segment-tree} shows a segment tree built on a sample array
of length $n=16$ (for simplicity, we will assume that $n$ is a power
of two, although it is easy to generalize to situations where it is
not). Each leaf of the tree corresponds to an array entry; each
internal node is drawn with a grey bar showing the range of the
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
    the query range $[i, j]$, return the value of the current
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
\pref{fig:segment-tree-range-query} illustrates the process of computing
the sum of the range $[4 \dots 11]$.  Blue nodes are the ones we
recurse through; green nodes are those whose range is wholly contained
in the query range, and are returned without recursing further; grey
nodes are disjoint from the query range and return zero.

On this small example tree, it may seem that we visit a significant
fraction of the total nodes, but in general, we visit no more than
about $4 \lg n$ nodes.  \pref{fig:big-range-query} makes this more
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

\section{Segment Trees, Generally}

Although most reference material on segment trees (or Fenwick trees)
talks about sums of \emph{integers}, this is needlessly specific.  In
general, all we need is a sequence of elements $a_1, \dots, a_n$ from
some \emph{monoid}.  Recall that a monoid is a set $M$ together with
an associative binary operation $\oplus : M \times M \to M$ and an
identity element $\mempty \in M$ such that
$m \oplus \mempty = \mempty \oplus m = m$ for all $m \in M$. We will
continue to talk about ``sums'' of elements of a monoid $M$ even
though the monoidal operation need not be sum-like in general (for
example, the set of natural numbers forms a monoid under
multiplication).  However, the ``sum'' metaphor does fail in one
important way: unlike addition, $\oplus$ need not be commutative, that
is, we may have $a \oplus b \neq b \oplus a$.  All the data structures
we will discuss work perfectly well for non-commutative monoids,
though some care is required to ensure values are combined in the
correct order.

Some monoids also have \emph{inverses}, that is, for each $m \in M$
there is an element $-m \in M$ such that
$m \oplus (-m) = (-m) \oplus m = \mempty$.  Such monoids-with-inverses
are called \emph{groups}.  For convenience, in any group we can also
define a ``subtraction'' operation $a \ominus b = a \oplus (-b)$.
Although basic segment trees work with any monoid, the constructions
we consider in the rest of the paper will generally require a group.

\section{Implementing Segment Trees}
\label{sec:impl-seg-trees}

\pref{fig:haskell-segtree} exhibits a simple, generic implementation
of a segment tree in Haskell, using some utilities for working with
index ranges shown in \pref{fig:ranges}.  We store a segment tree as a
recursive algebraic data type, and implement |update| and |rq| using
code that directly corresponds to the recursive descriptions given in
the previous section.

\begin{figure}
\begin{code}

-- ($a$ :--: $b$) represents the closed interval $[a,b]$
data Range = Int :--: Int
  deriving (Eq, Show)

subR :: Range -> Range -> Bool
(lo1 :--: hi1) `subR` (lo2 :--: hi2) = lo2 <= lo1 && hi1 <= hi2

inR :: Int -> Range -> Bool
k `inR` i = (k :--: k) `subR` i

disjoint :: Range -> Range -> Bool
disjoint (lo1 :--: hi1) (lo2 :--: hi2) = hi1 < lo2 || hi2 < lo1

\end{code}
  \caption{Range utilities}
  \label{fig:ranges}
\end{figure}

\begin{figure}
\begin{code}

data SegTree a where
  Empty   :: SegTree a
  Branch  :: a -> Range -> SegTree a -> SegTree a -> SegTree a

update :: Monoid a => Int -> a -> SegTree a -> SegTree a
update _ _ Empty = Empty
update i v b@(Branch a rng l r)
  | i `inR` rng  = Branch (a <> v) rng (update i v l) (update i v r)
  | otherwise    = b

rq :: Monoid a => Range -> SegTree a -> a
rq _ Empty = mempty
rq q (Branch a rng l r)
  | disjoint rng q  = mempty
  | rng `subR` q    = a
  | otherwise       = rq q l <> rq q r

\end{code}
\caption{Simple segment tree implementation in Haskell} \label{fig:haskell-segtree}
\end{figure}

Although this implementation is simple and relatively straightforward
to understand, compared to simply storing the sequence of values in an
array, it incurs a good deal of overhead.  We can be more clever in
our use of space by storing all the nodes of a segment tree in an
array, using the standard indexing scheme illustrated in
\pref{fig:bt-indexing} (for example, this scheme, or something like
it, is commonly used to implement binary heaps).  The root has label
$1$; every time we descend one level we append an extra bit: $0$ when
we descend to the left child and $1$ when we descend to the right.
Thus, the index of each node records the sequence of left-right
choices along the path to that node from the root.  Going from a node
to its children is as simple as doing a left bit-shift and optionally
adding 1; going from a node to its parent is a right bit-shift.  This
defines a bijection from the positive natural numbers to the nodes of
an infinite binary tree.  If we label the segment tree array with
$s_1 \dots s_{2n-1}$, then $s_1$ stores the sum of all the $a_i$,
$s_2$ stores the sum of the first half of the $a_i$, $s_3$ stores the
sum of the second half, and so on.  $a_1 \dots a_n$ themselves are
stored as $s_n \dots s_{2n-1}$, and in general $a_i$ is stored as
$s_{n+i-1}$.

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
we have discussed can be straightforwardly transformed into imperative
code that works with a mutable array: for example, instead of storing
a reference to the current subtree, we store an integer index; every
time we want to descend to the left or right we simply double the
current index or double and add one; and so on.

\section{Segment Trees are Redundant}

Of course, segment trees are redundant in the sense that they cache
range sums which could easily be recomputed from the original
sequence.  That's the whole point: caching these ``redundant'' sums
trades off space for time, allowing us to perform arbitrary range
queries more quickly at the cost of doubling the required storage
space.

However, if the values come from a group, segment trees are redundant
in a stronger sense: we can throw out almost \emph{half} of the data
in a segment tree and still retain the logarithmic running time for
updates and range queries!

How, you ask?  Simple: just throw out the data stored in \emph{every
  node which is a right child}. \pref{fig:deactivate-right} shows the
same example tree we have been using, but with the data deleted from
every right child.  Note that ``every right child'' includes both
leaves and internal nodes: we throw out the data associated to
\emph{every} node which is the right child of its parent.  We will refer
to the nodes with discarded data as \emph{inactive} and the remaining
nodes (that is, left children and the root) as \emph{active}.  We also
say that a tree with all its right children inactivated in this way
has been \emph{thinned}.

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

First, let's see that there is enough information remaining to
reconstruct the information that was discarded.  You might wish to
pause at this point and work it out for yourself: can you deduce what
values must go in the greyed-out nodes in \pref{fig:deactivate-right},
without peeking at any previous figures?

\begin{theorem}
  The value of any inactive node in a thinned segment tree can be
  recovered, in $O(\lg n)$ time, using only the values of active nodes.
\end{theorem}
\begin{proof}
  The proof is by induction on the depth of an inactive node from its
  nearest active ancestor.  Note that every inactive node must have an
  active ancestor; if nothing else, the root of the tree remains
  active.
  \begin{itemize}
  \item In the base case, if an inactive node is the child of an
    active node, the situation looks like the diagram on the left side
    of \pref{fig:inactive-child}.
    \begin{figure}
    \begin{center}
    \begin{diagram}[width=150]
      import FenwickDiagrams
      import SegTree
      dia :: Diagram B
      dia = hsep 2
        [ t # deactivate # drawSegTree stopts
          # beneath upedge
        , t # deactivateR Inactive # drawSegTree stopts
          # beneath upedge
        ]
        where
          t = Branch "p" 1 2 (Leaf "l" 1) (Leaf "r" 2)
          iopts = (showInactiveOpts True) { nodeShape = const circleNodeShape }
          stopts = (mkSTOpts iopts) { stVSep = 0.5 }
          upedge = ((origin ~~ ((-0.5) ^& 1)) # dashingL [0.05,0.05] 0)
    \end{diagram}
    \end{center}
    \caption{An inactive node whose parent is: (L) active (R) inactive} \label{fig:inactive-child}
    \end{figure}
    In this case $p = l \oplus r$ by definition, so $r$ can be
    computed as $(-l) \oplus p$. (Not $p \ominus l$, since the
    group may not be commutative!)
  \item Otherwise, the situation looks like the right side of
    \pref{fig:inactive-child}.  Again $r = (-l) \oplus p$, but we do
    not know the value of $p$.  However, since $p$ is closer to its
    nearest active ancestor than $r$, by the induction hypothesis we
    can find an expression for $p$ using only the values of active
    nodes; substituting this into $r = (-l) \oplus p$ yields the
    desired expression for $r$.
  \end{itemize}
  As for taking logarithmic time, the inductive case shows that the
  number of operations ultimately needed to compute $r$ grows linearly
  with the depth of $r$ from its nearest active ancestor, which is
  bounded by the depth of the tree.
\end{proof}

This proof is, in fact, an algorithm, although this algorithm isn't
typically used, because it is too specialized. Simply being able to
\emph{recover} all the discarded information isn't good enough; we
need to be able to perform range queries and updates.

Updates are easy: as before, we only need to update nodes along the
path from the modified leaf to the root, simply skipping any inactive
nodes along the way.  However, it is less clear that we can still do
range queries in $O(\lg n)$ time.  Naively, we would need to do
$O(\lg n)$ work (using the above algorithm) to reconstruct each of the
$O(\lg n)$ nodes needed to compute a range sum, leading to
$O((\lg n)^2)$ time.  This isn't bad, but we can do better.

\begin{theorem}
  Given a thinned segment tree, the sum of \emph{any prefix} of the
  original array can be computed, in logarithmic time, using only the
  values of active nodes.
\end{theorem}
\begin{proof}
  By induction on the size $m$ of the required prefix.  In the base
  case, when $m=0$, the sum of an empty prefix is obviously easy to
  compute given the existence of an identity value $\mempty$.
  Otherwise, consider whether $m$ is even or odd.
  \begin{itemize}
  \item If $m=2k$ is even, then \todoi{picture!} the prefix sum of the
    first $2k$ array elements is the same as the prefix sum of the
    first $k$ elements one level up, which we can find by induction.
    \todoi{Say something more general, either here or previously,
      about the fact that removing the last level of a segment tree
      leaves us with another valid segment tree.}
  \item On the other hand, if $m = 2k+1$ is odd, then \todoi{picture!}
    the last element in the desired range is a left child (or the root
    itself, if $m = 1$) and therefore active.  We can thus find
    the sum of the first $2k+1$ elements by combining the sum of the
    first $2k$ elements with the value of the single active element at
    the end.
  \end{itemize}
  \todoi{Explain why this takes $O(\lg n)$ time.}
  \todoi{Turn this into working code??}
\end{proof}

\begin{corollary}
  Range queries on thinned segment trees can be performed in $O(\lg n)$ time.
\end{corollary}
\begin{proof}
  We can compute any range sum by subtracting prefix sums:
  $RQ(i,j) = -P(i-1) \oplus P(j)$ (or just $P(j) \ominus P(i-1)$ for
  commutative groups). \todoi{picture}
\end{proof}

Note that computing $RQ(i,i)$ gives us another way to recover the
value of an individual inactive element.

\section{Fenwick trees}

How should we actually store a thinned segment tree in memory?  If we
stare at \pref{fig:deactivate-right} again, an obvious strategy
suggests itself: simply take every active node and ``slide'' it down
and to the right until it lands in an empty spot in the underlying
array, as illustrated in \pref{fig:sliding-right}.  This sets up a
one-to-one correspondence between active nodes and indices in the
range $1 \dots n$.  Another way to understand this indexing scheme is
to use a postorder traversal of the tree, skipping over inactive
nodes and giving consecutive indices to active nodes encountered
during the traversal. \todoi{Explain in more detail---this is crucial!}

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

This method of storing the active nodes from a thinned segment tree in
an array is precisely what is commonly known as a \emph{Fenwick tree},
or \emph{bit-indexed tree}. \todoi{XXX cite} Although this is a clever use of
space, the big question is how to implement the update and range query
operations.  Our implementations of these operations for segment trees
worked by recursively descending through the tree. When storing the
active nodes of a thinned tree in an array, it is not obvious what
operations on array indices will correspond to moving around the tree.

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

\todoi{This is a
  Fenwick tree, or bit-indexed tree.  Question: how to carry out the
  operations?  Code is clever, concise, fast in practice, and
  extremely nonobvious.  Our goal: derive it!}

Our goal will be to first derive functions for converting back and
forth between Fenwick numbering and full binary tree numbering.  Then
we can derive operations on Fenwick trees from operations on segment
trees by converting to binary tree numbering, doing the operation, and
converting back.  Fusing away the conversions via equational reasoning
will yield concise implementations of operations directly on Fenwick
trees.

\section{Converting XXX}

Figure \todoi{figure: binary tree labelled with both binary and
  thinned in-order labels} shows a binary tree where nodes have been
numbered in two different ways: all nodes have been labelled with the
simple binary indexing scheme

% \begin{verbatim}
% data BT a where
%   Leaf   :: a -> BT a
%   Branch :: a -> BT a -> BT a -> BT a

% data Nat where
%   Z :: Nat
%   S :: Nat -> Nat

% data Bin where
%   One :: Bin
%   O :: Bin -> Bin
%   I :: Bin -> Bin

% bt :: Nat -> Bin -> BT Bin
% bt Z     i = Leaf i
% bt (S n) i = Branch i (bt n (O i)) (bt n (I i))
% \end{verbatim}

Our goal is to come up with a way to calculate the binary index for a
given Fenwick index or vice versa.  To this end, consider the sequence
of binary indices corresponding to the Fenwick indices $1 \dots 2^n$.
For example, when $n = 4$ (as in XXX fig. whatever), we have the
sequence shown in \pref{tab:indexing}.

\begin{table}[htp]
  \centering
  \begin{tabular}{cccccccccccccccc}
  1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10 & 11 & 12 & 13 & 14 & 15 & 16
  \\
  16 & 8 & 18 & 4 & 20 & 10 & 22 & 2 & 24 & 12 & 26 & 6 & 28 & 14 & 30 & 1
  \end{tabular}
  \caption{Fenwick $\leftrightarrow$ binary indexing for $n = 4$}
  \label{tab:indexing}
\end{table}

Staring at this table, a few patterns stand out.  First, all the
numbers on the bottom row are even except for the final $1$---which
makes sense, since other than the root only left children are
included, which have a binary index twice that of their parent.
Second, we can see the even numbers $16 \dots 30$, in order, in all
the odd positions.  These are exactly the leaves of the tree, and
indeed, we can see that every other node in the Fenwick array will be
a leaf from the original tree.  Alternating with these, in the even
positions, are the numbers $8\; 4\; 10\; 2 \dots$, which correspond to
all the non-leaf nodes; but these would be exactly the sequence of
binary indices in a tree with $n = 3$.

These observations lead to the recurrence shown in \pref{fig:seqrec}
for the sequence $b_n$ of binary indices stored in the Fenwick array
for trees of size $2^n$.

\begin{figure}

%if false
\begin{code}

pow :: Int -> Int -> Int
pow = (^)

\end{code}
%endif

\begin{code}

interleave :: [a] -> [a] -> [a]
[] `interleave` _ = []
(x : xs) `interleave` ys = x : (ys `interleave` xs)

b :: Int -> [Int]
b 0 = [1]
b n = [pow 2 n, pow 2 n + 2 .. pow 2 (n+1) - 2] `interleave` b (n-1)

\end{code}

\caption{Recurrence for sequence of binary indices in a Fenwick
    array}
  \label{fig:seqrec}
\end{figure}

We can check that this does in fact reproduce the observed sequence
for $n = 4$:

\begin{verbatim}
ghci> b 4
[16,8,18,4,20,10,22,2,24,12,26,6,28,14,30,1]
\end{verbatim}

Let |s ! k| denote the $k$th item in the list $s$ (counting from 1),
as defined in \pref{fig:index-interleave}.  The same figure also lists
two easy lemmas about the interaction between indexing and
interleaving, namely, |(xs `interleave` ys) ! (2*k) = ys ! k|, and
|(xs `interleave` ys) ! (2*k - 1) = xs!k|.  With these in hand, we can
define the Fenwick $\to$ binary index conversion function |f2b n k = b
n ! k|, and then simplify it as follows.

\begin{figure}
  \centering
\begin{code}

(a : _) ! 1 = a
(_ : as) ! k = as ! (k-1)

\end{code}

\begin{spec}
(xs `interleave` ys) ! (2*k)      = ys ! k
(xs `interleave` ys) ! (2*k - 1)  = xs ! k
\end{spec}

\begin{code}

f2b n k = b n ! k        -- $1 \leq k \leq 2^n$

\end{code}

  \caption{Indexing and interleaving}
  \label{fig:index-interleave}
\end{figure}

\begin{sproof}
  \stmt{|f2b n (2*k)|}
  \reason{=}{Definition of |f2b|}
  \stmt{|b n ! (2 * k)|}
  \reason{=}{Definition of |b|}
  \stmt{|([pow 2 n, pow 2 n + 2 .. pow 2 (n+1) - 2] `interleave` b (n-1)) ! (2 * k)|}
  \reason{=}{|`interleave`-!| lemma}
  \stmt{b (n-1) ! k}
  \reason{=}{Definition of |f2b|}
  \stmt{|f2b (n-1) k|}
\end{sproof}

OTOH

\begin{sproof}
  \stmt{|f2b n (2*k-1)|}
  \reason{=}{Definition of |f2b|}
  \stmt{|b n ! (2 * k-1)|}
  \reason{=}{Definition of |b|}
  \stmt{|([pow 2 n, pow 2 n + 2 .. pow 2 (n+1) - 2] `interleave` b (n-1)) ! (2 * k-1)|}
  \reason{=}{|`interleave`-!| lemma}
  \stmt{|([pow 2 n, pow 2 n + 2 .. pow 2 (n+1) - 2] ! k|}
  \reason{=}{XXX}
  \stmt{|pow 2 n + 2*(k-1)|}
\end{sproof}

Thus we have
\[ |f2b n j| = \begin{cases} |f2b (n-1) (j/2)| & j \text{ even} \\ 2^n
    + j - 1 & j \text{ odd} \end{cases} \] Note that when $n = 0$ we
must have $j = 1$, and hence $|f2b 0 1| = 2^0 + 1 - 1 = 1$, as
required, so this definition is valid for all $n \geq 0$.  Now factor
$j$ uniquely as $2^a \cdot b$ where $b$ is odd.  Then by induction it
is easy to see that
\[ |f2b n (pow 2 a * b) = f2b (n - a) b| = 2^{n-a} + b - 1. \]

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  % This material is based upon work supported by the
  % \grantsponsor{GS100000001}{National Science
  %   Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  % No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  % No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  % conclusions or recommendations expressed in this material are those
  % of the author and do not necessarily reflect the views of the
  % National Science Foundation.
\end{acks}


% Bibliography
\bibliography{fenwick}


%% Appendix
% \appendix
% \section{Appendix}

% Text of appendix \ldots

\end{document}
