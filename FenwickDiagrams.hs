{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module FenwickDiagrams where

import           Diagrams.Prelude
import           SegTree

data NodeType = LeafNode | InternalNode
type SegNode a = (NodeType, a)

sampleArray :: [Sum Int]
sampleArray = map (Sum . negate) [0, -4, -1, -1, -1, 2, -6, 4, 1, -6, 2, -5, 6, -2, -8, -3]

drawSegTree :: _ =>
  -- | Node drawing function: takes value of node (marked as leaf or
  --   internal) leaves and Right for internal nodes, along with
  --   interval endpoints the node covers
  (SegNode a -> Int -> Int -> Diagram b) ->

  -- | The segment tree to draw
  SegmentTree a ->
  Diagram b

drawSegTree f (Leaf a i)         = f (LeafNode, a) i i
drawSegTree f (Branch a i j l r) = localize $ vsep 1
  [ f (InternalNode, a) i j # named "root"
  , ((drawSegTree f l # named "left") ||| (drawSegTree f r # named "right")) # centerX
  ]
  # withNames ["root", "left", "right"]
  ( \[x, l, r] ->
      applyAll [ beneath (location x ~~ location l), beneath (location x ~~ location r) ]
  )

leafWidth :: Double
leafWidth = 1.2

-- XXX need to generalize the below node-drawing code.
-- Want to be able to draw

drawNode :: _ => SegNode a -> Int -> Int -> Diagram b
drawNode (LeafNode, n)     _ _ = drawNodeWith (square 1 <> strutX leafWidth) n
drawNode (InternalNode, n) i j = mconcat
  [ drawNodeWith (circle 0.5) n
  , hrule ((fromIntegral j - fromIntegral i) * leafWidth + 0.5)
    # lw veryThick
    # lc grey
    # lineCap LineCapRound
  ]

-- (j - i + 1) * leafWidth - (leafWidth - 1)
-- = (j - i) * leafWidth + 1
--
-- then subtract extra 0.5 just to leave a bit more gap
--
-- X X X

drawNodeWith :: _ => Diagram b -> a -> Diagram b
drawNodeWith d n = mconcat
  [ text (show n) # fontSizeL 0.6
  , d # fc white
  ]
