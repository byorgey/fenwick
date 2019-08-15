{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module FenwickDiagrams where

import           Diagrams.Prelude
import           SegTree

sampleArray :: [Sum Int]
sampleArray = map (Sum . negate) [0, -4, -1, -1, -1, 2, -6, 4, 1, -6, 2, -5, 6, -2, -8, -3]

drawSegTree :: _ => SegmentTree (Diagram b) -> Diagram b
drawSegTree t = drawNodes t <> drawEdges t

drawNodes :: _ => SegmentTree (Diagram b) -> Diagram b
drawNodes (Leaf d _) = d
drawNodes (Branch d i j l r) = vsep 1 [d, (drawNodes l ||| drawNodes r) # centerX]

drawEdges :: _ => SegmentTree (Diagram b) -> Diagram b
drawEdges t = mempty
