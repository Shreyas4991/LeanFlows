import Mathlib


open Digraph

structure WDigraph V extends Digraph V where
  weight : V → V → EReal
  non_adj_zero : ∀ v w : V, ¬ Adj v w → weight v w = ⊤
  triangle_inequality : ∀ v w x : V, Adj v w → Adj w x → Adj v x →
    weight v x ≤ weight v w + weight w x


structure BellmanFordDataStructure (V : Type u) where
  source : V
  dist : V → EReal
  dist_source : dist source = 0



variable (V : Type u) [DecidableEq V]

def initialise
  (source : V) : BellmanFordDataStructure V where
    source := source
    dist v := if v = source then 0 else ⊤
    dist_source := by
      simp


noncomputable def relaxOneEdge (W : WDigraph V)
  (DS : BellmanFordDataStructure V)
  (v w : V):
  BellmanFordDataStructure V where
  source := DS.source
  dist x :=
    if w = x ∧ w ≠ DS.source ∧ DS.dist v  + W.weight v w ≤ DS.dist w
    then DS.dist v  + W.weight v w
    else DS.dist x

  dist_source := by
    rw [DS.dist_source]
    split
    case isFalse => rfl
    case isTrue h =>
      exfalso
      simp at h
      apply h.right.left
      exact h.left

noncomputable def relaxEdge (W : WDigraph V)
  (DS : BellmanFordDataStructure V)
  (edges : List <| V × V) : BellmanFordDataStructure V :=
  match edges with
  | [] => DS
  | (v,w) :: rest => relaxEdge W (relaxOneEdge V W DS v w) rest


noncomputable def iterate (n : ℕ) (f : α → α) (init : α) : α :=
  match n with
  | 0 => init
  | m + 1 => iterate m f (f init)

abbrev isEdgeList (G : Digraph V) (eL : List <| V × V) :=
  ∀ v w : V, G.Adj v w ↔ (v,w) ∈ eL

noncomputable def BellmanFord
  [Fintype V]
  (W : WDigraph V)
  (eList : List <| V × V)
  (_ : isEdgeList V W.toDigraph eList)
  :=
  iterate (Fintype.card V) (fun ds => relaxEdge V W ds eList)
