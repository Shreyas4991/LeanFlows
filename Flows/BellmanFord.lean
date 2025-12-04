import Mathlib
import Flows.Walk

open Digraph

structure WDigraph V extends Digraph V where
  weight : V → V → EReal
  non_adj_zero : ∀ v w : V, ¬ Adj v w → weight v w = ⊤
  triangle_inequality : ∀ v w x : V, Adj v w → Adj w x → Adj v x →
    weight v x ≤ weight v w + weight w x

@[ext]
structure WDigraph.Walk (G : WDigraph V) where
  support : List V
  chainAdj : List.IsChain G.Adj support

@[ext]
structure WDigraph.Path (G : WDigraph V) extends Walk G where
  nodup : List.Nodup support

def WDigraph.Walk.length {G : WDigraph V} (W : G.Walk):= W.support.length

def WDigraph.Path.length {G : WDigraph V} (P : G.Path):= P.support.length

def WDigraph.Walk.startsAt {G : WDigraph V} (W : G.Walk)
  (h : W.support ≠ []) : V :=
  W.support.head h

def WDigraph.Walk.endsAt {G : WDigraph V} (W : G.Walk)
  (h : W.support ≠ []) : V :=
  W.support.getLast h

def WDigraph.Path.startsAt {G : WDigraph V} (P : G.Path)
  (h : P.support ≠ []) : V :=
  P.support.head h

def WDigraph.Path.endsAt {G : WDigraph V} (P : G.Path)
  (h : P.support ≠ []) : V :=
  P.support.getLast h

def WDigraph.Walk.IsCircuit {G : WDigraph V} (W : G.Walk) : Prop :=
  W.support.length > 2 ∧ W.support.head = W.support.getLast


def WDigraph.Walk.IsCycle (G : WDigraph V) (P : G.Path) : Prop :=
  P.toWalk.IsCircuit

def WDigraph.Walk.Length {G : WDigraph V} (W : G.Walk) :=
  W.support.length

def WDigraph.Walk.Single {G : WDigraph V} (u : V) : G.Walk where
  support := [u]
  chainAdj := by
    apply List.IsChain.singleton

def WDigraph.Path.Single {G : WDigraph V} (u : V) : G.Path where
  support := [u]
  chainAdj := by
    apply List.IsChain.singleton
  nodup := by
    simp_all

def WDigraph.Walk.cons {G : WDigraph V}
  (u : V) (W : G.Walk)
  (hAdj : (hnempty : W.support ≠ [])
    → G.Adj u (W.support.head hnempty))
  : G.Walk where
  support :=
    match W.support with
    | [] => [u]
    | v :: vs => u :: v :: vs
  chainAdj := by
    have hchainW := W.chainAdj
    cases hW : W.support with
    | nil =>
        simp
    | cons head tail =>
        simp
        rw [hW] at hchainW hAdj
        constructor
        · simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head_cons, forall_const]
        · assumption

def WDigraph.Walk.tail {G : WDigraph V} (W : G.Walk) : G.Walk where
  support := W.support.tail
  chainAdj := by
    apply List.IsChain.tail
    exact W.chainAdj

def WDigraph.Path.cons {G : WDigraph V}
  (u : V) (W : G.Path)
  (hnewvertex : List.Nodup (u :: W.support))
  (hAdj : (hnempty : W.support ≠ [])
    → G.Adj u (W.support.head hnempty))
  : G.Path where
  support :=
    match W.support with
    | [] => [u]
    | v :: vs => u :: v :: vs
  chainAdj := by
    have hchainW := W.chainAdj
    cases hW : W.support with
    | nil =>
        simp
    | cons head tail =>
        simp
        rw [hW] at hchainW hAdj
        constructor
        · simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.head_cons, forall_const]
        · assumption
  nodup := by
    induction hW : W.support with
    | nil =>
        simp
    | cons head tail ih =>
        simp_all

def WDigraph.Walk.edgeList {G : WDigraph V} (W : G.Walk) : List (V × V) :=
  match hW : W.support with
  | []
  | [_] => []
  | v :: w :: _ =>
      (v,w) :: edgeList W.tail
  termination_by W.support.length
  decreasing_by
    simp [Walk.tail, hW]

lemma WDigraph.Walk.length_edge_length {G : WDigraph V}
  (W : G.Walk) (hW : W.support ≠ []) : W.length = W.edgeList.length + 1 := by
  fun_induction Walk.edgeList
  · rename_i hW'
    exfalso
    simp at hW
    apply hW hW'
  · rename_i x' head' hW'
    simp_all [Walk.length]
  · expose_names
    simp_all
    have : x.tail.support ≠ [] := by
      simp [hW_1, Walk.tail]
    have s₂ : x.length = x.tail.length + 1 := by
      unfold Walk.tail
      unfold Walk.length
      zify
      simp_all
    specialize ih1 this
    rw [s₂, ih1]


lemma WDigraph.Walk.nonEmptyEdgeList_nonEmptySupport
  {G : WDigraph V}
  (W : G.Walk)
  (hWEdgeList : W.edgeList ≠ []) : W.support ≠ [] := by
  fun_induction edgeList <;> simp_all



def WDigraph.Walk.wlength {G : WDigraph V} (W : G.Walk) : EReal :=
  match hW : W.edgeList with
  | [] => 0
  | (v,w) :: _ => G.weight v w + wlength (W.tail)
  termination_by W.length
  decreasing_by
    simp [WDigraph.Walk.tail, Walk.length]
    have W_non_empty_support : W.support ≠ [] := by
      simp_all [nonEmptyEdgeList_nonEmptySupport]
    exact List.length_pos_iff.mpr W_non_empty_support


def WDigraph.Path.wlength {G : WDigraph V} (P : G.Path) : EReal :=
  P.toWalk.wlength

lemma emptyWalksUnique {G : WDigraph V}
  (W₁ W₂ : G.Walk) (hW₁ : W₁.support = [])
  (hW₂ : W₂.support = []) : W₁ = W₂ := by
  ext index elem
  constructor
  all_goals
    intro h
    simp_all

def WDigraph.pathsFromSource (G : WDigraph V) (s : V)
  : Set (G.Path) := fun path =>
    (h : path.support ≠ []) → path.startsAt h = s


def WDigraph.walksFromSource (G : WDigraph V) (s : V)
  : Set (G.Walk) := fun walk =>
    (h : walk.support ≠ []) → walk.startsAt h = s

def WDigraph.pathsToSink (G : WDigraph V) (t : V) : Set (G.Path) :=
  fun path => (h : path.support ≠ []) → path.endsAt h = t

def WDigraph.walksToSink (G : WDigraph V) (t : V) : Set (G.Walk) :=
  fun walk => (h : walk.support ≠ []) → walk.endsAt h = t

def WDigraph.stPaths (G : WDigraph V) (s t : V) : Set (G.Path) :=
  fun path => (h : path.support ≠ []) → path.startsAt h = s ∧ path.endsAt h = t

def WDigraph.stWalks (G : WDigraph V) (s t : V) : Set (G.Walk) :=
  fun walk => (h : walk.support ≠ []) → walk.startsAt h = s ∧ walk.endsAt h = t

#print InfSet
def shortestPaths (G : WDigraph V) (source : V) :=
  sInf (G.pathsFromSource source)

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
  (v w : V) :
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
  (source : V)
  (eList : List <| V × V)
  (_ : isEdgeList V W.toDigraph eList)
  :=  iterate
        (Fintype.card V)
        (fun ds => relaxEdge V W ds eList)
        (initialise V source)
