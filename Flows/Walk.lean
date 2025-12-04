/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Mathlib



open Digraph

def Digraph.outNeighborSet (G : Digraph V) (v : V) : Set V :=
  {w : V | G.Adj v w}

def Digraph.inNeighborSet (G : Digraph V) (v : V) : Set V :=
  {w : V | G.Adj w v}


structure Digraph.Walk (G : Digraph V) where
  support : List V
  chainAdj : List.IsChain G.Adj support

def Digraph.Walk.startsAt {G : Digraph V} (W : G.Walk)
  (h : W.support ≠ []) : V :=
  W.support.head h

def Digraph.Walk.endsAt {G : Digraph V} (W : G.Walk)
  (h : W.support ≠ []) : V :=
  W.support.getLast h

def IsCircuit {G : Digraph V} (W : G.Walk) : Prop :=
  W.support.length > 2 ∧ W.support.head = W.support.getLast


structure Digraph.Path (G : Digraph V) extends Walk G where
  nodup : List.Nodup support

def IsCycle (G : Digraph V) (P : G.Path) : Prop :=
  IsCircuit P.toWalk

def Digraph.Walk.Length {G : Digraph V} (W : G.Walk) :=
  W.support.length

def Digraph.Walk.Single {G : Digraph V} (u : V) : G.Walk where
  support := [u]
  chainAdj := by
    apply List.IsChain.singleton

def Digraph.Path.Single {G : Digraph V} (u : V) : G.Path where
  support := [u]
  chainAdj := by
    apply List.IsChain.singleton
  nodup := by
    simp_all

def Digraph.Walk.cons {G : Digraph V}
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

def Digraph.Walk.tail {G : Digraph V} (W : G.Walk) : G.Walk where
  support := W.support.tail
  chainAdj := by
    apply List.IsChain.tail
    exact W.chainAdj

def Digraph.Path.cons {G : Digraph V}
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

def Digraph.Walk.edgeList {G : Digraph V} (W : G.Walk) : List (V × V) :=
  match hW : W.support with
  | []
  | [_] => []
  | v :: w :: _ =>
      (v,w) :: edgeList W.tail
  termination_by W.support.length
  decreasing_by
    simp [Walk.tail, hW]

lemma isWalkEdge_vert_support_left (G : Digraph V)
  (W : G.Walk) (x y : V) (hxy : (x, y) ∈ W.edgeList)
  : x ∈ W.support := by
  revert hxy
  fun_induction Digraph.Walk.edgeList
  · expose_names
    simp_all
  · expose_names
    grind
  · expose_names
    simp_all
    rintro (⟨x_eq_v, y_eq_w⟩ | hrest)
    · left
      assumption
    · right
      simp_all
      have : x_1.tail.support = w :: tail := by
        simp_all [Digraph.Walk.tail]
      rw [this] at ih1
      simp at ih1
      assumption

lemma isWalkEdge_vert_support_right (G : Digraph V)
  (W : G.Walk) (x y : V) (hxy : (x, y) ∈ W.edgeList)
  : y ∈ W.support := by
  revert hxy
  fun_induction Digraph.Walk.edgeList
  · expose_names
    simp_all
  · expose_names
    grind
  · expose_names
    simp_all
    rintro (⟨x_eq_v, y_eq_w⟩ | hrest)
    · right; left
      assumption
    · right
      simp_all
      have : x_1.tail.support = w :: tail := by
        simp_all [Digraph.Walk.tail]
      rw [this] at ih1
      simp at ih1
      assumption



abbrev Digraph.Walk.isWalkEdge {G : Digraph V}
  (W : G.Walk) (x y : V) :=
    (x,y) ∈ W.edgeList

abbrev Digraph.Path.isPathEdge {G : Digraph V}
  (P : G.Path) (x y : V) :=
    (x,y) ∈ P.edgeList

abbrev Digraph.PathFromTo {G : Digraph V} (P : G.Path) (h : P.support ≠ []) (s t : V) :=
  P.startsAt h = s  ∧ P.endsAt h = t
