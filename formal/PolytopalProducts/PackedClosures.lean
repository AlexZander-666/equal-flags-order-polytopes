import Mathlib

/-! Executable computation for rank-three tight closures, using packed rows. -/

namespace PolytopalProducts.Codim3

/-- An augmented order, its Hasse arcs, and its two distinguished indices. -/
structure GraphData (n m : ℕ) where
  order : Vector Nat n
  arcs : Vector (Fin n × Fin n) m
  low : Fin n
  high : Fin n

def add (r : Vector Nat n) (p : Fin n × Fin n) : Vector Nat n :=
  Vector.ofFn fun i ↦
    if r[i.val].testBit p.2.val then r[i.val] ||| r[p.1.val] else r[i.val]

def arrow (r : Vector Nat n) (i j : Fin n) : Bool := r[i.val].testBit j.val

def close (g : GraphData n m) (s : List (Fin m)) : Vector Nat n :=
  s.foldr (fun e r ↦ add r g.arcs[e.val]) g.order

def dimensionOK (g : GraphData n m) (r : Vector Nat n) (d : ℕ) : Bool :=
  !(arrow r g.high g.low) && r.toList.eraseDups.length == d + 2

def tight (g : GraphData n m) (r : Vector Nat n) : List (Fin m) :=
  (List.finRange m).filter fun e ↦
    arrow r g.arcs[e.val].2 g.arcs[e.val].1

def canonical (g : GraphData n m) (r : Vector Nat n) : List (Fin m) :=
  (tight g r).take 3

def orderedTriples (m : ℕ) (i : Fin m) : List (List (Fin m)) :=
  (List.finRange m).flatMap fun j ↦
    if i < j then (List.finRange m).filterMap fun k ↦
      if j < k then some [i, j, k] else none
    else []

def rowCount (g : GraphData n m) (d : ℕ) (i : Fin m) : ℕ :=
  (orderedTriples m i).countP fun s ↦
    let r := close g s
    dimensionOK g r d && canonical g r == s

def rowFailures (g : GraphData n m) (d : ℕ) (i : Fin m) : ℕ :=
  (orderedTriples m i).countP fun s ↦
    let r := close g s
    if dimensionOK g r d then
      let c := canonical g r
      let r' := close g c
      !(c.length == 3 && dimensionOK g r' d && tight g r == tight g r')
    else false

end PolytopalProducts.Codim3

