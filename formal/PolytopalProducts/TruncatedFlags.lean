import PolytopalProducts.TruncatedGraph

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3 PolytopalProducts.OrderFaces
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- Ranks of the twice augmented face poset, including its two artificial pins. -/
def augmentedRank (i : Fin 30) : ℕ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val ≤ 8 then 2
  else if i.val ≤ 20 then 3 else if i.val ≤ 27 then 4 else if i.val = 28 then 5 else 6

def raisesRank (g : GraphData 30 64) : Prop :=
  ∀ e : Fin 64, augmentedRank g.arcs[e.val].2 = augmentedRank g.arcs[e.val].1 + 1

theorem both_raise_rank : raisesRank graph ∧ raisesRank hexGraph := by
  unfold raisesRank
  decide +kernel

theorem geometric_cover_raises_rank {V : Type*} [PartialOrder V] {g : GraphData 30 64}
    (m : GraphRealization V g) (graded : raisesRank g) {u v : Pinned V} (h : u ⋖ v) :
    augmentedRank (m.point.symm v) = augmentedRank (m.point.symm u) + 1 := by
  obtain ⟨e,he⟩ := m.arc.surjective ⟨(u,v),h⟩
  have eq := (m.endpoints e).symm.trans (congrArg Subtype.val he)
  have hu := congrArg Prod.fst eq
  have hv := congrArg Prod.snd eq
  change m.point _ = u at hu
  change m.point _ = v at hv
  rw [← hu,← hv,m.point.symm_apply_apply,m.point.symm_apply_apply]
  exact graded e

/-- Each selected rank supplies exactly one index. An omitted rank has one empty choice. -/
def choices (selected : Bool) (rank : Nat) : List (Option (Fin 30)) :=
  if selected then ((List.finRange 30).filter (fun i ↦ augmentedRank i == rank)).map some else [none]

def orderedPair (g : GraphData 30 64) : Option (Fin 30) → Option (Fin 30) → Bool
  | some i,some j => arrow g.order i j
  | _,_ => true

def flagCount (g : GraphData 30 64) (v e f : Bool) : Nat :=
  ((choices v 2).flatMap fun a ↦ (choices e 3).flatMap fun b ↦
    (choices f 4).filter fun c ↦ orderedPair g a b && orderedPair g a c && orderedPair g b c).length

def flagVector (g : GraphData 30 64) : Vector Nat 8 :=
  #v[flagCount g false false false,flagCount g true false false,flagCount g false true false,
     flagCount g false false true,flagCount g true true false,flagCount g true false true,
     flagCount g false true true,flagCount g true true true]

theorem complete_flag_values :
    flagVector graph = #v[1,7,12,7,24,24,24,48] ∧ flagVector hexGraph = #v[1,7,12,7,24,24,24,48] := by
  decide +kernel

#print axioms geometric_cover_raises_rank
#print axioms complete_flag_values
end PolytopalProducts.Truncated

