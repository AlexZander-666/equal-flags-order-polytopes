import Polygon.Tally
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Transfer matrices for cyclic labels valued in an arbitrary finite poset. -/

noncomputable section
open scoped BigOperators

namespace PolytopalProducts

/-- The ordinary cycle trace, with a general finite state type. -/
theorem trace_pow_cycle {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J ℕ) (k : ℕ) :
    (M ^ (k + 1)).trace = ∑ x : Fin (k + 1) → J, ∏ i, M (x i) (x (i + 1)) := by
  let e := Fintype.equivFin J
  let r := Matrix.reindexRingEquiv ℕ e
  have ht (A : Matrix J J ℕ) : A.trace = (r A).trace := by
    unfold Matrix.trace
    exact Fintype.sum_equiv e _ _ (fun i ↦ by simp [r, Matrix.diag_apply])
  rw [ht, map_pow, Polygon.Tally.trace_pow_cycle]
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) e.symm)
  intro x
  rfl

variable {J : Type*} [Fintype J] [Preorder J] [DecidableLE J]

/-- The order indicator on the state poset. -/
def zeta : Matrix J J ℕ := fun x y ↦ if x ≤ y then 1 else 0

/-- Each entry counts possible labels of an edge with the indicated ends. -/
def gram : Matrix J J ℕ := zeta * (zeta : Matrix J J ℕ).transpose

theorem gram_apply (a b : J) : gram a b = Fintype.card {y : J // a ≤ y ∧ b ≤ y} := by
  rw [gram, Matrix.mul_apply, Fintype.card_subtype]
  simp only [zeta, Matrix.transpose_apply]
  calc
    _ = ∑ j : J, if a ≤ j ∧ b ≤ j then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases ha : a ≤ j <;> by_cases hb : b ≤ j <;> simp [ha, hb]
    _ = _ := by simpa only [Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun j : J ↦ a ≤ j ∧ b ≤ j) Finset.univ)

/-- Vertex labels of a cyclic crown with a separately chosen upper label on each edge. -/
abbrev CrownLabeling (J : Type*) [Preorder J] (k : ℕ) :=
  Σ v : Fin (k + 1) → J, ∀ i : Fin (k + 1), {e : J // v i ≤ e ∧ v (i + 1) ≤ e}

theorem card_crownLabeling [DecidableEq J] (k : ℕ) :
    Fintype.card (CrownLabeling J k) = ((gram : Matrix J J ℕ) ^ (k + 1)).trace := by
  rw [trace_pow_cycle, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_pi]
  simp only [gram_apply]

end PolytopalProducts

