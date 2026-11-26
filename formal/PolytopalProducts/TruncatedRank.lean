import PolytopalProducts.TruncatedFlags
import Mathlib.Order.Hom.WithTopBot

namespace PolytopalProducts.Truncated
open PolytopalProducts.OrderFaces PolytopalProducts.Codim3
/-- Distance in consecutive covers from the least element. -/
def AtLevel {X : Type*} [PartialOrder X] [OrderBot X] : ℕ → X → Prop
  | 0, x => x = ⊥
  | r+1, x => ∃ y, AtLevel r y ∧ y ⋖ x

def rankConditions (g : GraphData 30 64) : Prop :=
  (∀ i, augmentedRank i = 0 ↔ i = g.low) ∧
  (∀ i, i ≠ g.low → ∃ e : Fin 64, g.arcs[e.val].2 = i)

theorem rank_data : rankConditions graph ∧ rankConditions hexGraph := by
  unfold rankConditions
  decide +kernel

theorem rank_iff {V : Type*} [PartialOrder V] {g : GraphData 30 64}
    (m : GraphRealization V g) (graded : raisesRank g) (hdata : rankConditions g)
    (r : ℕ) (i : Fin 30) : AtLevel r (m.point i) ↔ augmentedRank i = r := by
  induction r generalizing i with
  | zero =>
    change m.point i = ⊥ ↔ _
    rw [← m.low, Equiv.apply_eq_iff_eq]
    exact (hdata.1 i).symm
  | succ r ih =>
    constructor
    · rintro ⟨y,hy,cy⟩
      obtain ⟨j,rfl⟩ := m.point.surjective y
      have h := geometric_cover_raises_rank m graded cy
      simpa only [Equiv.symm_apply_apply, (ih j).mp hy] using h
    · intro a
      have ne : i ≠ g.low := fun h ↦ by have t := (hdata.1 i).mpr h; omega
      obtain ⟨e,he⟩ := hdata.2 i ne
      let j := g.arcs[e.val].1
      have cov := (m.arc e).property
      rw [m.endpoints e,he] at cov
      refine ⟨m.point j,(ih j).mpr ?_,cov⟩
      have step := graded e
      rw [he,a] at step
      exact Nat.add_right_cancel step.symm

theorem level_order_iso {X Y : Type*} [PartialOrder X] [OrderBot X] [PartialOrder Y] [OrderBot Y]
    (e : X ≃o Y) (r : ℕ) (x : X) : AtLevel r (e x) ↔ AtLevel r x := by
  induction r generalizing x with
  | zero => change e x = ⊥ ↔ x = ⊥; rw [← e.map_bot, e.injective.eq_iff]
  | succ r ih =>
    constructor
    · rintro ⟨y,h,c⟩
      obtain ⟨z,rfl⟩ := e.surjective y
      exact ⟨z,(ih z).mp h,(apply_covBy_apply_iff e).mp c⟩
    · rintro ⟨z,h,c⟩
      exact ⟨e z,(ih z).mpr h,(apply_covBy_apply_iff e).mpr c⟩

#print axioms rank_iff
#print axioms level_order_iso
end PolytopalProducts.Truncated

