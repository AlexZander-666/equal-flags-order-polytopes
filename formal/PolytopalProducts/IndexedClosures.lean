import PolytopalProducts.ActualGraphData
import PolytopalProducts.ClassDirections

/-! The packed reach computation presents the exact geometric face and affine dimension. -/

noncomputable section

namespace PolytopalProducts.Codim3

open PolytopalProducts.OrderFaces
open scoped Classical

variable {n m : ℕ} {V : Type*} [PartialOrder V] {g : GraphData n m}

/-- The chosen indices as a set of actual augmented Hasse covers. -/
def actualSeed (model : GraphRealization V g) (s : List (Fin m)) : Finset (Arc V) :=
  s.toFinset.map model.arc.toEmbedding

theorem arrow_add (r : Vector Nat n) (p : Fin n × Fin n) (a b : Fin n) :
    arrow (add r p) a b = true ↔ arrow r a b = true ∨
      (arrow r a p.2 = true ∧ arrow r p.1 b = true) := by
  unfold arrow add
  rw [Vector.getElem_ofFn]
  by_cases h : r[a.val].testBit p.2.val = true
  · simp [h]
  · have hf : r[a.val].testBit p.2.val = false := Bool.eq_false_of_not_eq_true h
    simp [hf]

private theorem closure_eq_of_mem {W : Type*} (r : W → W → Prop)
    (ht : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hr : ∀ a, r a a)
    {s t : List (W × W)} (h : ∀ e, e ∈ s ↔ e ∈ t) (a b : W) :
    closure r s a b ↔ closure r t a b := by
  constructor
  · exact closure_le (closure_trans ht t) s
      (fun _ _ ↦ closure_contains t) (fun x y hxy ↦ closure_reverse hr ((h (x, y)).mp hxy))
  · exact closure_le (closure_trans ht s) t
      (fun _ _ ↦ closure_contains s) (fun x y hxy ↦ closure_reverse hr ((h (x, y)).mpr hxy))

theorem close_matches (model : GraphRealization V g) (s : List (Fin m)) (a b : Fin n) :
    arrow (close g s) a b = true ↔ reach (actualSeed model s) (model.point a) (model.point b) := by
  let endpoints (e : Fin m) : Pinned V × Pinned V :=
    (model.point g.arcs[e.val].1, model.point g.arcs[e.val].2)
  have hl (t : List (Fin m)) (x y : Fin n) :
      arrow (close g t) x y = true ↔
        closure (· ≤ ·) (t.map endpoints) (model.point x) (model.point y) := by
    induction t generalizing x y with
    | nil => exact model.order x y
    | cons e t ih =>
      change arrow (add (close g t) g.arcs[e.val]) x y = true ↔ _
      rw [arrow_add, ih, ih, ih]
      rfl
  refine (hl s a b).trans (closure_eq_of_mem (· ≤ ·) (fun _ _ _ ↦ le_trans)
    (fun _ ↦ le_rfl) ?_ _ _)
  intro e
  constructor
  · rintro he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    apply List.mem_map.mpr
    refine ⟨model.arc i, Finset.mem_toList.mpr ?_, model.endpoints i⟩
    exact Finset.mem_map.mpr ⟨i, List.mem_toFinset.mpr hi, rfl⟩
  · rintro he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp hc)
    exact List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, (model.endpoints i).symm⟩

private theorem add_no_high_bits {r : Vector Nat n} (p : Fin n × Fin n)
    (hr : ∀ i : Fin n, ∀ j ≥ n, r[i.val].testBit j = false) :
    ∀ i : Fin n, ∀ j ≥ n, (add r p)[i.val].testBit j = false := by
  intro i j hj
  unfold add
  rw [Vector.getElem_ofFn]
  split
  · rw [Nat.testBit_lor, hr _ j hj, hr _ j hj]
    rfl
  · exact hr _ j hj

theorem close_no_high_bits (model : GraphRealization V g) (s : List (Fin m)) :
    ∀ i : Fin n, ∀ j ≥ n, (close g s)[i.val].testBit j = false := by
  induction s with
  | nil =>
    intro i j hj
    exact Nat.testBit_lt_two_pow ((model.bounded i).trans_le (Nat.pow_le_pow_right (by decide) hj))
  | cons e t ih => exact add_no_high_bits g.arcs[e.val] ih

theorem same_row_iff (model : GraphRealization V g) (s : List (Fin m)) (i j : Fin n) :
    (close g s)[i.val] = (close g s)[j.val] ↔
      sameClass (actualSeed model s) (model.point i) (model.point j) := by
  set r := close g s
  have hself (i : Fin n) : arrow r i i = true :=
    (close_matches model s i i).mpr (reach_of_le _ le_rfl)
  constructor
  · intro h
    have he (a : Fin n) : arrow r i a = arrow r j a := by simp only [arrow, h]
    exact ⟨(close_matches model s i j).mp ((he j).trans (hself j)),
      (close_matches model s j i).mp ((he i).symm.trans (hself i))⟩
  · rintro ⟨hij, hji⟩
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · apply Bool.eq_iff_iff.mpr
      exact ((close_matches model s i ⟨k, hk⟩).trans
        ⟨fun hr ↦ reach_trans _ hji hr, fun hr ↦ reach_trans _ hij hr⟩).trans
        (close_matches model s j ⟨k, hk⟩).symm
    · exact (close_no_high_bits model s i k (le_of_not_gt hk)).trans
        (close_no_high_bits model s j k (le_of_not_gt hk)).symm

variable [Fintype V]

theorem nonempty_iff_accepted_pins (model : GraphRealization V g) (s : List (Fin m)) :
    (seededFace (actualSeed model s)).Nonempty ↔ arrow (close g s) g.high g.low = false := by
  rw [seededFace_nonempty_iff, ← model.high, ← model.low,
    ← close_matches model s g.high g.low]
  exact Bool.eq_false_iff.symm

def rowSet (r : Vector Nat n) : Finset ℕ := r.toList.toFinset

private def encodeRow (model : GraphRealization V g) (r : Vector Nat n) (p : Pinned V) :
    rowSet r :=
  ⟨r[(model.point.symm p).val], by
    rw [rowSet, List.mem_toFinset, Vector.mem_toList_iff]
    exact Vector.mem_iff_getElem.mpr ⟨_, (model.point.symm p).isLt, rfl⟩⟩

omit [Fintype V] in
private theorem encodeRow_surjective (model : GraphRealization V g) (r : Vector Nat n) :
    Function.Surjective (encodeRow model r) := by
  rintro ⟨k, hk⟩
  rw [rowSet, List.mem_toFinset, Vector.mem_toList_iff] at hk
  obtain ⟨j, hj, hkj⟩ := Vector.mem_iff_getElem.mp hk
  refine ⟨model.point ⟨j, hj⟩, Subtype.ext ?_⟩
  change r[(model.point.symm (model.point ⟨j, hj⟩)).val] = k
  simpa using hkj

theorem finrank_eq_rows (model : GraphRealization V g) (s : List (Fin m))
    (hn : (seededFace (actualSeed model s)).Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (seededFace (actualSeed model s))) =
      (rowSet (close g s)).card - 2 := by
  rw [← Fintype.card_coe]
  refine finrank_seededFace (actualSeed model s) (encodeRow model (close g s))
    (encodeRow_surjective model _) ?_ hn
  intro a b
  rw [Subtype.ext_iff]
  change ((close g s)[(model.point.symm a).val] =
    (close g s)[(model.point.symm b).val]) ↔ _
  simpa using same_row_iff model s (model.point.symm a) (model.point.symm b)

end PolytopalProducts.Codim3

