import PolytopalProducts.FaceModels
import Polygon.GeneralRealization

/-! The actual exposed-face order of a Cartesian product of convex bodies. -/

noncomputable section
open Set ContinuousLinearMap

namespace PolytopalProducts.Geometry

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The exposed faces, including the empty face and the full body, ordered by inclusion. -/
abbrev ExposedFace (A : Set E) := {S : Set E // IsExposed ℝ A S}

/-- The nonempty members of the exposed-face order. -/
abbrev NonemptyExposed (A : Set E) := {S : ExposedFace A // S.val.Nonempty}

/-- A functional on a product exposes the product of the maxima of its restrictions. -/
theorem toExposed_prod (l : StrongDual ℝ (E × F)) (A : Set E) (B : Set F) :
    l.toExposed (A ×ˢ B) =
      (l.comp (inl ℝ E F)).toExposed A ×ˢ (l.comp (inr ℝ E F)).toExposed B := by
  let f := l.comp (inl ℝ E F)
  let g := l.comp (inr ℝ E F)
  have split (x : E) (y : F) : l (x, y) = f x + g y :=
    (comp_inl_add_comp_inr l (x, y)).symm
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨hx, hy⟩, h⟩
    refine ⟨⟨hx, fun x' hx' ↦ ?_⟩, ⟨hy, fun y' hy' ↦ ?_⟩⟩
    · exact (add_le_add_iff_right _).mp (by simpa only [split] using h (x', y) ⟨hx', hy⟩)
    · exact (add_le_add_iff_left _).mp (by simpa only [split] using h (x, y') ⟨hx, hy'⟩)
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    refine ⟨⟨hx, hy⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simpa only [split] using add_le_add (hx' a ha) (hy' b hb)

theorem isExposed_prod {A S : Set E} {B T : Set F}
    (hS : IsExposed ℝ A S) (hT : IsExposed ℝ B T) : IsExposed ℝ (A ×ˢ B) (S ×ˢ T) := by
  rintro ⟨⟨x, y⟩, hx, hy⟩
  obtain ⟨f, rfl⟩ := hS ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := hT ⟨y, hy⟩
  refine ⟨f.comp (fst ℝ E F) + g.comp (snd ℝ E F), ?_⟩
  change f.toExposed A ×ˢ g.toExposed B =
    (f.comp (fst ℝ E F) + g.comp (snd ℝ E F)).toExposed (A ×ˢ B)
  rw [toExposed_prod]
  congr 2 <;> ext z <;> simp

private def exposedOfProd (A : Set E) (B : Set F) :
    WithBot (NonemptyExposed A × NonemptyExposed B) → ExposedFace (A ×ˢ B) :=
  WithBot.recBotCoe ⟨∅, isExposed_empty⟩ fun p ↦
    ⟨p.1.val.val ×ˢ p.2.val.val, isExposed_prod p.1.val.property p.2.val.property⟩

private theorem exposedOfProd_le_iff (A : Set E) (B : Set F)
    (p q : WithBot (NonemptyExposed A × NonemptyExposed B)) :
    exposedOfProd A B p ≤ exposedOfProd A B q ↔ p ≤ q := by
  cases p using WithBot.recBotCoe with
  | bot =>
    change ∅ ⊆ (exposedOfProd A B q).val ↔ (⊥ : WithBot _) ≤ q
    exact iff_of_true (empty_subset _) bot_le
  | coe p =>
    cases q using WithBot.recBotCoe with
    | bot =>
      change p.1.val.val ×ˢ p.2.val.val ⊆ ∅ ↔
        (p : WithBot (NonemptyExposed A × NonemptyExposed B)) ≤ ⊥
      exact iff_of_false
        (fun h ↦ (p.1.property.prod p.2.property).ne_empty (subset_empty_iff.mp h))
        (WithBot.not_coe_le_bot p)
    | coe q =>
      change p.1.val.val ×ˢ p.2.val.val ⊆ q.1.val.val ×ˢ q.2.val.val ↔
        (p : WithBot (NonemptyExposed A × NonemptyExposed B)) ≤ ↑q
      rw [WithBot.coe_le_coe, Set.prod_subset_prod_iff' (p.1.property.prod p.2.property)]
      rfl

private theorem exposedOfProd_surjective (A : Set E) (B : Set F) :
    Function.Surjective (exposedOfProd A B) := by
  intro S
  by_cases hn : S.val.Nonempty
  · obtain ⟨l, hl⟩ := S.property hn
    have he : S.val = (l.comp (inl ℝ E F)).toExposed A ×ˢ
        (l.comp (inr ℝ E F)).toExposed B := hl.trans (toExposed_prod l A B)
    rw [he] at hn
    obtain ⟨⟨x, y⟩, hx, hy⟩ := hn
    let Fa : NonemptyExposed A := ⟨⟨_, ContinuousLinearMap.toExposed.isExposed⟩, x, hx⟩
    let Fb : NonemptyExposed B := ⟨⟨_, ContinuousLinearMap.toExposed.isExposed⟩, y, hy⟩
    exact ⟨↑(Fa, Fb), Subtype.ext he.symm⟩
  · exact ⟨⊥, Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hn).symm⟩

/-- The product face order has one empty face and a product of nonempty face orders. -/
def exposedProductIso (A : Set E) (B : Set F) :
    WithBot (NonemptyExposed A × NonemptyExposed B) ≃o ExposedFace (A ×ˢ B) where
  toEquiv := Equiv.ofBijective (exposedOfProd A B)
    ⟨fun a b h ↦ le_antisymm ((exposedOfProd_le_iff A B a b).mp (le_of_eq h))
      ((exposedOfProd_le_iff A B b a).mp (le_of_eq h.symm)), exposedOfProd_surjective A B⟩
  map_rel_iff' := exposedOfProd_le_iff A B _ _

section Polygon

open Polygon.FaceOrder Polygon.GeneralRealization Polygon.Ehrhart

/-- The nonempty geometric polygon faces correspond to all codes except the bottom. -/
def polygonNonemptyIso (n : ℕ) : NonemptyFace (n + 2) ≃o NonemptyExposed (polytope n) where
  toEquiv := Equiv.subtypeEquiv (faceOrderIso (n := n)).toEquiv fun f ↦ by
    change f ≠ Face.bottom ↔ (indexedFace f).Nonempty
    constructor
    · intro hf
      by_contra hn
      exact hf ((faceOrderIso (n := n)).injective (Subtype.ext
        ((Set.not_nonempty_iff_eq_empty.mp hn).trans indexedFace_bottom.symm)))
    · rintro hf rfl
      simp at hf
  map_rel_iff' := faceOrderIso.map_rel_iff

/-- The unit segment used for the physical prism. -/
def unitSegment : Set ℝ := Set.Icc 0 1

private theorem linearOnReal (u : StrongDual ℝ ℝ) (x : ℝ) : u x = x * u 1 := by
  calc
    u x = u (x • (1 : ℝ)) := by simp
    _ = _ := by rw [map_smul, smul_eq_mul]

private theorem exposed_unit_one (u : StrongDual ℝ ℝ) (h : 0 < u 1) :
    u.toExposed unitSegment = {1} := by
  ext x
  change (x ∈ unitSegment ∧ ∀ y ∈ unitSegment, u y ≤ u x) ↔ x = 1
  have h₁ : (1 : ℝ) ∈ unitSegment := by simp [unitSegment]
  constructor
  · intro hx
    have hw : 1 * u 1 ≤ x * u 1 := by
      calc
        _ = u 1 := one_mul _
        _ ≤ u x := hx.2 1 h₁
        _ = _ := linearOnReal u x
    exact le_antisymm hx.1.2 (le_of_not_gt fun hxlt ↦
      (not_le_of_gt (mul_lt_mul_of_pos_right hxlt h)) hw)
  · rintro rfl
    exact ⟨h₁, fun y hy ↦ by
      rw [linearOnReal u y]
      calc
        _ ≤ 1 * u 1 := mul_le_mul_of_nonneg_right hy.2 h.le
        _ = _ := one_mul _⟩

private theorem exposed_unit_zero (u : StrongDual ℝ ℝ) (h : u 1 < 0) :
    u.toExposed unitSegment = {0} := by
  ext x
  change (x ∈ unitSegment ∧ ∀ y ∈ unitSegment, u y ≤ u x) ↔ x = 0
  have h₀ : (0 : ℝ) ∈ unitSegment := by simp [unitSegment]
  constructor
  · intro hx
    have hw := hx.2 0 h₀
    rw [linearOnReal u 0, linearOnReal u x] at hw
    exact le_antisymm ((mul_le_mul_right_of_neg h).mp hw) hx.1.1
  · rintro rfl
    exact ⟨h₀, fun y hy ↦ by
      rw [linearOnReal u y, linearOnReal u 0]
      exact mul_le_mul_of_nonpos_right hy.1 h.le⟩

private theorem exposed_unit_all (u : StrongDual ℝ ℝ) (h : u 1 = 0) :
    u.toExposed unitSegment = unitSegment := by
  ext x
  change (x ∈ unitSegment ∧ ∀ y ∈ unitSegment, u y ≤ u x) ↔ x ∈ unitSegment
  have hu (y : ℝ) : u y = 0 := by rw [linearOnReal u y, h, mul_zero]
  simp only [hu, le_refl, implies_true, and_true]

private def segmentRepr : SegmentFace → Set ℝ
  | .endpoint i => {(i.val : ℝ)}
  | .whole => unitSegment

private theorem segmentRepr_zero : segmentRepr (.endpoint 0) = {0} := by
  simp [segmentRepr]

private theorem segmentRepr_one : segmentRepr (.endpoint 1) = {1} := by
  norm_num [segmentRepr]

private def segmentRealize (f : SegmentFace) : NonemptyExposed unitSegment := by
  refine ⟨⟨segmentRepr f, ?_⟩, ?_⟩
  · cases f with
    | whole => exact IsExposed.refl _
    | endpoint i =>
      fin_cases i
      · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, segmentRepr_zero]
        rw [← exposed_unit_zero (-(ContinuousLinearMap.id ℝ ℝ)) (by simp)]
        exact ContinuousLinearMap.toExposed.isExposed
      · rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, segmentRepr_one]
        rw [← exposed_unit_one (ContinuousLinearMap.id ℝ ℝ) (by simp)]
        exact ContinuousLinearMap.toExposed.isExposed
  · cases f with
    | whole => exact ⟨0, by simp [segmentRepr, unitSegment]⟩
    | endpoint i => exact Set.singleton_nonempty _

private theorem segmentRepr_le_iff (a b : SegmentFace) :
    segmentRepr a ⊆ segmentRepr b ↔ a ≤ b := by
  cases a with
  | whole =>
    cases b with
    | whole => exact iff_of_true Subset.rfl trivial
    | endpoint j =>
      change unitSegment ⊆ {(j.val : ℝ)} ↔ False
      apply iff_false_intro
      intro h
      have h₀ := Set.mem_singleton_iff.mp (h (show (0 : ℝ) ∈ unitSegment by simp [unitSegment]))
      have h₁ := Set.mem_singleton_iff.mp (h (show (1 : ℝ) ∈ unitSegment by simp [unitSegment]))
      linarith only [h₀, h₁]
  | endpoint i =>
    cases b with
    | whole =>
      change {(i.val : ℝ)} ⊆ unitSegment ↔ True
      fin_cases i <;> simp [unitSegment]
    | endpoint j =>
      change ({(i.val : ℝ)} : Set ℝ) ⊆ {(j.val : ℝ)} ↔ i = j
      rw [Set.singleton_subset_iff, Set.mem_singleton_iff]
      exact ⟨fun h ↦ Fin.ext (by exact_mod_cast h), fun h ↦ by rw [h]⟩

private theorem segmentRealize_surjective : Function.Surjective segmentRealize := by
  rintro ⟨⟨S, hS⟩, hne⟩
  obtain ⟨u, hu⟩ := hS hne
  rcases lt_trichotomy (u 1) 0 with h | h | h
  · exact ⟨.endpoint 0, Subtype.ext (Subtype.ext
      (segmentRepr_zero.trans (hu.trans (exposed_unit_zero u h)).symm))⟩
  · exact ⟨.whole, Subtype.ext (Subtype.ext ((hu.trans (exposed_unit_all u h)).symm))⟩
  · exact ⟨.endpoint 1, Subtype.ext (Subtype.ext
      (segmentRepr_one.trans (hu.trans (exposed_unit_one u h)).symm))⟩

/-- The two endpoints and the whole segment give its whole nonempty face order. -/
def segmentFaceIso : SegmentFace ≃o NonemptyExposed unitSegment where
  toEquiv := Equiv.ofBijective segmentRealize
    ⟨fun a b h ↦ le_antisymm ((segmentRepr_le_iff a b).mp (le_of_eq (congrArg
      (fun s : NonemptyExposed unitSegment ↦ s.val.val) h)))
      ((segmentRepr_le_iff b a).mp (le_of_eq (congrArg
        (fun s : NonemptyExposed unitSegment ↦ s.val.val) h.symm))), segmentRealize_surjective⟩
  map_rel_iff' := segmentRepr_le_iff _ _

/-- The actual prism, as a Cartesian product of the polygon hull with a segment. -/
def geometricPrism (n : ℕ) : Set (Point × ℝ) := polytope n ×ˢ unitSegment

/-- The combinatorial prism model is the full exposed-face order of this geometric prism. -/
def prismFaceIso (n : ℕ) : Prism (n + 2) ≃o ExposedFace (geometricPrism n) := by
  let e : NonemptyFace (n + 2) × SegmentFace ≃o
      NonemptyExposed (polytope n) × NonemptyExposed unitSegment :=
    ⟨Equiv.prodCongr (polygonNonemptyIso n).toEquiv segmentFaceIso.toEquiv,
      fun {_ _} ↦ and_congr (polygonNonemptyIso n).map_rel_iff segmentFaceIso.map_rel_iff⟩
  exact e.withBotCongr.trans (exposedProductIso _ _)

/-- The trace theorem counts lattice points of the POP of the actual geometric prism. -/
theorem card_geometricPrism_latticePoints (n q : ℕ) :
    Nat.card (LatticePoints (fun a b : ExposedFace (geometricPrism n) ↦ a ≤ b) q) =
      prismTrace SegmentFace (Fin (q + 1)) (n + 2) := by
  let e := prismFaceIso n
  rw [← Nat.card_congr (latticePointsCongr e.toEquiv (fun a b ↦ e.map_rel_iff.symm) q),
    Nat.card_eq_fintype_card]
  exact card_prism_latticePoints _ _

end Polygon

end PolytopalProducts.Geometry

