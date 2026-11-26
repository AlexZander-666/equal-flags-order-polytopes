import PolytopalProducts.PrismGeometry

/-! The physical pyramid realizes the product of the full base-face order with a two-chain. -/

noncomputable section
open Set ContinuousLinearMap

namespace PolytopalProducts.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def layer (A : Set E) : Set (E × ℝ) := A ×ˢ ({0} : Set ℝ)

def apex : E × ℝ := (0, 1)

def pyramid (A : Set E) : Set (E × ℝ) := convexHull ℝ (insert apex (layer A))

private def restrictBase (l : StrongDual ℝ (E × ℝ)) : StrongDual ℝ E :=
  l.comp (inl ℝ E ℝ)

private theorem apex_mem_pyramid (A : Set E) : apex ∈ pyramid A :=
  subset_convexHull ℝ _ (mem_insert _ _)

private theorem layer_subset_pyramid (A : Set E) : layer A ⊆ pyramid A :=
  (subset_insert _ _).trans (subset_convexHull ℝ _)

private theorem convex_layer {A : Set E} (hA : Convex ℝ A) : Convex ℝ (layer A) :=
  hA.prod (convex_singleton _)

private theorem base_mem_pyramid_iff {A : Set E} (hA : Convex ℝ A) (x : E) :
    (x, (0 : ℝ)) ∈ pyramid A ↔ x ∈ A := by
  refine ⟨fun h ↦ ?_, fun h ↦ layer_subset_pyramid A ⟨h, rfl⟩⟩
  obtain rfl | hn := A.eq_empty_or_nonempty
  · simp [pyramid, layer, apex] at h
  have hl : (layer A).Nonempty := hn.prod (singleton_nonempty _)
  rw [pyramid, convexHull_insert hl,
    (convex_layer hA).convexHull_eq, convexJoin_singleton_left] at h
  rcases mem_iUnion.mp h with ⟨⟨y, t⟩, h⟩
  rcases mem_iUnion.mp h with ⟨⟨hy, ht⟩, hs⟩
  change t = 0 at ht
  subst t
  obtain ⟨a, b, _, _, hab, he⟩ := hs
  have ha : a = 0 := by simpa [apex] using congrArg Prod.snd he
  have hb : b = 1 := by simpa [ha] using hab
  rw [ha, hb, zero_smul, one_smul, zero_add] at he
  have hxy : y = x := congrArg Prod.fst he
  exact hxy ▸ hy

/-- The base layer of an exposed subset is obtained by keeping base maximizers. -/
private theorem base_maximizers {l : StrongDual ℝ (E × ℝ)} {A : Set E} {m : ℝ}
    (hbound : ∀ x ∈ A, restrictBase l x ≤ m)
    (hmax : ∃ x ∈ A, restrictBase l x = m) :
    {z ∈ layer A | l z = m} = layer ((restrictBase l).toExposed A) := by
  obtain ⟨p, hp, hpm⟩ := hmax
  ext ⟨x, t⟩
  change ((x ∈ A ∧ t = 0) ∧ l (x, t) = m) ↔
    ((x ∈ A ∧ ∀ y ∈ A, restrictBase l y ≤ restrictBase l x) ∧ t = 0)
  constructor
  · rintro ⟨⟨hx, rfl⟩, he⟩
    exact ⟨⟨hx, fun y hy ↦ (hbound y hy).trans_eq he.symm⟩, rfl⟩
  · rintro ⟨⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨hx, rfl⟩, (hbound x hx).antisymm (hpm ▸ hx' p hp)⟩

/-- A hull maximizer is a convex combination of maximizing generators.
The proof uses the same convex support argument as the polygon base realization. -/
private theorem exposed_hull (l : StrongDual ℝ (E × ℝ)) (S : Set (E × ℝ)) (m : ℝ)
    (hbound : ∀ x ∈ S, l x ≤ m) (hmax : ∃ x ∈ S, l x = m) :
    l.toExposed (convexHull ℝ S) = convexHull ℝ {x ∈ S | l x = m} := by
  let F := convexHull ℝ {x ∈ S | l x = m}
  let C : Set (E × ℝ) := {x | l x ≤ m ∧ (l x = m → x ∈ F)}
  have hc : Convex ℝ C := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    change l x ≤ m ∧ _ at hx
    change l y ≤ m ∧ _ at hy
    change l (a • x + b • y) ≤ m ∧ _
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    have hm : a * m + b * m = m := by linear_combination m * hab
    refine ⟨(add_le_add (mul_le_mul_of_nonneg_left hx.1 ha.le)
      (mul_le_mul_of_nonneg_left hy.1 hb.le)).trans_eq hm, ?_⟩
    intro he
    have hxe : l x = m := hx.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt ha)
        (mul_le_mul_of_nonneg_left hy.1 hb.le)]
    have hye : l y = m := hy.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.1 ha.le)
        (mul_lt_mul_of_pos_left hlt hb)]
    exact (convex_convexHull ℝ _) (hx.2 hxe) (hy.2 hye) ha.le hb.le hab
  have hall : convexHull ℝ S ⊆ C := convexHull_min (fun x hx ↦
    ⟨hbound x hx, fun he ↦ subset_convexHull ℝ _ ⟨hx, he⟩⟩) hc
  obtain ⟨u, hu, hum⟩ := hmax
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    exact (hall hx).2 ((hall hx).1.antisymm (hum ▸ hh u (subset_convexHull ℝ S hu)))
  · intro hx
    have hx₁ : x ∈ convexHull ℝ S := convexHull_mono (fun _ h ↦ h.1) hx
    have hx₂ : m ≤ l x :=
      convexHull_min (fun y (h : y ∈ {z ∈ S | l z = m}) ↦ h.2.ge)
        (convex_halfSpace_ge l.toLinearMap.isLinear m) hx
    exact ⟨hx₁, fun y hy ↦ (hall hy).1.trans hx₂⟩

private theorem expose_pyramid {l : StrongDual ℝ (E × ℝ)} {A : Set E} {m : ℝ}
    (hbound : ∀ x ∈ A, restrictBase l x ≤ m)
    (hmax : ∃ x ∈ A, restrictBase l x = m) :
    l.toExposed (pyramid A) = convexHull ℝ
      ((if m ≤ l apex then {apex} else ∅) ∪
        (if l apex ≤ m then layer ((restrictBase l).toExposed A) else ∅)) := by
  let r := l apex
  obtain ⟨p, hp, hpm⟩ := hmax
  have hb : ∀ z ∈ layer A, l z ≤ m := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    change t = 0 at ht
    subst t
    exact hbound z hz
  rw [pyramid, exposed_hull l _ (max r m)]
  · congr 1
    rw [← base_maximizers hbound ⟨p, hp, hpm⟩]
    ext z
    change (z ∈ insert apex (layer A) ∧ l z = max r m) ↔
      z ∈ (if m ≤ r then ({apex} : Set (E × ℝ)) else ∅) ∨
      z ∈ (if r ≤ m then {z ∈ layer A | l z = m} else ∅)
    constructor
    · rintro ⟨hz, hm⟩
      rcases mem_insert_iff.mp hz with rfl | hz
      · left
        have hrm : m ≤ r := (le_max_right r m).trans_eq hm.symm
        rw [if_pos hrm]
        rfl
      · have hzle := hb z hz
        have hrm : r ≤ m := (le_max_left _ _).trans (hm ▸ hzle)
        right
        rw [if_pos hrm]
        exact ⟨hz, hm.trans (max_eq_right hrm)⟩
    · intro h
      rcases h with h | h
      · by_cases hrm : m ≤ r
        · change z ∈ (if m ≤ r then ({apex} : Set (E × ℝ)) else ∅) at h
          simp only [hrm, if_true, mem_singleton_iff] at h
          exact ⟨Or.inl h, by rw [h, max_eq_left hrm]⟩
        · rw [if_neg hrm] at h
          exact h.elim
      · by_cases hrm : r ≤ m
        · change z ∈ (if r ≤ m then {z ∈ layer A | l z = m} else ∅) at h
          simp only [hrm, if_true] at h
          exact ⟨Or.inr h.1, h.2.trans (max_eq_right hrm).symm⟩
        · rw [if_neg hrm] at h
          exact h.elim
  · rintro z (rfl | hz)
    · exact le_max_left _ _
    · exact (hb z hz).trans (le_max_right _ _)
  · rcases le_total m r with h | h
    · exact ⟨apex, Or.inl rfl, (max_eq_left h).symm⟩
    · exact ⟨(p, 0), Or.inr ⟨hp, rfl⟩, hpm.trans (max_eq_right h).symm⟩

private def withHeight (f : StrongDual ℝ E) (b : ℝ) : StrongDual ℝ (E × ℝ) :=
  f.comp (fst ℝ E ℝ) + b • snd ℝ E ℝ

private theorem restrict_withHeight (f : StrongDual ℝ E) (b : ℝ) :
    restrictBase (withHeight f b) = f := by
  ext x
  simp [restrictBase, withHeight]

private theorem withHeight_apex (f : StrongDual ℝ E) (b : ℝ) :
    withHeight f b apex = b := by
  simp [withHeight, apex]

private theorem expose_withHeight {A : Set E} {f : StrongDual ℝ E} {m : ℝ}
    (b : ℝ) (hbound : ∀ x ∈ A, f x ≤ m) (hmax : ∃ x ∈ A, f x = m) :
    (withHeight f b).toExposed (pyramid A) = convexHull ℝ
      ((if m ≤ b then {apex} else ∅) ∪ (if b ≤ m then layer (f.toExposed A) else ∅)) := by
  simpa only [restrict_withHeight, withHeight_apex] using
    (expose_pyramid (l := withHeight f b)
      (by simpa only [restrict_withHeight] using hbound)
      (by simpa only [restrict_withHeight] using hmax))

private def liftFace (S : Set E) : Bool → Set (E × ℝ)
  | false => layer S
  | true => pyramid S

private theorem lift_isExposed {A S : Set E} (hA : Convex ℝ A) (hn : A.Nonempty)
    (hS : IsExposed ℝ A S) (b : Bool) : IsExposed ℝ (pyramid A) (liftFace S b) := by
  obtain rfl | hs := S.eq_empty_or_nonempty
  · cases b
    · simpa [liftFace, layer] using (isExposed_empty (𝕜 := ℝ) (A := pyramid A))
    · obtain ⟨p, hp⟩ := hn
      intro _
      refine ⟨withHeight 0 1, ?_⟩
      change pyramid ∅ = (withHeight 0 1).toExposed (pyramid A)
      rw [expose_withHeight (f := 0) (m := 0) 1 (by simp) ⟨p, hp, by simp⟩]
      norm_num [pyramid, layer]
  · obtain ⟨p, hp⟩ := hs
    obtain ⟨f, hf⟩ := hS ⟨p, hp⟩
    change S = f.toExposed A at hf
    obtain ⟨hpa, hpm⟩ := hf ▸ hp
    cases b
    · intro _
      refine ⟨withHeight f (f p - 1), ?_⟩
      change layer S = (withHeight f (f p - 1)).toExposed (pyramid A)
      rw [expose_withHeight (f p - 1) hpm ⟨p, hpa, rfl⟩, ← hf]
      simp [show ¬ f p ≤ f p - 1 by linarith, show f p - 1 ≤ f p by linarith,
        (convex_layer (hS.convex hA)).convexHull_eq]
    · intro _
      refine ⟨withHeight f (f p), ?_⟩
      change pyramid S = (withHeight f (f p)).toExposed (pyramid A)
      rw [expose_withHeight (f p) hpm ⟨p, hpa, rfl⟩, ← hf]
      simp only [pyramid, le_refl, if_true, singleton_union]

private theorem base_mem_lift {S : Set E} (hc : Convex ℝ S) (x : E) (b : Bool) :
    (x, (0 : ℝ)) ∈ liftFace S b ↔ x ∈ S := by
  cases b
  · simp [liftFace, layer]
  · exact base_mem_pyramid_iff hc x

private theorem apex_mem_lift (S : Set E) (b : Bool) :
    apex ∈ liftFace S b ↔ b = true := by
  cases b
  · simp [liftFace, layer, apex]
  · exact iff_of_true (apex_mem_pyramid S) rfl

private theorem lift_subset_iff {S T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T) (b c : Bool) :
    liftFace S b ⊆ liftFace T c ↔ S ⊆ T ∧ b ≤ c := by
  constructor
  · intro h
    refine ⟨fun x hx ↦ (base_mem_lift hT x c).mp (h ((base_mem_lift hS x b).mpr hx)), ?_⟩
    cases b
    · simp
    · have hc := (apex_mem_lift T c).mp (h ((apex_mem_lift S true).mpr rfl))
      simp [hc]
  · rintro ⟨hst, hbc⟩
    have hlt : layer S ⊆ layer T := Set.prod_mono_left hst
    cases b <;> cases c
    · exact hlt
    · exact hlt.trans (layer_subset_pyramid T)
    · exact False.elim ((by decide : ¬(true ≤ false)) hbc)
    · exact convexHull_mono (insert_subset_insert hlt)

private def pyramidRealize {A : Set E} (hA : Convex ℝ A) (hn : A.Nonempty)
    (p : ExposedFace A × Bool) : ExposedFace (pyramid A) :=
  ⟨liftFace p.1.val p.2, lift_isExposed hA hn p.1.property p.2⟩

private theorem pyramidRealize_le_iff {A : Set E} (hA : Convex ℝ A) (hn : A.Nonempty)
    (p q : ExposedFace A × Bool) : pyramidRealize hA hn p ≤ pyramidRealize hA hn q ↔ p ≤ q :=
  lift_subset_iff (p.1.property.convex hA) (q.1.property.convex hA) p.2 q.2

private theorem pyramidRealize_surjective {A : Set E} (hA : Convex ℝ A)
    (hn : A.Nonempty) (hcompact : IsCompact A) : Function.Surjective (pyramidRealize hA hn) := by
  intro S
  by_cases hs : S.val.Nonempty
  · obtain ⟨l, hl⟩ := S.property hs
    let f := restrictBase l
    let B : ExposedFace A := ⟨f.toExposed A, ContinuousLinearMap.toExposed.isExposed⟩
    obtain ⟨p, hp, hm⟩ := hcompact.exists_isMaxOn hn f.continuous.continuousOn
    have hh := expose_pyramid (l := l) (m := f p) (fun x hx ↦ hm hx) ⟨p, hp, rfl⟩
    change S.val = l.toExposed (pyramid A) at hl
    rw [hh] at hl
    change S.val = convexHull ℝ
      ((if f p ≤ l apex then {apex} else ∅) ∪
        (if l apex ≤ f p then layer (f.toExposed A) else ∅)) at hl
    rcases lt_trichotomy (l apex) (f p) with ha | ha | ha
    · refine ⟨(B, false), Subtype.ext ?_⟩
      change layer (f.toExposed A) = S.val
      rw [if_neg (not_le_of_gt ha), if_pos ha.le, empty_union,
        (convex_layer (B.property.convex hA)).convexHull_eq] at hl
      exact hl.symm
    · refine ⟨(B, true), Subtype.ext ?_⟩
      change pyramid (f.toExposed A) = S.val
      rw [if_pos ha.ge, if_pos ha.le, singleton_union] at hl
      exact hl.symm
    · refine ⟨(⟨∅, isExposed_empty⟩, true), Subtype.ext ?_⟩
      change pyramid (∅ : Set E) = S.val
      rw [if_pos ha.le, if_neg (not_le_of_gt ha), union_empty, convexHull_singleton] at hl
      simpa [pyramid, layer] using hl.symm
  · refine ⟨(⟨∅, isExposed_empty⟩, false), Subtype.ext ?_⟩
    change layer (∅ : Set E) = S.val
    rw [Set.not_nonempty_iff_eq_empty.mp hs]
    simp [layer]

/-- The exposed-face order of a physical pyramid is its base face order times a two-chain. -/
def exposedPyramidIso {A : Set E} (hA : Convex ℝ A) (hn : A.Nonempty)
    (hcompact : IsCompact A) : (ExposedFace A × Bool) ≃o ExposedFace (pyramid A) where
  toEquiv := Equiv.ofBijective (pyramidRealize hA hn)
    ⟨fun p q h ↦ le_antisymm ((pyramidRealize_le_iff hA hn p q).mp (le_of_eq h))
      ((pyramidRealize_le_iff hA hn q p).mp (le_of_eq h.symm)),
      pyramidRealize_surjective hA hn hcompact⟩
  map_rel_iff' := pyramidRealize_le_iff hA hn _ _

section Polygon

open Polygon.GeneralRealization Polygon.Ehrhart

private def finTwoIsoBool : Fin 2 ≃o Bool where
  toFun i := i == 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> decide
  right_inv b := by cases b <;> decide
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The physical pyramid with apex one unit above the plane of the polygon hull. -/
def geometricPyramid (n : ℕ) : Set (Point × ℝ) := pyramid (polytope n)

/-- The model including the empty face, apex, base and lateral faces. -/
def pyramidFaceIso (n : ℕ) : Pyramid (n + 2) ≃o ExposedFace (geometricPyramid n) := by
  let e : Pyramid (n + 2) ≃o (ExposedFace (polytope n) × Bool) :=
    ⟨Equiv.prodCongr (faceOrderIso (n := n)).toEquiv finTwoIsoBool.toEquiv,
      fun {_ _} ↦ and_congr faceOrderIso.map_rel_iff finTwoIsoBool.map_rel_iff⟩
  exact e.trans (exposedPyramidIso (convex_convexHull ℝ _)
    ⟨point (0 : Index n), point_mem_polytope _⟩ ((Set.finite_range _).isCompact_convexHull ℝ))

/-- The trace formula counts POP lattice points of the complete genuine pyramid face order. -/
theorem card_geometricPyramid_latticePoints (n q : ℕ) :
    Nat.card (LatticePoints (fun a b : ExposedFace (geometricPyramid n) ↦ a ≤ b) q) =
      productTrace (Fin 2) (Fin (q + 1)) (n + 2) := by
  let e := pyramidFaceIso n
  rw [← Nat.card_congr (latticePointsCongr e.toEquiv (fun a b ↦ e.map_rel_iff.symm) q),
    Nat.card_eq_fintype_card]
  exact card_pyramid_latticePoints _ _

end Polygon

end PolytopalProducts.Geometry

