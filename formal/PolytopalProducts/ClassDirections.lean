import PolytopalProducts.Reach

/-! The dimension of a nonempty order face is the number of free equality classes. -/

noncomputable section

namespace PolytopalProducts.OrderFaces

open Set
open scoped Classical

variable {V : Type*} [Fintype V] [PartialOrder V]

/-- Directions in the original coordinate space which are constant on the equality classes. -/
def classDirections (s : Finset (Arc V)) : Submodule ℝ (V → ℝ) where
  carrier := {z | ∀ a b, sameClass s a b → coord V a z = coord V b z}
  zero_mem' := by simp
  add_mem' hx hy a b h := by rw [map_add, map_add, hx a b h, hy a b h]
  smul_mem' r _ hx a b h := by rw [map_smul, map_smul, hx a b h]

theorem vectorSpan_seededFace (s : Finset (Arc V)) (hn : (seededFace s).Nonempty) :
    vectorSpan ℝ (seededFace s) = classDirections s := by
  let F := seededFace s
  have hF : IsExposed ℝ (Halfspaces.body (form V) (rhs V)) F :=
    Halfspaces.face_isExposed _ _ _
  obtain ⟨x, hx, hs⟩ := Halfspaces.exists_strict_point _ _ hF hn
  have hclass (z : V → ℝ) (hz : z ∈ F) (a b : Pinned V) (h : sameClass s a b) :
      value V z a = value V z b :=
    ((mem_seededFace_iff s z).mp hz _ _ h.1).antisymm
      ((mem_seededFace_iff s z).mp hz _ _ h.2)
  change vectorSpan ℝ F = classDirections s
  apply le_antisymm
  · rw [vectorSpan_eq_span_vsub_set_right ℝ hx]
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩ a b hab
    change coord V a (y - x) = coord V b (y - x)
    rw [map_sub, map_sub]
    have h₁ := hclass x hx a b hab
    have h₂ := hclass y hy a b hab
    unfold value at h₁ h₂
    linarith
  · let t := Halfspaces.active (form V) (rhs V) F
    have he : F = Halfspaces.face (form V) (rhs V) t :=
      Halfspaces.eq_face_active _ _ hF hn
    have hxt : x ∈ Halfspaces.face (form V) (rhs V) t := he ▸ hx
    have hv : vectorSpan ℝ F = Halfspaces.tangent (form V) t :=
      he.symm ▸ Halfspaces.vectorSpan_face _ _ t hxt hs
    rw [hv]
    intro z hz e he'
    have hre : reach s e.val.2 e.val.1 := by
      have hi : e ∈ tightArcs s := active_seededFace s hn ▸ he'
      exact (Finset.mem_filter.mp hi).2
    exact sub_eq_zero.mpr (hz _ _ ⟨reach_of_le s e.property.le, hre⟩)

section ClassIndex

variable {K : Type*} [Fintype K] (s : Finset (Arc V))
variable (rep : Pinned V → K) (onto : Function.Surjective rep)
variable (hrep : ∀ a b, rep a = rep b ↔ sameClass s a b)

private abbrev FreeClass := {k : K // k ≠ rep ⊥ ∧ k ≠ rep (high V)}

private def extend (u : FreeClass rep → ℝ) (k : K) : ℝ :=
  if h : k ≠ rep ⊥ ∧ k ≠ rep (high V) then u ⟨k, h⟩ else 0

omit [Fintype V] [PartialOrder V] [Fintype K] in
private theorem coord_extend (u : FreeClass rep → ℝ) (a : Pinned V) :
    coord V a (fun v ↦ extend rep u (rep (interior V v))) = extend rep u (rep a) := by
  cases a using WithBot.recBotCoe with
  | bot => simp [extend, coord]
  | coe a =>
    cases a using WithTop.recTopCoe with
    | top =>
      change coord V (high V) _ = extend rep u (rep (high V))
      rw [extend, dif_neg (fun h ↦ h.2 rfl)]
      simp only [coord, high, WithBot.recBotCoe_coe, WithTop.recTopCoe_top, zero_apply]
    | coe a => rfl

private def restrictClass (d : classDirections s) (k : FreeClass rep) : ℝ :=
  coord V (Classical.choose (onto k.val)) d.val

private def expandClass (u : FreeClass rep → ℝ) : classDirections s :=
  ⟨fun v ↦ extend rep u (rep (interior V v)), fun a b hab ↦ by
    rw [coord_extend, coord_extend, (hrep a b).mpr hab]⟩

omit [Fintype V] [Fintype K] in
include hrep in
private theorem coord_eq_zero_of_nonfree (d : classDirections s) (a : Pinned V)
    (hn : ¬(rep a ≠ rep ⊥ ∧ rep a ≠ rep (high V))) : coord V a d.val = 0 := by
  by_cases h : rep a = rep ⊥
  · have hh := d.property _ _ ((hrep a ⊥).mp h)
    simpa [coord] using hh
  · have hhigh : rep a = rep (high V) := by
      by_contra h'
      exact hn ⟨h, h'⟩
    have hh := d.property _ _ ((hrep a (high V)).mp hhigh)
    simpa only [coord, high, WithBot.recBotCoe_coe, WithTop.recTopCoe_top, zero_apply] using hh

/-- The independent direction coordinates are one scalar for each class not containing a pin. -/
def classDirectionsEquiv : classDirections s ≃ₗ[ℝ] (FreeClass rep → ℝ) where
  toFun d := restrictClass s rep onto d
  invFun u := expandClass s rep hrep u
  left_inv d := by
    apply Subtype.ext
    funext v
    let k := rep (interior V v)
    change extend rep (restrictClass s rep onto d) k = d.val v
    by_cases hk : k ≠ rep ⊥ ∧ k ≠ rep (high V)
    · rw [extend, dif_pos hk]
      have he := (hrep (Classical.choose (onto k)) (interior V v)).mp
        (Classical.choose_spec (onto k))
      exact d.property _ _ he
    · rw [extend, dif_neg hk]
      exact (coord_eq_zero_of_nonfree s rep hrep d (interior V v) hk).symm
  right_inv u := by
    funext k
    change coord V (Classical.choose (onto k.val))
      (fun v ↦ extend rep u (rep (interior V v))) = u k
    rw [coord_extend, Classical.choose_spec (onto k.val), extend, dif_pos k.property]
  map_add' x y := by
    funext k
    exact (coord V (Classical.choose (onto k.val))).map_add x.val y.val
  map_smul' t x := by
    funext k
    exact (coord V (Classical.choose (onto k.val))).map_smul t x.val

include hrep onto in
/-- The face dimension is the number of equality classes minus the two pinned classes. -/
theorem finrank_seededFace (hn : (seededFace s).Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (seededFace s)) = Fintype.card K - 2 := by
  have hpin : rep ⊥ ≠ rep (high V) := by
    intro h
    exact (seededFace_nonempty_iff s).mp hn ((hrep _ _).mp h).2
  have hfree :
      (Finset.univ.filter fun k : K ↦ k ≠ rep ⊥ ∧ k ≠ rep (high V)) =
        Finset.univ \ {rep ⊥, rep (high V)} := by
    ext k
    simp [not_or]
  rw [vectorSpan_seededFace s hn, (classDirectionsEquiv s rep onto hrep).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_subtype, hfree, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Finset.card_pair hpin]
  rfl

end ClassIndex

end PolytopalProducts.OrderFaces

