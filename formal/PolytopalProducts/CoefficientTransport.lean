import PolytopalProducts.OrderFaces
import PolytopalProducts.CubeGeometry

/-! Transporting the actual order-polytope faces and their dimensions along a face-order iso. -/

noncomputable section

namespace PolytopalProducts.OrderFaces

open Set ContinuousLinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

private theorem image_exposed (e : E ≃L[ℝ] F) (l : StrongDual ℝ E) (A : Set E) :
    e '' l.toExposed A =
      (l.comp e.symm.toContinuousLinearMap).toExposed (e '' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hx.2 z hz
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro z hz
    simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hy (e z) ⟨z, hz, rfl⟩

private theorem finrank_image (e : E ≃L[ℝ] F) (S : Set E) :
    Module.finrank ℝ (vectorSpan ℝ (e '' S)) = Module.finrank ℝ (vectorSpan ℝ S) := by
  let a := e.toLinearEquiv.toAffineEquiv.toAffineMap
  change Module.finrank ℝ (vectorSpan ℝ (a '' S)) = _
  rw [← a.map_vectorSpan]
  exact (Submodule.equivMapOfInjective a.linear e.injective (vectorSpan ℝ S)).finrank_eq.symm

private def mapDimensionalFace (e : E ≃L[ℝ] F) {A : Set E} {B : Set F} (h : e '' A = B)
    (d : ℕ) (p : {p : Set E // IsExposed ℝ A p ∧ p.Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ p) = d}) :
    {p : Set F // IsExposed ℝ B p ∧ p.Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ p) = d} := by
  refine ⟨e '' p.val, ?_, p.property.2.1.image _, (finrank_image e _).trans p.property.2.2⟩
  obtain ⟨l, hl⟩ := p.property.1 p.property.2.1
  intro _
  refine ⟨l.comp e.symm.toContinuousLinearMap, ?_⟩
  change e '' p.val = (l.comp e.symm.toContinuousLinearMap).toExposed B
  rw [← h, hl]
  exact image_exposed e l A

private def dimensionalFacesEquiv (e : E ≃L[ℝ] F) {A : Set E} {B : Set F} (h : e '' A = B)
    (d : ℕ) :
    {p : Set E // IsExposed ℝ A p ∧ p.Nonempty ∧ Module.finrank ℝ (vectorSpan ℝ p) = d} ≃
    {p : Set F // IsExposed ℝ B p ∧ p.Nonempty ∧ Module.finrank ℝ (vectorSpan ℝ p) = d} where
  toFun := mapDimensionalFace e h d
  invFun := mapDimensionalFace e.symm (by rw [← h]; exact e.toEquiv.symm_image_image A) d
  left_inv p := Subtype.ext (e.toEquiv.symm_image_image p.val)
  right_inv p := Subtype.ext (e.toEquiv.image_symm_image p.val)

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

private theorem image_orderPolytope (e : X ≃o Y) :
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Y ↦ ℝ) e.toEquiv) ''
      Polygon.Ehrhart.orderPolytope (· ≤ · : X → X → Prop) =
        Polygon.Ehrhart.orderPolytope (· ≤ · : Y → Y → Prop) := by
  let c := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Y ↦ ℝ) e.toEquiv
  have h (f : X → ℝ) (x : X) : c f (e x) = f x := by
    change Equiv.piCongrLeft (fun _ : Y ↦ ℝ) e.toEquiv f (e.toEquiv x) = f x
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  have he (f : X → ℝ) :
      c f ∈ Polygon.Ehrhart.orderPolytope (· ≤ · : Y → Y → Prop) ↔
        f ∈ Polygon.Ehrhart.orderPolytope (· ≤ · : X → X → Prop) := by
    constructor
    · rintro ⟨bounds, mono⟩
      exact ⟨fun x ↦ h f x ▸ bounds (e x),
        fun x y hxy ↦ by simpa only [h] using mono (e x) (e y) (e.monotone hxy)⟩
    · rintro ⟨bounds, mono⟩
      constructor
      · intro x
        obtain ⟨a, rfl⟩ := e.surjective x
        rw [h]
        exact bounds a
      · intro x y hxy
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        rw [h, h]
        exact mono a b (e.map_rel_iff.mp hxy)
  ext f
  obtain ⟨g, rfl⟩ := c.surjective f
  constructor
  · rintro ⟨a, ha, hag⟩
    have hag' := c.injective hag
    exact (he g).mpr (hag' ▸ ha)
  · exact fun hf ↦ ⟨g, (he g).mp hf, rfl⟩

/-- The genuine face coefficients depend only on the order of the coordinate indices. -/
theorem fCoefficient_iso (e : X ≃o Y) (d : ℕ) :
    fCoefficient X d = fCoefficient Y d :=
  Nat.card_congr (dimensionalFacesEquiv
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Y ↦ ℝ) e.toEquiv) (image_orderPolytope e) d)

end PolytopalProducts.OrderFaces

