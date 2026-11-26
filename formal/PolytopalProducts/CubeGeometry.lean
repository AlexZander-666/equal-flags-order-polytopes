import PolytopalProducts

/-! The complete exposed-face order of the actual unit cube. -/

noncomputable section

namespace PolytopalProducts.Geometry

open Set

variable {A : Type*} [PartialOrder A]
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

private theorem orderIso_bot_empty {S : Set E} (e : WithBot A ≃o ExposedFace S) :
    (e ⊥).val = ∅ := by
  let B : ExposedFace S := ⟨∅, isExposed_empty⟩
  have h : e ⊥ ≤ B := e.monotone (bot_le : ⊥ ≤ e.symm B) |>.trans_eq (e.apply_symm_apply B)
  exact subset_empty_iff.mp h

private def toNonempty {S : Set E} (e : WithBot A ≃o ExposedFace S) (a : A) :
    NonemptyExposed S :=
  ⟨e ↑a, by
    by_contra hn
    have h := (Set.not_nonempty_iff_eq_empty.mp hn).trans (orderIso_bot_empty e).symm
    exact (WithBot.coe_ne_bot : (a : WithBot A) ≠ ⊥) (e.injective (Subtype.ext h))⟩

private theorem toNonempty_surjective {S : Set E} (e : WithBot A ≃o ExposedFace S) :
    Function.Surjective (toNonempty e) := by
  rintro ⟨F, hf⟩
  obtain ⟨a, ha⟩ := e.surjective F
  cases a using WithBot.recBotCoe with
  | bot => exact False.elim (hf.ne_empty ((congrArg Subtype.val ha).symm.trans (orderIso_bot_empty e)))
  | coe a => exact ⟨a, Subtype.ext ha⟩

/-- Remove the unique empty geometric face under an order isomorphism with a new bottom. -/
def nonemptyOfWithBot {S : Set E} (e : WithBot A ≃o ExposedFace S) :
    A ≃o NonemptyExposed S where
  toEquiv := Equiv.ofBijective (toNonempty e)
    ⟨fun _ _ he ↦ WithBot.coe_injective (e.injective (congrArg Subtype.val he)),
      toNonempty_surjective e⟩
  map_rel_iff' :=
    (e.map_rel_iff : e (↑_ : WithBot A) ≤ e ↑_ ↔ _).trans WithBot.coe_le_coe

/-- All nonempty face codes of the three-dimensional coordinate cube. -/
abbrev CubeFace := WithBot (SegmentFace × (SegmentFace × SegmentFace))

/-- The actual unit cube in three real coordinates. -/
def cube : Set (ℝ × (ℝ × ℝ)) := unitSegment ×ˢ (unitSegment ×ˢ unitSegment)

def cubeFaceIso : CubeFace ≃o ExposedFace cube := by
  let prodSeg : SegmentFace × SegmentFace ≃o
      NonemptyExposed unitSegment × NonemptyExposed unitSegment :=
    ⟨Equiv.prodCongr segmentFaceIso.toEquiv segmentFaceIso.toEquiv,
      fun {_ _} ↦ and_congr segmentFaceIso.map_rel_iff segmentFaceIso.map_rel_iff⟩
  let square := nonemptyOfWithBot (prodSeg.withBotCongr.trans (exposedProductIso _ _))
  let prism : (SegmentFace × (SegmentFace × SegmentFace)) ≃o
      NonemptyExposed unitSegment × NonemptyExposed (unitSegment ×ˢ unitSegment) :=
    ⟨Equiv.prodCongr segmentFaceIso.toEquiv square.toEquiv,
      fun {_ _} ↦ and_congr segmentFaceIso.map_rel_iff square.map_rel_iff⟩
  exact prism.withBotCongr.trans (exposedProductIso _ _)

/-- The actual six-sided pyramid, with the six parabola base points and the apex. -/
def hexagonalPyramid : Set ((ℝ × ℝ) × ℝ) := geometricPyramid 3

def hexagonalPyramidFaceIso : Pyramid 5 ≃o ExposedFace hexagonalPyramid :=
  pyramidFaceIso 3

end PolytopalProducts.Geometry

