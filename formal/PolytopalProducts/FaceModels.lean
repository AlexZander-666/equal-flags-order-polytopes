import PolytopalProducts.FaceProfiles

/-! The full pyramid model and the prism model with its single empty face. -/

noncomputable section
open scoped BigOperators Classical

namespace PolytopalProducts

open Polygon.FaceOrder Polygon.Ehrhart

/-- The named nonempty faces of a polygon. -/
abbrev NonemptyFace (k : ℕ) := {f : Face k // f ≠ Face.bottom}

/-- The nonempty segment faces. The two endpoints are incomparable. -/
inductive SegmentFace
  | endpoint (i : Fin 2)
  | whole
  deriving DecidableEq, Fintype

def SegmentFace.rel : SegmentFace → SegmentFace → Prop
  | _, .whole => True
  | .endpoint i, .endpoint j => i = j
  | .whole, .endpoint _ => False

instance : PartialOrder SegmentFace where
  le := SegmentFace.rel
  le_refl x := by cases x <;> simp [SegmentFace.rel]
  le_trans x y z h₁ h₂ := by cases x <;> cases y <;> cases z <;>
    simp_all [SegmentFace.rel]
  le_antisymm x y h₁ h₂ := by cases x <;> cases y <;> simp_all [SegmentFace.rel]

theorem card_segmentFace : Fintype.card SegmentFace = 3 := by
  let e : SegmentFace ≃ Option (Fin 2) :=
    { toFun := fun | .endpoint i => some i | .whole => none
      invFun := fun | some i => .endpoint i | none => .whole
      left_inv := fun x ↦ by cases x <;> rfl
      right_inv := fun x ↦ by cases x <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The full pyramid poset from the full polygon and the two-element chain. -/
abbrev Pyramid (k : ℕ) := Face k × Fin 2

/-- The full prism face poset. Its bottom is separate from the product of nonempty faces. -/
abbrev PrismModel (k : ℕ) (Q : Type*) := WithBot (NonemptyFace k × Q)

/-- The full prism poset from the nonempty polygon and segment faces. -/
abbrev Prism (k : ℕ) := PrismModel k SegmentFace

/-- Adding one bottom to the nonempty polygon faces recovers the known full face poset. -/
def faceWithBotIso (k : ℕ) : WithBot (NonemptyFace k) ≃o Face k where
  toFun := WithBot.recBotCoe Face.bottom Subtype.val
  invFun f := if h : f = Face.bottom then ⊥ else ↑(⟨f, h⟩ : NonemptyFace k)
  left_inv x := by
    cases x using WithBot.recBotCoe with
    | bot => simp
    | coe x => simp [x.property]
  right_inv f := by
    by_cases h : f = Face.bottom <;> simp [h]
  map_rel_iff' := by
    intro x y
    cases x using WithBot.recBotCoe with
    | bot =>
      cases y using WithBot.recBotCoe with
      | bot => simp
      | coe y => simpa using bottom_le_face y.val
    | coe x =>
      cases y using WithBot.recBotCoe with
      | bot =>
        change x.val ≤ Face.bottom ↔ (x : WithBot (NonemptyFace k)) ≤ ⊥
        exact iff_of_false (fun h ↦ x.property (le_antisymm h (bottom_le_face _)))
          (WithBot.not_coe_le_bot x)
      | coe y =>
        change x.val ≤ y.val ↔ (x : WithBot (NonemptyFace k)) ≤ ↑y
        exact (WithBot.coe_le_coe (a := x) (b := y)).symm

theorem card_pyramid (k : ℕ) : Fintype.card (Pyramid k) = 4 * (k + 1) + 4 := by
  rw [Fintype.card_prod, Fintype.card_fin, card_face]
  omega

theorem card_prism (k : ℕ) : Fintype.card (Prism k) = 6 * (k + 1) + 4 := by
  have h := Fintype.card_congr (faceWithBotIso k).toEquiv
  change Fintype.card (Option (NonemptyFace k)) = _ at h
  change Fintype.card (Option (NonemptyFace k × SegmentFace)) = _
  rw [Fintype.card_option, card_face] at h
  rw [Fintype.card_option, Fintype.card_prod, card_segmentFace]
  omega

private def coeOrderHom (A : Type*) [Preorder A] : A →o WithBot A :=
  ⟨fun a ↦ ↑a, WithBot.coe_mono⟩

private def withBotExtend {A B : Type*} [Preorder A] [Preorder B]
    (c : B) (f : A →o B) (h : ∀ x, c ≤ f x) : WithBot A →o B where
  toFun := WithBot.recBotCoe c f
  monotone' := WithBot.monotone_iff.mpr ⟨by simpa using f.monotone, by simpa using h⟩

private def prismToProfile {A Q T : Type*} [Preorder A] [Preorder Q] [Preorder T]
    (f : WithBot (A × Q) →o T) :
    {g : WithBot A →o (Q →o T) // g ⊥ = OrderHom.const Q (f ⊥)} :=
  ⟨withBotExtend (OrderHom.const Q (f ⊥))
    (OrderHom.curry (f.comp (coeOrderHom _))) (fun _ _ ↦ f.monotone bot_le), rfl⟩

private def profileToPrism {A Q T : Type*} [Preorder A] [Preorder Q] [Preorder T]
    (c : T) (g : {g : WithBot A →o (Q →o T) // g ⊥ = OrderHom.const Q c}) :
    WithBot (A × Q) →o T :=
  withBotExtend c (OrderHom.curry.symm (g.val.comp (coeOrderHom A))) (fun x ↦ by
    have h := g.val.monotone (bot_le : (⊥ : WithBot A) ≤ ↑x.1)
    rw [g.property] at h
    exact h x.2)

/-- Currying the nonempty part of a product leaves the actual empty-face label scalar. -/
def prismCurry {A Q T : Type*} [Preorder A] [Preorder Q] [Preorder T] :
    (WithBot (A × Q) →o T) ≃
      Σ c : T, {g : WithBot A →o (Q →o T) // g ⊥ = OrderHom.const Q c} where
  toFun f := ⟨f ⊥, prismToProfile f⟩
  invFun g := profileToPrism g.1 g.2
  left_inv f := by
    ext x
    cases x using WithBot.recBotCoe <;> rfl
  right_inv := by
    rintro ⟨c, g, hg⟩
    change (⟨c, prismToProfile (profileToPrism c ⟨g, hg⟩)⟩ :
      Σ c : T, {g : WithBot A →o (Q →o T) // g ⊥ = OrderHom.const Q c}) = ⟨c, ⟨g, hg⟩⟩
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    ext x q
    cases x using WithBot.recBotCoe with
    | bot => exact DFunLike.congr_fun hg.symm q
    | coe x => rfl

/-- Profile form of a full prism labeling, with the bottom profile constrained to be constant. -/
def prismProfileEquiv (k : ℕ) {Q T : Type*} [Preorder Q] [Preorder T] :
    (PrismModel k Q →o T) ≃
      Σ c : T, {f : Face k →o (Q →o T) // f Face.bottom = OrderHom.const Q c} := by
  let e := (faceWithBotIso k).arrowCongr (OrderIso.refl (Q →o T))
  refine prismCurry.trans (Equiv.sigmaCongrRight fun c ↦ ?_)
  exact Equiv.subtypeEquiv e.toEquiv (fun f ↦ Iff.rfl)

/-- The order-polytope label subtype and a bundled order hom record the same map. -/
def labelOrderHomEquiv {A : Type*} [Preorder A] (q : ℕ) :
    Labels (fun a b : A ↦ a ≤ b) (q + 1) ≃ (A →o Fin (q + 1)) where
  toFun f := ⟨f.val, fun a b ↦ f.property a b⟩
  invFun f := ⟨f, fun _ _ h ↦ f.monotone h⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Real order-polytope dilates have exactly these bundled integer labelings. -/
def latticeOrderHomEquiv {A : Type*} [Preorder A] (q : ℕ) :
    LatticePoints (fun a b : A ↦ a ≤ b) q ≃ (A →o Fin (q + 1)) :=
  (latticePointsEquivLabels _ q).trans (labelOrderHomEquiv q)

section Counts
variable {Q T : Type*} [Fintype Q] [Fintype T] [Preorder Q] [Preorder T]

/-- The trace sum over all boundary profiles in the product model. -/
def productTrace (Q T : Type*) [Fintype Q] [Fintype T] [Preorder Q] [Preorder T] (k : ℕ) :
    ℕ :=
  ∑ a : Q →o T, ∑ b : {b : Q →o T // a ≤ b},
    ((gram : Matrix (StateInterval a b.val) _ ℕ) ^ (k + 1)).trace

/-- The trace sum over a scalar lower label and an upper profile in the prism model. -/
def prismTrace (Q T : Type*) [Fintype Q] [Fintype T] [Preorder Q] [Preorder T] (k : ℕ) :
    ℕ :=
  ∑ c : T, ∑ b : {b : Q →o T // OrderHom.const Q c ≤ b},
    ((gram : Matrix (StateInterval (OrderHom.const Q c) b.val) _ ℕ) ^ (k + 1)).trace

/-- The complete product-poset transfer for an arbitrary finite fiber and target. -/
theorem card_product_transfer (k : ℕ) :
    Fintype.card (Face k × Q →o T) = productTrace Q T k := by
  rw [productTrace, Fintype.card_congr OrderHom.curry.toEquiv]
  exact card_faceOrderHom k

/-- The complete prism-face transfer sums one scalar label for the empty face. -/
theorem card_prism_transfer (k : ℕ) :
    Fintype.card (PrismModel k Q →o T) = prismTrace Q T k := by
  rw [prismTrace, Fintype.card_congr (prismProfileEquiv k), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.card_congr (fixedBottomEquiv k (OrderHom.const Q c))]
  exact card_topBoundary k (OrderHom.const Q c)

end Counts

/-- Ehrhart count for the pyramid face model, for every integer dilation including zero. -/
theorem card_pyramid_latticePoints (k q : ℕ) :
    Fintype.card (LatticePoints (fun a b : Pyramid k ↦ a ≤ b) q) =
      productTrace (Fin 2) (Fin (q + 1)) k := by
  rw [Fintype.card_congr (latticeOrderHomEquiv q)]
  exact card_product_transfer (Q := Fin 2) (T := Fin (q + 1)) k

/-- Ehrhart count for the prism face model, for every integer dilation including zero. -/
theorem card_prism_latticePoints (k q : ℕ) :
    Fintype.card (LatticePoints (fun a b : Prism k ↦ a ≤ b) q) =
      prismTrace SegmentFace (Fin (q + 1)) k := by
  rw [Fintype.card_congr (latticeOrderHomEquiv q)]
  exact card_prism_transfer (Q := SegmentFace) (T := Fin (q + 1)) k

end PolytopalProducts

