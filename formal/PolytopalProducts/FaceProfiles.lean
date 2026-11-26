import PolytopalProducts.Transfer
import Polygon.FaceOrder

/-! The cyclic face model, with arbitrary finite label posets instead of a chain. -/

noncomputable section
open scoped BigOperators

namespace PolytopalProducts

open Polygon.FaceOrder

instance finiteOrderHom {A B : Type*} [Fintype A] [Fintype B] [Preorder A] [Preorder B] :
    Fintype (A →o B) := by
  classical
  exact Fintype.ofInjective (fun f : A →o B ↦ (f : A → B)) DFunLike.coe_injective

/-- The inclusively bounded states used by a fixed boundary pair. -/
abbrev StateInterval {J : Type*} [Preorder J] (a b : J) := {x : J // a ≤ x ∧ x ≤ b}

/-- The selected top and the labels on the cyclic part of the boundary. -/
abbrev TopBoundary {J : Type*} [Preorder J] (k : ℕ) (a : J) :=
  Σ b : {b : J // a ≤ b}, CrownLabeling (StateInterval a b.val) k

theorem bottom_le_face {k : ℕ} (a : Face k) : Face.bottom ≤ a := by
  cases a <;> trivial

theorem face_le_top {k : ℕ} (a : Face k) : a ≤ Face.top := by
  cases a <;> trivial

private def toTopBoundary {J : Type*} [Preorder J] {k : ℕ} (f : Face k →o J) :
    TopBoundary k (f Face.bottom) := by
  let state (x : Face k) : StateInterval (f Face.bottom) (f Face.top) :=
    ⟨f x, f.monotone (bottom_le_face x), f.monotone (face_le_top x)⟩
  refine ⟨⟨f Face.top, f.monotone (bottom_le_face Face.top)⟩,
    fun i ↦ state (Face.vertex i), fun i ↦ ⟨state (Face.edge i), ?_, ?_⟩⟩
  · exact f.monotone ((vertex_le_edge_iff i i).mpr (Or.inl rfl))
  · exact f.monotone ((vertex_le_edge_iff (i + 1) i).mpr (Or.inr rfl))

private def fromTopBoundary {J : Type*} [Preorder J] {k : ℕ} {a : J} :
    TopBoundary k a → (Face k →o J)
  | ⟨⟨b, hab⟩, v, e⟩ => by
    let label : Face k → J
      | .bottom => a
      | .top => b
      | .vertex i => (v i).val
      | .edge i => (e i).val.val
    refine ⟨label, ?_⟩
    have vlo (i) : a ≤ (v i).val := (v i).property.1
    have vhi (i) : (v i).val ≤ b := (v i).property.2
    have elo (i) : a ≤ (e i).val.val := (e i).val.property.1
    have ehi (i) : (e i).val.val ≤ b := (e i).val.property.2
    intro x y h
    cases x <;> cases y <;>
      simp_all [label, le_iff_faceLE, faceLE]
    rcases h with rfl | rfl
    · exact (e _).property.1
    · exact (e _).property.2

/-- Polygon-face maps with fixed bottom label are exactly one bounded crown per top label. -/
def fixedBottomEquiv {J : Type*} [Preorder J] (k : ℕ) (a : J) :
    {f : Face k →o J // f Face.bottom = a} ≃ TopBoundary k a where
  toFun f := f.property ▸ toTopBoundary f.val
  invFun data := ⟨fromTopBoundary data, by rcases data with ⟨⟨_, _⟩, _, _⟩; rfl⟩
  left_inv := by
    rintro ⟨f, h⟩
    subst a
    apply Subtype.ext
    ext x
    cases x <;> rfl
  right_inv := by
    rintro ⟨⟨b, hab⟩, v, e⟩
    rfl

/-- Polygon-face maps are the disjoint sum of their fixed-bottom fibers. -/
def boundaryEquiv {J : Type*} [Preorder J] (k : ℕ) :
    (Face k →o J) ≃ (Σ a : J, TopBoundary k a) :=
  (Equiv.sigmaFiberEquiv (fun f : Face k →o J ↦ f Face.bottom)).symm.trans
    (Equiv.sigmaCongrRight (fixedBottomEquiv k))

variable {J : Type*} [Fintype J] [Preorder J] [DecidableLE J] [DecidableEq J]

theorem card_topBoundary (k : ℕ) (a : J) :
    Fintype.card (TopBoundary k a) =
      ∑ b : {b : J // a ≤ b}, ((gram : Matrix (StateInterval a b.val) _ ℕ) ^ (k + 1)).trace := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl fun b _ ↦ card_crownLabeling (J := StateInterval a b.val) k

/-- The sum over all intervals counts polygon-face labelings in any finite state poset. -/
theorem card_faceOrderHom (k : ℕ) :
    Fintype.card (Face k →o J) =
      ∑ a : J, ∑ b : {b : J // a ≤ b},
        ((gram : Matrix (StateInterval a b.val) _ ℕ) ^ (k + 1)).trace := by
  rw [Fintype.card_congr (boundaryEquiv k), Fintype.card_sigma]
  exact Finset.sum_congr rfl fun a _ ↦ card_topBoundary k a

end PolytopalProducts

