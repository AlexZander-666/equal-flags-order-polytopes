import PolytopalProducts.Codim3Data
import PolytopalProducts.CoefficientTransport

noncomputable section

namespace PolytopalProducts.Codim3

open Polygon PolytopalProducts.Geometry PolytopalProducts.OrderFaces

local instance : DecidableLE SegmentFace := fun a b ↦ by
  cases a <;> cases b <;> change Decidable (SegmentFace.rel _ _) <;>
    simp only [SegmentFace.rel] <;> infer_instance

def cubePoint (i : Fin 30) : Pinned CubeFace :=
  (#v[⊥,
    interior CubeFace (⊥),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 0, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 0, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 1, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 1, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 0, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 0, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 1, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 1, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 0, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.whole, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 0, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.whole, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 0, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 1, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.endpoint 1, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.endpoint 1, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 0, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.whole, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.whole, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 1, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.whole, SegmentFace.endpoint 0)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 0, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.endpoint 0, SegmentFace.whole, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.endpoint 1, SegmentFace.whole, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.endpoint 1, SegmentFace.whole)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.whole, SegmentFace.endpoint 1)),
    interior CubeFace (↑(SegmentFace.whole, SegmentFace.whole, SegmentFace.whole)),
    high CubeFace])[i.val]

def hexPoint (i : Fin 30) : Pinned (Pyramid 5) :=
  (#v[⊥,
    interior (Pyramid 5) ((FaceOrder.Face.bottom, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 0, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 1, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 2, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 3, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 4, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 5, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.bottom, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 0, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 5, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 0, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 1, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 1, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 2, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 2, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 3, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 3, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 4, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 4, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.vertex 5, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.top, 0)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 0, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 5, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 1, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 2, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 3, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.edge 4, 1)),
    interior (Pyramid 5) ((FaceOrder.Face.top, 1)),
    high (Pyramid 5)])[i.val]


set_option maxHeartbeats 2000000 in
theorem cubePoint_injective : Function.Injective cubePoint := by
  change ∀ a b : Fin 30, cubePoint a = cubePoint b → a = b
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem hexPoint_injective : Function.Injective hexPoint := by
  change ∀ a b : Fin 30, hexPoint a = hexPoint b → a = b
  decide +kernel

theorem card_pinnedCube : Fintype.card (Pinned CubeFace) = 30 := by
  change Fintype.card (Option (Option (Option (SegmentFace × (SegmentFace × SegmentFace))))) = _
  norm_num [card_segmentFace]

theorem card_pinnedHex : Fintype.card (Pinned (Pyramid 5)) = 30 := by
  change Fintype.card (Option (Option (Pyramid 5))) = _
  simp only [Fintype.card_option, card_pyramid]

def cubePointEquiv : Fin 30 ≃ Pinned CubeFace :=
  Equiv.ofBijective cubePoint ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨cubePoint_injective, by simp [card_pinnedCube]⟩)

def hexPointEquiv : Fin 30 ≃ Pinned (Pyramid 5) :=
  Equiv.ofBijective hexPoint ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hexPoint_injective, by simp [card_pinnedHex]⟩)

set_option maxHeartbeats 2000000 in
theorem cubeOrderMatches :
    ∀ i j, arrow cubeGraph.order i j = true ↔ cubePoint i ≤ cubePoint j := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem hexOrderMatches :
    ∀ i j, arrow hexGraph.order i j = true ↔ hexPoint i ≤ hexPoint j := by
  decide +kernel

def strictIndex (g : GraphData n m) (a b : Fin n) : Bool :=
  arrow g.order a b && !(arrow g.order b a)

def coverIndex (g : GraphData n m) (a b : Fin n) : Bool :=
  strictIndex g a b &&
    !(List.finRange n).any fun c ↦ strictIndex g a c && strictIndex g c b

def listedIndex (g : GraphData n m) (a b : Fin n) : Bool :=
  (List.finRange m).any fun e ↦ g.arcs[e.val] == (a, b)

theorem coverIndex_iff {V : Type*} [PartialOrder V] {g : GraphData n m}
    (p : Fin n ≃ Pinned V)
    (he : ∀ i j, arrow g.order i j = true ↔ p i ≤ p j) (a b : Fin n) :
    coverIndex g a b = true ↔ p a ⋖ p b := by
  have hs (x y : Fin n) : strictIndex g x y = true ↔ p x < p y := by
    rw [strictIndex, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, lt_iff_le_not_ge]
    exact and_congr (he x y) (Bool.eq_false_iff.trans (not_congr (he y x)))
  have hno :
      (!(List.finRange n).any fun c ↦ strictIndex g a c && strictIndex g c b) = true ↔
      ∀ ⦃z : Pinned V⦄, p a < z → ¬z < p b := by
    rw [Bool.not_eq_true_eq_eq_false]
    constructor
    · intro hh z h₁ h₂
      let i := p.symm z
      have hx : strictIndex g a i = true := (hs a i).mpr (by simpa [i] using h₁)
      have hy : strictIndex g i b = true := (hs i b).mpr (by simpa [i] using h₂)
      have hab : (strictIndex g a i && strictIndex g i b) = true := by
        rw [Bool.and_eq_true]
        exact ⟨hx, hy⟩
      have ht : (List.finRange n).any (fun c ↦ strictIndex g a c && strictIndex g c b) = true :=
        List.any_eq_true.mpr ⟨i, List.mem_finRange _, hab⟩
      exact Bool.false_ne_true (hh.symm.trans ht)
    · intro hh
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨i, _, hi⟩ := List.any_eq_true.mp ht
      obtain ⟨hx, hy⟩ := (by simpa only [Bool.and_eq_true] using hi : strictIndex g a i = true ∧ strictIndex g i b = true)
      exact hh ((hs a i).mp hx) ((hs i b).mp hy)
  rw [coverIndex, Bool.and_eq_true]
  exact and_congr (hs a b) hno

set_option maxHeartbeats 3000000 in
theorem cubeCoverCheck : ∀ i j, listedIndex cubeGraph i j = coverIndex cubeGraph i j := by
  decide +kernel

set_option maxHeartbeats 3000000 in
theorem hexCoverCheck : ∀ i j, listedIndex hexGraph i j = coverIndex hexGraph i j := by
  decide +kernel

theorem cubeArcs_injective : Function.Injective (fun e : Fin 64 ↦ cubeGraph.arcs[e.val]) := by
  change ∀ a b : Fin 64, cubeGraph.arcs[a.val] = cubeGraph.arcs[b.val] → a = b
  decide +kernel

theorem hexArcs_injective : Function.Injective (fun e : Fin 64 ↦ hexGraph.arcs[e.val]) := by
  change ∀ a b : Fin 64, hexGraph.arcs[a.val] = hexGraph.arcs[b.val] → a = b
  decide +kernel

theorem cubeOrder_bounded : ∀ i : Fin 30, cubeGraph.order[i.val] < 2^30 := by decide +kernel

theorem hexOrder_bounded : ∀ i : Fin 30, hexGraph.order[i.val] < 2^30 := by decide +kernel

/-- A directed graph table with its actual index identification and cover enumeration. -/
structure GraphRealization (V : Type*) [PartialOrder V] (g : GraphData n m) where
  point : Fin n ≃ Pinned V
  arc : Fin m ≃ Arc V
  low : point g.low = ⊥
  high : point g.high = OrderFaces.high V
  order : ∀ i j, arrow g.order i j = true ↔ point i ≤ point j
  endpoints : ∀ e, (arc e).val = (point g.arcs[e.val].1, point g.arcs[e.val].2)
  bounded : ∀ i : Fin n, g.order[i.val] < 2^n

private def arcEquiv {V : Type*} [PartialOrder V] (g : GraphData n m)
    (p : Fin n ≃ Pinned V) (ho : ∀ i j, arrow g.order i j = true ↔ p i ≤ p j)
    (hc : ∀ i j, listedIndex g i j = coverIndex g i j)
    (hj : Function.Injective (fun e : Fin m ↦ g.arcs[e.val])) : Fin m ≃ Arc V := by
  let f (e : Fin m) : Arc V := ⟨(p g.arcs[e.val].1, p g.arcs[e.val].2), by
    apply (coverIndex_iff p ho _ _).mp
    rw [← hc]
    exact List.any_eq_true.mpr ⟨e, List.mem_finRange _, beq_iff_eq.mpr (Prod.eta _)⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply hj
    exact Prod.ext (p.injective (congrArg (fun a : Arc V ↦ a.val.1) h))
      (p.injective (congrArg (fun a : Arc V ↦ a.val.2) h))
  · intro a
    obtain ⟨i, hi⟩ := p.surjective a.val.1
    obtain ⟨j, hj⟩ := p.surjective a.val.2
    have h : listedIndex g i j = true := by
      rw [hc, coverIndex_iff p ho, hi, hj]
      exact a.property
    obtain ⟨e, _, he⟩ := List.any_eq_true.mp h
    have heu := beq_iff_eq.mp he
    exact ⟨e, Subtype.ext (Prod.ext ((congrArg (fun u ↦ p u.1) heu).trans hi)
      ((congrArg (fun u ↦ p u.2) heu).trans hj))⟩

def cubeGraphRealization : GraphRealization CubeFace cubeGraph where
  point := cubePointEquiv
  arc := arcEquiv cubeGraph cubePointEquiv cubeOrderMatches cubeCoverCheck cubeArcs_injective
  low := rfl
  high := rfl
  order := cubeOrderMatches
  endpoints _ := rfl
  bounded := cubeOrder_bounded

def hexGraphRealization : GraphRealization (Pyramid 5) hexGraph where
  point := hexPointEquiv
  arc := arcEquiv hexGraph hexPointEquiv hexOrderMatches hexCoverCheck hexArcs_injective
  low := rfl
  high := rfl
  order := hexOrderMatches
  endpoints _ := rfl
  bounded := hexOrder_bounded

end PolytopalProducts.Codim3
