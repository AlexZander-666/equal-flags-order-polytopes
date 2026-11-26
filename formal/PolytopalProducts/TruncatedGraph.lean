import PolytopalProducts.TruncatedGeometry
import PolytopalProducts.TriplesCount

noncomputable section
namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3 PolytopalProducts.OrderFaces

def pinnedPoint (i : Fin 30) : Pinned FaceCode :=
  (#v[⊥,interior FaceCode ⟨0⟩,interior FaceCode ⟨1⟩,interior FaceCode ⟨2⟩,interior FaceCode ⟨3⟩,interior FaceCode ⟨4⟩,interior FaceCode ⟨5⟩,interior FaceCode ⟨6⟩,interior FaceCode ⟨7⟩,interior FaceCode ⟨8⟩,interior FaceCode ⟨9⟩,interior FaceCode ⟨10⟩,interior FaceCode ⟨11⟩,interior FaceCode ⟨12⟩,interior FaceCode ⟨13⟩,interior FaceCode ⟨14⟩,interior FaceCode ⟨15⟩,interior FaceCode ⟨16⟩,interior FaceCode ⟨17⟩,interior FaceCode ⟨18⟩,interior FaceCode ⟨19⟩,interior FaceCode ⟨20⟩,interior FaceCode ⟨21⟩,interior FaceCode ⟨22⟩,interior FaceCode ⟨23⟩,interior FaceCode ⟨24⟩,interior FaceCode ⟨25⟩,interior FaceCode ⟨26⟩,interior FaceCode ⟨27⟩,high FaceCode])[i.val]

theorem pinned_card : Fintype.card (Pinned FaceCode) = 30 := by
  have sz : Fintype.card FaceCode = 28 :=
    (Fintype.card_congr (show FaceCode ≃ Fin 28 from ⟨FaceCode.index,FaceCode.mk,by intro x; rfl,by intro x; rfl⟩)).trans (Fintype.card_fin _)
  change Fintype.card (Option (Option FaceCode)) = 30
  simp [Fintype.card_option,sz]

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def pinnedEquiv : Fin 30 ≃ Pinned FaceCode :=
  Equiv.ofBijective pinnedPoint ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨by change ∀ a b : Fin 30, pinnedPoint a = pinnedPoint b → a = b; decide +kernel,
     by simp [pinned_card]⟩)

theorem graphOrder : ∀ i j, arrow graph.order i j = true ↔ pinnedPoint i ≤ pinnedPoint j := by
  decide +kernel

theorem graphCover : ∀ i j, listedIndex graph i j = coverIndex graph i j := by decide +kernel

theorem graphArcInjective : Function.Injective (fun e : Fin 64 ↦ graph.arcs[e.val]) := by
  change ∀ a b : Fin 64, graph.arcs[a.val] = graph.arcs[b.val] → a = b
  decide +kernel

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


def graphModel : GraphRealization FaceCode graph where
  point := pinnedEquiv
  arc := arcEquiv graph pinnedEquiv graphOrder graphCover graphArcInjective
  low := rfl
  high := rfl
  order := graphOrder
  endpoints _ := rfl
  bounded := by decide +kernel

def graphBipartite : OrderedBipartite graph where
  color := hexColor
  oriented := by decide +kernel
  color_ne := by decide +kernel

#print axioms graphModel
#print axioms graphBipartite
end PolytopalProducts.Truncated

