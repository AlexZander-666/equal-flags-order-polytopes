import PolytopalProducts.TruncatedGraph
import PolytopalProducts.FastTripleEvaluator

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3 PolytopalProducts.Geometry PolytopalProducts.OrderFaces

theorem physical_rows : fCoefficient (ExposedFace body) 25 =
    ∑ i : Fin 64, FastTriples.advancedRow graph 25 i := by
  rw [← fCoefficient_iso faceIso, FastTriples.sum_advancedRow_eq_signatures graphModel graphBipartite
      (by decide : 0 < 25) (by decide : 25 + 5 = 30)]
  apply fCoefficient_eq_card_signatures graphModel
  have hc := pinned_card
  change Fintype.card (Option (Option FaceCode)) = 30 at hc
  simp only [Fintype.card_option] at hc
  omega

#print axioms physical_rows
end PolytopalProducts.Truncated


