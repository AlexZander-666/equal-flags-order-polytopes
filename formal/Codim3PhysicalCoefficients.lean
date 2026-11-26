import Codim3ComputedSums
import PolytopalProducts.FastTripleEvaluator

namespace PolytopalProducts.Codim3

open PolytopalProducts.OrderFaces PolytopalProducts.Geometry

theorem cube_f25 : fCoefficient (ExposedFace cube) 25 = 35948 := by
  rw [cube_fCoefficient_eq_signatures,
    ← FastTriples.sum_advancedRow_eq_signatures cubeGraphRealization cubeOrderedBipartite
      (by decide : 0 < 25) (by decide : 25 + 5 = 30)]
  exact cube_numerical_sum

theorem hexagonal_pyramid_f25 : fCoefficient (ExposedFace hexagonalPyramid) 25 = 35946 := by
  rw [hex_pyramid_fCoefficient_eq_signatures,
    ← FastTriples.sum_advancedRow_eq_signatures hexGraphRealization hexOrderedBipartite
      (by decide : 0 < 25) (by decide : 25 + 5 = 30)]
  exact hex_numerical_sum

theorem physical_f25_ne :
    fCoefficient (ExposedFace cube) 25 ≠ fCoefficient (ExposedFace hexagonalPyramid) 25 := by
  rw [cube_f25, hexagonal_pyramid_f25]
  decide

end PolytopalProducts.Codim3

#print axioms PolytopalProducts.Codim3.cube_f25
#print axioms PolytopalProducts.Codim3.hexagonal_pyramid_f25
#print axioms PolytopalProducts.Codim3.physical_f25_ne
