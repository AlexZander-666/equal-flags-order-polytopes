import Codim3PhysicalCoefficients
import PolytopalProducts.TruncatedRows.Sum
import PolytopalProducts.TruncatedReadout
import PolytopalProducts.TruncatedIntrinsicFlags
import PolytopalProducts.TruncatedDimension

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3 PolytopalProducts.Geometry PolytopalProducts.OrderFaces

theorem truncated_f25 : fCoefficient (ExposedFace body) 25 = 35944 :=
  physical_rows.trans numerical_sum

theorem equal_flag_values_different_f25 :
    flagVector graph = flagVector hexGraph ∧
    fCoefficient (ExposedFace body) 25 ≠ fCoefficient (ExposedFace hexagonalPyramid) 25 := by
  refine ⟨complete_flag_values.1.trans complete_flag_values.2.symm, ?_⟩
  rw [truncated_f25,hexagonal_pyramid_f25]
  decide

theorem same_flags_different_order_polytopes :
    Module.finrank ℝ (vectorSpan ℝ body) = 3 ∧
    Module.finrank ℝ (vectorSpan ℝ hexagonalPyramid) = 3 ∧
    eight (actualCount (ExposedFace body)) = eight (actualCount (ExposedFace hexagonalPyramid)) ∧
    fCoefficient (ExposedFace body) 25 = 35944 ∧
    fCoefficient (ExposedFace hexagonalPyramid) 25 = 35946 :=
  ⟨both_dimensions.1,both_dimensions.2,
   actual_complete_flags.1.trans actual_complete_flags.2.symm,truncated_f25,hexagonal_pyramid_f25⟩

#print axioms same_flags_different_order_polytopes
#print axioms truncated_f25
#print axioms equal_flag_values_different_f25
end PolytopalProducts.Truncated
