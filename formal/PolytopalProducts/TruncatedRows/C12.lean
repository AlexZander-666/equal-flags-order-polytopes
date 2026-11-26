import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_12 : FastTriples.advancedRow graph 25 12 = 1118 := by decide +kernel
#print axioms row_12

theorem row_13 : FastTriples.advancedRow graph 25 13 = 1073 := by decide +kernel
#print axioms row_13

theorem row_14 : FastTriples.advancedRow graph 25 14 = 1026 := by decide +kernel
#print axioms row_14

theorem row_15 : FastTriples.advancedRow graph 25 15 = 983 := by decide +kernel
#print axioms row_15

end PolytopalProducts.Truncated
