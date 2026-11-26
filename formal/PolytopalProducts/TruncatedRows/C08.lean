import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_8 : FastTriples.advancedRow graph 25 8 = 1312 := by decide +kernel
#print axioms row_8

theorem row_9 : FastTriples.advancedRow graph 25 9 = 1262 := by decide +kernel
#print axioms row_9

theorem row_10 : FastTriples.advancedRow graph 25 10 = 1211 := by decide +kernel
#print axioms row_10

theorem row_11 : FastTriples.advancedRow graph 25 11 = 1165 := by decide +kernel
#print axioms row_11

end PolytopalProducts.Truncated
