import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_4 : FastTriples.advancedRow graph 25 4 = 1465 := by decide +kernel
#print axioms row_4

theorem row_5 : FastTriples.advancedRow graph 25 5 = 1415 := by decide +kernel
#print axioms row_5

theorem row_6 : FastTriples.advancedRow graph 25 6 = 1363 := by decide +kernel
#print axioms row_6

theorem row_7 : FastTriples.advancedRow graph 25 7 = 1312 := by decide +kernel
#print axioms row_7

end PolytopalProducts.Truncated
