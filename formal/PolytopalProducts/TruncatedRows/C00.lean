import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_0 : FastTriples.advancedRow graph 25 0 = 1857 := by decide +kernel
#print axioms row_0

theorem row_1 : FastTriples.advancedRow graph 25 1 = 1573 := by decide +kernel
#print axioms row_1

theorem row_2 : FastTriples.advancedRow graph 25 2 = 1519 := by decide +kernel
#print axioms row_2

theorem row_3 : FastTriples.advancedRow graph 25 3 = 1466 := by decide +kernel
#print axioms row_3

end PolytopalProducts.Truncated
