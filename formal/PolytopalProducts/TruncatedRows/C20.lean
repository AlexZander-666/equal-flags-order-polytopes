import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_20 : FastTriples.advancedRow graph 25 20 = 778 := by decide +kernel
#print axioms row_20

theorem row_21 : FastTriples.advancedRow graph 25 21 = 739 := by decide +kernel
#print axioms row_21

theorem row_22 : FastTriples.advancedRow graph 25 22 = 701 := by decide +kernel
#print axioms row_22

theorem row_23 : FastTriples.advancedRow graph 25 23 = 667 := by decide +kernel
#print axioms row_23

end PolytopalProducts.Truncated
