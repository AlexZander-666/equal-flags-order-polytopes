import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_16 : FastTriples.advancedRow graph 25 16 = 940 := by decide +kernel
#print axioms row_16

theorem row_17 : FastTriples.advancedRow graph 25 17 = 898 := by decide +kernel
#print axioms row_17

theorem row_18 : FastTriples.advancedRow graph 25 18 = 857 := by decide +kernel
#print axioms row_18

theorem row_19 : FastTriples.advancedRow graph 25 19 = 817 := by decide +kernel
#print axioms row_19

end PolytopalProducts.Truncated
