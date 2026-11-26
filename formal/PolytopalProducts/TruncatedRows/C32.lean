import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_32 : FastTriples.advancedRow graph 25 32 = 415 := by decide +kernel
#print axioms row_32

theorem row_33 : FastTriples.advancedRow graph 25 33 = 387 := by decide +kernel
#print axioms row_33

theorem row_34 : FastTriples.advancedRow graph 25 34 = 360 := by decide +kernel
#print axioms row_34

theorem row_35 : FastTriples.advancedRow graph 25 35 = 334 := by decide +kernel
#print axioms row_35

end PolytopalProducts.Truncated
