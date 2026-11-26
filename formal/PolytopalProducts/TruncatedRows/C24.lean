import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_24 : FastTriples.advancedRow graph 25 24 = 632 := by decide +kernel
#print axioms row_24

theorem row_25 : FastTriples.advancedRow graph 25 25 = 597 := by decide +kernel
#print axioms row_25

theorem row_26 : FastTriples.advancedRow graph 25 26 = 565 := by decide +kernel
#print axioms row_26

theorem row_27 : FastTriples.advancedRow graph 25 27 = 532 := by decide +kernel
#print axioms row_27

end PolytopalProducts.Truncated
