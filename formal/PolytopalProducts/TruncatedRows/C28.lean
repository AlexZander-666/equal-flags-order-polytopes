import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_28 : FastTriples.advancedRow graph 25 28 = 502 := by decide +kernel
#print axioms row_28

theorem row_29 : FastTriples.advancedRow graph 25 29 = 472 := by decide +kernel
#print axioms row_29

theorem row_30 : FastTriples.advancedRow graph 25 30 = 442 := by decide +kernel
#print axioms row_30

theorem row_31 : FastTriples.advancedRow graph 25 31 = 413 := by decide +kernel
#print axioms row_31

end PolytopalProducts.Truncated
