import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_60 : FastTriples.advancedRow graph 25 60 = 3 := by decide +kernel
#print axioms row_60

theorem row_61 : FastTriples.advancedRow graph 25 61 = 1 := by decide +kernel
#print axioms row_61

theorem row_62 : FastTriples.advancedRow graph 25 62 = 0 := by decide +kernel
#print axioms row_62

theorem row_63 : FastTriples.advancedRow graph 25 63 = 0 := by decide +kernel
#print axioms row_63

end PolytopalProducts.Truncated
