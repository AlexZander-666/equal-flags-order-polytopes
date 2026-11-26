import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_48 : FastTriples.advancedRow graph 25 48 = 85 := by decide +kernel
#print axioms row_48

theorem row_49 : FastTriples.advancedRow graph 25 49 = 72 := by decide +kernel
#print axioms row_49

theorem row_50 : FastTriples.advancedRow graph 25 50 = 62 := by decide +kernel
#print axioms row_50

theorem row_51 : FastTriples.advancedRow graph 25 51 = 53 := by decide +kernel
#print axioms row_51

end PolytopalProducts.Truncated
