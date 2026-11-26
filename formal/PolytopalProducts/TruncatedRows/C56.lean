import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_56 : FastTriples.advancedRow graph 25 56 = 21 := by decide +kernel
#print axioms row_56

theorem row_57 : FastTriples.advancedRow graph 25 57 = 15 := by decide +kernel
#print axioms row_57

theorem row_58 : FastTriples.advancedRow graph 25 58 = 10 := by decide +kernel
#print axioms row_58

theorem row_59 : FastTriples.advancedRow graph 25 59 = 6 := by decide +kernel
#print axioms row_59

end PolytopalProducts.Truncated
