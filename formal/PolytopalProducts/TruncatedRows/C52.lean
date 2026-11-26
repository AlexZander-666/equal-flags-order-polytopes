import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_52 : FastTriples.advancedRow graph 25 52 = 43 := by decide +kernel
#print axioms row_52

theorem row_53 : FastTriples.advancedRow graph 25 53 = 35 := by decide +kernel
#print axioms row_53

theorem row_54 : FastTriples.advancedRow graph 25 54 = 28 := by decide +kernel
#print axioms row_54

theorem row_55 : FastTriples.advancedRow graph 25 55 = 21 := by decide +kernel
#print axioms row_55

end PolytopalProducts.Truncated
