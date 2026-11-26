import PolytopalProducts.TruncatedData
import PolytopalProducts.FastTriples

namespace PolytopalProducts.Truncated
open PolytopalProducts.Codim3
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem row_36 : FastTriples.advancedRow graph 25 36 = 307 := by decide +kernel
#print axioms row_36

theorem row_37 : FastTriples.advancedRow graph 25 37 = 282 := by decide +kernel
#print axioms row_37

theorem row_38 : FastTriples.advancedRow graph 25 38 = 260 := by decide +kernel
#print axioms row_38

theorem row_39 : FastTriples.advancedRow graph 25 39 = 237 := by decide +kernel
#print axioms row_39

end PolytopalProducts.Truncated
