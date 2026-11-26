import PolytopalProducts.PackedClosures

/-! A numeric kernel pilot which caches the first two reversed covers. -/

namespace PolytopalProducts.Codim3.FastTriples

def mask {A : Type*} (xs : List A) (p : A → Bool) (index : A → ℕ) : ℕ :=
  xs.foldr (fun x m ↦ if p x then (2^index x) ||| m else m) 0

def predecessors {n : ℕ} (r : Vector Nat n) (v : Fin n) : ℕ :=
  mask (List.finRange n) (arrow r · v) Fin.val

def representatives {n : ℕ} (r : Vector Nat n) : ℕ :=
  mask (List.finRange n)
    (fun i ↦ !(List.finRange n).any fun j ↦
      decide (j < i) && arrow r i j && arrow r j i) Fin.val

def bySource {n m : ℕ} (g : GraphData n m) (v : ℕ) : ℕ :=
  mask (List.finRange m) (fun e ↦ g.arcs[e.val].1.val == v) Fin.val

def byTarget {n m : ℕ} (g : GraphData n m) (v : ℕ) : ℕ :=
  mask (List.finRange m) (fun e ↦ g.arcs[e.val].2.val == v) Fin.val

def collectSide (xs : List ℕ) (side : ℕ → ℕ) : ℕ :=
  xs.foldr (fun i u ↦ side i ||| u) 0

def row {n m : ℕ} (g : GraphData n m) (d : ℕ) (i : Fin m) : ℕ :=
  let sourceTable : Vector ℕ n := Vector.ofFn (fun v ↦ bySource g v.val)
  let targetTable : Vector ℕ n := Vector.ofFn (fun v ↦ byTarget g v.val)
  let source (v : ℕ) := sourceTable.toArray[v]?.getD 0
  let target (v : ℕ) := targetTable.toArray[v]?.getD 0
  let initial := add g.order g.arcs[i.val]
  ((List.finRange m).filter fun j ↦ i < j).foldl (fun count j ↦
    let prior := add initial g.arcs[j.val]
    let reps := representatives prior
    let cls := reps.bitIndices.length
    if cls < d + 2 || arrow prior g.high g.low then count
    else
      let before := mask (tight g prior) (fun _ ↦ true) Fin.val
      let columns : Vector ℕ n := Vector.ofFn (predecessors prior)
      let addCount := ((List.finRange m).filter fun k ↦ j < k).countP fun k ↦
        let e := g.arcs[k.val]
        let common := prior[e.1.val] &&& columns[e.2.val]
        let loss := (common &&& reps).bitIndices.length - 1
        if cls - loss != d + 2 || (common.testBit g.low.val && common.testBit g.high.val) then false
        else
          let xs := common.bitIndices
          let newly := collectSide xs source &&& collectSide xs target
          (((before ||| newly).bitIndices.take 3) == [i.val, j.val, k.val])
      count + addCount) 0

end PolytopalProducts.Codim3.FastTriples

namespace PolytopalProducts.Codim3.FastTriples

def mergeRepresentatives (previous common : ℕ) : ℕ :=
  let merged := previous &&& common
  if merged = 0 then previous
  else (previous ^^^ merged) ||| 2^((merged.bitIndices).headD 0)

def commonMask (rows cols : Fin n → ℕ) (edge : Fin n × Fin n) : ℕ :=
  rows edge.1 &&& cols edge.2

def advancedRow {n m : ℕ} (g : GraphData n m) (d : ℕ) (i : Fin m) : ℕ :=
  let sourceTable : Vector ℕ n := Vector.ofFn (fun v ↦ bySource g v.val)
  let targetTable : Vector ℕ n := Vector.ofFn (fun v ↦ byTarget g v.val)
  let source (v : ℕ) := sourceTable.toArray[v]?.getD 0
  let target (v : ℕ) := targetTable.toArray[v]?.getD 0
  let edgesIn (u : ℕ) :=
    let xs := u.bitIndices
    collectSide xs source &&& collectSide xs target
  let initial := add g.order g.arcs[i.val]
  let firstColumns : Vector ℕ n := Vector.ofFn (predecessors initial)
  let firstReps := representatives initial
  let firstTight := mask (tight g initial) (fun _ ↦ true) Fin.val
  let firstPins := arrow initial g.high g.low
  ((List.finRange m).filter fun j ↦ i < j).foldl (fun count j ↦
    let e := g.arcs[j.val]
    let interval := commonMask (fun v ↦ initial[v.val]) (fun v ↦ firstColumns[v.val]) e
    let reps := mergeRepresentatives firstReps interval
    let cls := reps.bitIndices.length
    let mergedPins := interval.testBit g.low.val && interval.testBit g.high.val
    if cls < d + 2 || firstPins || mergedPins then count
    else
      let before := firstTight ||| edgesIn interval
      let rows (v : Fin n) :=
        if arrow initial v e.2 then initial[v.val] ||| initial[e.1.val] else initial[v.val]
      let cols (v : Fin n) :=
        if arrow initial e.1 v then firstColumns[v.val] ||| firstColumns[e.2.val]
        else firstColumns[v.val]
      let addCount := ((List.finRange m).filter fun k ↦ j < k).countP fun k ↦
        let common := commonMask rows cols g.arcs[k.val]
        let loss := (common &&& reps).bitIndices.length - 1
        if cls - loss != d + 2 || (common.testBit g.low.val && common.testBit g.high.val) then false
        else
          ((before ||| edgesIn common) % (2^(k.val+1))) == 2^i.val + 2^j.val + 2^k.val
      count + addCount) 0

end PolytopalProducts.Codim3.FastTriples
