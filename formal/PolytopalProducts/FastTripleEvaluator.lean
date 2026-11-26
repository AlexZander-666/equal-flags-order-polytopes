import PolytopalProducts.TriplesCount

/-! Reflected test for one sorted three-cover candidate. -/

noncomputable section

namespace PolytopalProducts.Codim3.FastTriples

open PolytopalProducts.OrderFaces

variable {n m : ℕ} {V : Type*} [PartialOrder V] {g : GraphData n m}

def cachedEdgesIn (g : GraphData n m) (bits : ℕ) : ℕ :=
  let sourceTable : Vector ℕ n := Vector.ofFn (fun v ↦ bySource g v.val)
  let targetTable : Vector ℕ n := Vector.ofFn (fun v ↦ byTarget g v.val)
  let source (v : ℕ) := sourceTable.toArray[v]?.getD 0
  let target (v : ℕ) := targetTable.toArray[v]?.getD 0
  collectSide bits.bitIndices source &&& collectSide bits.bitIndices target

private theorem collectSide_congr {l : List ℕ} {f h : ℕ → ℕ}
    (eq : ∀ i ∈ l, f i = h i) : collectSide l f = collectSide l h := by
  induction l with
  | nil => rfl
  | cons i t ih =>
    change f i ||| collectSide t f = h i ||| collectSide t h
    rw [eq i (by simp), ih (fun j hj ↦ eq j (List.mem_cons_of_mem _ hj))]

private theorem vector_lookup (p : ℕ → ℕ) (i : ℕ) (hi : i < n) :
    (Vector.ofFn (fun j : Fin n ↦ p j.val)).toArray[i]?.getD 0 = p i := by
  have h : i < (Vector.ofFn (fun j : Fin n ↦ p j.val)).toArray.size := by simpa using hi
  rw [Array.getElem?_eq_getElem h, Vector.getElem_toArray, Vector.getElem_ofFn]
  rfl

private theorem cachedEdgesIn_eq (g : GraphData n m) (bits : ℕ)
    (h : ∀ i ∈ bits.bitIndices, i < n) :
    cachedEdgesIn g bits =
      (collectSide bits.bitIndices (bySource g) &&& collectSide bits.bitIndices (byTarget g)) := by
  unfold cachedEdgesIn
  dsimp only
  rw [collectSide_congr (fun i hi ↦ vector_lookup (bySource g) i (h i hi)),
    collectSide_congr (fun i hi ↦ vector_lookup (byTarget g) i (h i hi))]

private theorem old_interval_bounded (model : GraphRealization V g) (s : List (Fin m))
    (e : Fin n × Fin n) :
    ∀ i ∈ (commonMask (fun v ↦ (close g s)[v.val]) (predecessors (close g s)) e).bitIndices,
      i < n := by
  intro k hk
  by_contra hn
  have h := Nat.mem_bitIndices.mp hk
  simp only [commonMask, Nat.testBit_and,
    close_no_high_bits model s e.1 k (le_of_not_gt hn), Bool.false_and] at h
  contradiction

private theorem actual_interval_nonempty (model : GraphRealization V g) (s : List (Fin m))
    (j : Fin m) :
    (intervalIndices (matrixRelation (close g s)) g.arcs[j.val].1 g.arcs[j.val].2).Nonempty := by
  let e := g.arcs[j.val]
  refine ⟨e.1, (mem_intervalIndices _ _ _).mpr ⟨?_, ?_⟩⟩
  · exact (close_matches model s _ _).mpr (reach_of_le _ le_rfl)
  · have he : (model.arc j).val.1 ≤ (model.arc j).val.2 := (model.arc j).property.le
    rw [model.endpoints j] at he
    exact (close_matches model s _ _).mpr (reach_of_le _ he)

/-- One branch of the optimized accumulator, with both earlier reverse covers cached. -/
def advancedCheck (g : GraphData n m) (d : ℕ) (i j k : Fin m) : Bool :=
  let initial := add g.order g.arcs[i.val]
  let firstColumns : Vector ℕ n := Vector.ofFn (predecessors initial)
  let firstReps := representatives initial
  let firstTight := tightWord g initial
  let firstPins := arrow initial g.high g.low
  let e := g.arcs[j.val]
  let interval := commonMask (fun v ↦ initial[v.val]) (fun v ↦ firstColumns[v.val]) e
  let reps := mergeRepresentatives firstReps interval
  let cls := reps.bitIndices.length
  let mergedPins := interval.testBit g.low.val && interval.testBit g.high.val
  if cls < d+2 || firstPins || mergedPins then false
  else
    let before := firstTight ||| cachedEdgesIn g interval
    let rows (v : Fin n) :=
      if arrow initial v e.2 then initial[v.val] ||| initial[e.1.val] else initial[v.val]
    let cols (v : Fin n) :=
      if arrow initial e.1 v then firstColumns[v.val] ||| firstColumns[e.2.val]
      else firstColumns[v.val]
    let common := commonMask rows cols g.arcs[k.val]
    let loss := (common &&& reps).bitIndices.length - 1
    if cls - loss != d+2 || (common.testBit g.low.val && common.testBit g.high.val) then false
    else
      ((before ||| cachedEdgesIn g common) % 2^(k.val+1)) == 2^i.val+2^j.val+2^k.val

private theorem split_candidate (cls loss d : ℕ) (pins finalPins check : Bool)
    {P : Prop} (hp : check = true ↔ P) :
    (if cls < d+2 || pins then false
      else if cls-loss != d+2 || finalPins then false else check) = true ↔
      (pins || finalPins) = false ∧ cls-loss = d+2 ∧ P := by
  by_cases h : cls-loss=d+2
  · have hn : ¬cls<d+2 := by omega
    cases pins <;> cases finalPins <;> simp [h,hn,hp]
  · by_cases hn : cls<d+2 <;> cases pins <;> cases finalPins <;> simp [h,hn]

theorem advancedCheck_sound (model : GraphRealization V g) {d : ℕ} (hd : 0 < d)
    {i j k : Fin m} (hij : i<j) (hjk : j<k) :
    advancedCheck g d i j k = true ↔ ({i,j,k} : Finset (Fin m)) ∈ canonicalSeeds g d := by
  let r₁ := close g [i]
  let e := g.arcs[j.val]
  let r₂ := close g [j,i]
  let f := g.arcs[k.val]
  let r₃ := close g [k,j,i]
  let I := commonMask (fun v ↦ r₁[v.val]) (predecessors r₁) e
  let C := commonMask (fun v ↦ r₂[v.val]) (predecessors r₂) f
  let reps := mergeRepresentatives (representatives r₁) I
  let bad := I.testBit g.low.val && I.testBit g.high.val
  let commonPins := C.testBit g.low.val && C.testBit g.high.val
  let cutoff := reps.bitIndices.length
  let loss := (C &&& reps).bitIndices.length - 1
  have rowsExact (v : Fin n) :
      r₂[v.val] = if arrow r₁ v e.2 then r₁[v.val] ||| r₁[e.1.val] else r₁[v.val] := by
    change (add r₁ e)[v.val] = _
    exact Vector.getElem_ofFn _
  have colsExact (v : Fin n) :
      predecessors r₂ v =
        if arrow r₁ e.1 v then predecessors r₁ v ||| predecessors r₁ e.2 else predecessors r₁ v :=
    predecessors_add r₁ e v
  have hrep : representatives r₂ = reps :=
    representatives_add r₁ e (matrixRelation_trans model [i]) (actual_interval_nonempty model [i] j)
  have hbefore : tightWord g r₂ = tightWord g r₁ ||| cachedEdgesIn g I := by
    rw [cachedEdgesIn_eq _ _ (old_interval_bounded model [i] e)]
    exact tightWord_add model [i] e
  have hafter : tightWord g r₃ = tightWord g r₂ ||| cachedEdgesIn g C := by
    rw [cachedEdgesIn_eq _ _ (old_interval_bounded model [j,i] f)]
    exact tightWord_add model [j,i] f
  have hpins1 : arrow r₂ g.high g.low = (arrow r₁ g.high g.low || bad) := by
    have he := pins_add model [i] e
    change arrow r₂ g.high g.low =
      (arrow r₁ g.high g.low || (I.testBit g.high.val && I.testBit g.low.val)) at he
    rw [Bool.and_comm] at he
    exact he
  have hpins2 : arrow r₃ g.high g.low = (arrow r₂ g.high g.low || commonPins) := by
    have he := pins_add model [j,i] f
    change arrow r₃ g.high g.low =
      (arrow r₂ g.high g.low || (C.testBit g.high.val && C.testBit g.low.val)) at he
    rw [Bool.and_comm] at he
    exact he
  have hcount : (rowSet r₃).card = cutoff-loss := by
    change (rowSet r₃).card = reps.bitIndices.length - ((C &&& reps).bitIndices.length - 1)
    rw [← hrep]
    exact row_count_after_reverse model [j,i] k
  have advancedEq : advancedCheck g d i j k =
      (if cutoff < d+2 || arrow r₂ g.high g.low then false
       else if cutoff-loss != d+2 || commonPins then false
       else ((tightWord g r₃ % 2^(k.val+1)) == 2^i.val+2^j.val+2^k.val)) := by
    unfold advancedCheck
    simp only [Vector.getElem_ofFn]
    let C' := commonMask
      (fun v ↦ if arrow r₁ v e.2 then r₁[v.val] ||| r₁[e.1.val] else r₁[v.val])
      (fun v ↦ if arrow r₁ e.1 v then predecessors r₁ v ||| predecessors r₁ e.2
        else predecessors r₁ v) f
    have hC : C' = C :=
      congrArg₂ (fun rows cols ↦ commonMask rows cols f) (funext rowsExact).symm
        (funext colsExact).symm
    change
      (if cutoff < d+2 || arrow r₁ g.high g.low || bad then false
      else if cutoff - ((C' &&& reps).bitIndices.length - 1) != d+2 ||
        (C'.testBit g.low.val && C'.testBit g.high.val) then false
      else (((tightWord g r₁ ||| cachedEdgesIn g I) ||| cachedEdgesIn g C') % 2^(k.val+1)) ==
        2^i.val+2^j.val+2^k.val) = _
    rw [Bool.or_assoc, ← hpins1, hC, ← hbefore, ← hafter]
  rw [sorted_triple_spec model hd hij hjk, advancedEq]
  change _ ↔ arrow r₃ g.high g.low = false ∧ (rowSet r₃).card = d+2 ∧ canonical g r₃ = [i,j,k]
  rw [hpins2, hcount]
  have hp := tightWord_prefix g r₃ hij hjk
  exact split_candidate _ _ _ _ _ _ (beq_iff_eq.trans hp)

private theorem countP_finRange_filter {p q : Fin m → Bool} :
    ((List.finRange m).filter p).countP q = ∑ i : Fin m, if p i && q i then 1 else 0 := by
  classical
  rw [List.countP_eq_length_filter, List.filter_filter]
  have hN := (List.nodup_finRange m).filter (fun i ↦ q i && p i)
  rw [← List.toFinset_card_of_nodup hN]
  rw [List.toFinset_filter, List.toFinset_finRange, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp [Bool.and_comm]

private theorem advancedRow_list (g : GraphData n m) (d : ℕ) (i : Fin m) :
    advancedRow g d i =
      (((List.finRange m).filter fun j ↦ i < j).map fun j ↦
        ((List.finRange m).filter fun k ↦ j < k).countP (advancedCheck g d i j)).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]
  unfold advancedRow
  apply congrArg (fun f ↦ ((List.finRange m).filter fun j ↦ i < j).foldl f 0)
  funext count j
  unfold advancedCheck cachedEdgesIn tightWord
  dsimp only
  split <;> simp only [*, List.countP_false, Function.const_apply, add_zero]

theorem advancedRow_sound (model : GraphRealization V g) {d : ℕ} (hd : 0 < d) (i : Fin m) :
    advancedRow g d i =
      ∑ j : Fin m, ∑ k : Fin m,
        if i < j ∧ j < k ∧ ({i,j,k} : Finset (Fin m)) ∈ canonicalSeeds g d then 1 else 0 := by
  classical
  rw [advancedRow_list, ← List.sum_toFinset _ ((List.nodup_finRange m).filter _),
    List.toFinset_filter, List.toFinset_finRange, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [if_pos (by simpa using hij), countP_finRange_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hjk : j < k
    · simp only [hij, hjk, decide_true, Bool.true_and, true_and]
      have h := advancedCheck_sound model hd hij hjk
      by_cases ha : advancedCheck g d i j k = true
      · simp only [if_pos ha, if_pos (h.mp ha)]
      · simp only [if_neg ha, if_neg (fun hh ↦ ha (h.mpr hh))]
    · simp [hjk]
  · simp [hij]

/-- The optimized counts enumerate the actual distinct equality signatures. -/
theorem sum_advancedRow_eq_signatures [Fintype V] (model : GraphRealization V g)
    (coloring : OrderedBipartite g) {d : ℕ} (hd : 0 < d) (hn : d+5=n) :
    (∑ i : Fin m, advancedRow g d i) = (signatures g d).card := by
  rw [card_signatures_eq_canonicalSeeds model coloring hn,
    card_canonicalSeeds_eq_card_acceptedTriples, card_acceptedTriples_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ advancedRow_sound model hd i)

end PolytopalProducts.Codim3.FastTriples
