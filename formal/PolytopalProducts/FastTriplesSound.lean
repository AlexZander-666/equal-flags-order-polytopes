import PolytopalProducts.IndexedClosures
import PolytopalProducts.IntervalMerge
import PolytopalProducts.FastTriples

/-! Readout of the bit masks used by interval contraction. -/

noncomputable section

namespace PolytopalProducts.Codim3.FastTriples

open PolytopalProducts.OrderFaces

variable {n m : ℕ} {g : GraphData n m} {V : Type*} [PartialOrder V]

theorem testBit_mask {A : Type*} (xs : List A) (p : A → Bool) (index : A → ℕ) (j : ℕ) :
    (mask xs p index).testBit j = true ↔ ∃ a ∈ xs, p a = true ∧ index a = j := by
  induction xs with
  | nil => simp [mask]
  | cons x xs ih =>
    change (if p x then (2^index x) ||| mask xs p index else mask xs p index).testBit j = true ↔ _
    cases hp : p x
    · simp [hp, ih]
    · simp [hp, Nat.testBit_two_pow, Bool.or_eq_true, ih]

theorem predecessors_testBit (r : Vector Nat n) (v i : Fin n) :
    (predecessors r v).testBit i.val = arrow r i v := by
  apply Bool.eq_iff_iff.mpr
  rw [predecessors, testBit_mask]
  constructor
  · rintro ⟨a, _, ha, he⟩
    rwa [show a = i from Fin.ext he] at ha
  · exact fun h ↦ ⟨i, List.mem_finRange i, h, rfl⟩

/-- The relation presented by one packed matrix. -/
def matrixRelation (r : Vector Nat n) (a b : Fin n) : Prop := arrow r a b = true

theorem matrixRelation_add (r : Vector Nat n) (e : Fin n × Fin n) (a b : Fin n) :
    matrixRelation (add r e) a b ↔ addArrow (matrixRelation r) e.2 e.1 a b :=
  arrow_add r e a b

theorem matrixRelation_trans (model : GraphRealization V g) (s : List (Fin m)) :
    ∀ ⦃x y z : Fin n⦄, matrixRelation (close g s) x y →
      matrixRelation (close g s) y z → matrixRelation (close g s) x z := by
  exact fun {x y z} h₁ h₂ ↦ (close_matches model s x z).mpr
    (reach_trans _ ((close_matches model s x y).mp h₁) ((close_matches model s y z).mp h₂))

theorem representatives_testBit (r : Vector Nat n) (i : Fin n) :
    (representatives r).testBit i.val = true ↔ i ∈ classLeaders (matrixRelation r) := by
  rw [representatives, testBit_mask, mem_classLeaders]
  have hex (a : Fin n) :
      (!(List.finRange n).any fun j ↦ decide (j < a) && arrow r a j && arrow r j a) = true ↔
        ∀ j < a, ¬equivalentIn (matrixRelation r) a j := by
    rw [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
    constructor
    · intro h j hj hsame
      apply h
      apply List.any_eq_true.mpr
      exact ⟨j, List.mem_finRange j, by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using
          (show (j < a ∧ arrow r a j = true) ∧ arrow r j a = true from
            ⟨⟨hj, hsame.1⟩, hsame.2⟩)⟩
    · intro h hsome
      obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hsome
      have h' : (j < a ∧ arrow r a j = true) ∧ arrow r j a = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hj
      exact h j h'.1.1 ⟨h'.1.2, h'.2⟩
  constructor
  · rintro ⟨a, _, hp, he⟩
    have ha : a = i := Fin.ext he
    subst a
    exact (hex i).mp hp
  · exact fun hi ↦ ⟨i, List.mem_finRange i, (hex i).mpr hi, rfl⟩

theorem commonMask_testBit (r : Vector Nat n) (e : Fin n × Fin n) (i : Fin n) :
    (commonMask (fun v ↦ r[v.val]) (predecessors r) e).testBit i.val = true ↔
      i ∈ intervalIndices (matrixRelation r) e.1 e.2 := by
  simp only [commonMask, Nat.testBit_and, predecessors_testBit, Bool.and_eq_true,
    mem_intervalIndices, matrixRelation, arrow]

theorem tight_add_iff (model : GraphRealization V g) (s : List (Fin m))
    (e : Fin n × Fin n) (i : Fin m) :
    i ∈ tight g (add (close g s) e) ↔
      i ∈ tight g (close g s) ∨
        let r := matrixRelation (close g s)
        g.arcs[i.val].1 ∈ intervalIndices r e.1 e.2 ∧
          g.arcs[i.val].2 ∈ intervalIndices r e.1 e.2 := by
  let r := matrixRelation (close g s)
  let a := g.arcs[i.val].1
  let b := g.arcs[i.val].2
  have hab : r a b := by
    apply (close_matches model s a b).mpr
    apply reach_of_le
    have hh : (model.arc i).val.1 ≤ (model.arc i).val.2 := (model.arc i).property.le
    rw [model.endpoints i] at hh
    exact hh
  have hb : addArrow r e.2 e.1 a b := Or.inl hab
  simp only [tight, List.mem_filter, List.mem_finRange, true_and]
  change matrixRelation (add (close g s) e) b a ↔ r b a ∨ _
  rw [matrixRelation_add]
  have he := equivalentIn_addArrow_iff (matrixRelation_trans model s)
    (a := e.1) (b := e.2) (x := a) (y := b)
  change addArrow r e.2 e.1 b a ↔ r b a ∨
    a ∈ intervalIndices r e.1 e.2 ∧ b ∈ intervalIndices r e.1 e.2
  change (addArrow r e.2 e.1 a b ∧ addArrow r e.2 e.1 b a) ↔
    (r a b ∧ r b a) ∨ ((r e.1 a ∧ r a e.2) ∧ (r e.1 b ∧ r b e.2)) at he
  simpa only [hb, hab, true_and, mem_intervalIndices] using he

section Counts

open scoped Classical

private theorem bitIndices_card {word : ℕ} (S : Finset (Fin n))
    (h : ∀ i : Fin n, word.testBit i.val = true ↔ i ∈ S)
    (he : ∀ k ≥ n, word.testBit k = false) :
    word.bitIndices.length = S.card := by
  have same : word.bitIndices.toFinset = S.map Fin.valEmbedding := by
    ext k
    rw [List.mem_toFinset, Nat.mem_bitIndices, Finset.mem_map]
    by_cases hk : k < n
    · exact (h ⟨k, hk⟩).trans
        ⟨fun hi ↦ ⟨⟨k, hk⟩, hi, rfl⟩,
          fun ⟨i, hi, hEq⟩ ↦ (show i = (⟨k, hk⟩ : Fin n) from Fin.ext hEq) ▸ hi⟩
    · constructor
      · intro ht
        rw [he k (le_of_not_gt hk)] at ht
        contradiction
      · rintro ⟨i, -, hi⟩
        exact (hk (hi ▸ i.isLt)).elim
  rw [← Finset.card_map (f := Fin.valEmbedding), ← same]
  exact (List.toFinset_card_of_nodup Nat.bitIndices_nodup).symm

private theorem representatives_bounded (r : Vector Nat n) (k : ℕ) (hk : n ≤ k) :
    (representatives r).testBit k = false := by
  apply Bool.eq_false_iff.mpr
  unfold representatives
  simp only [ne_eq, testBit_mask]
  rintro ⟨i, -, -, h⟩
  omega

private theorem rowSet_eq_image (r : Vector Nat n) :
    rowSet r = Finset.univ.image (fun i : Fin n ↦ r[i.val]) := by
  ext q
  rw [rowSet, List.mem_toFinset, Vector.mem_toList_iff, Vector.mem_iff_getElem, Finset.mem_image]
  exact ⟨fun ⟨i, hi, he⟩ ↦ ⟨⟨i, hi⟩, Finset.mem_univ _, he⟩,
    fun ⟨i, _, he⟩ ↦ ⟨i.val, i.isLt, he⟩⟩

theorem leaders_length (r : Vector Nat n) :
    (representatives r).bitIndices.length = (classLeaders (matrixRelation r)).card :=
  bitIndices_card _ (representatives_testBit _) (representatives_bounded _)

theorem representatives_length (model : GraphRealization V g) (s : List (Fin m)) :
    (representatives (close g s)).bitIndices.length = (rowSet (close g s)).card := by
  rw [bitIndices_card (classLeaders (matrixRelation (close g s))) (representatives_testBit _)
    (representatives_bounded _), rowSet_eq_image]
  apply card_classLeaders_eq_card_image
  intro x y
  exact (and_congr (close_matches model s x y) (close_matches model s y x)).trans
    (same_row_iff model s x y).symm

/-- The third equality reduces the number of classes by the number of represented
old classes in its interval, minus the one surviving class. -/
theorem row_count_after_reverse (model : GraphRealization V g) (s : List (Fin m)) (j : Fin m) :
    let r := close g s
    let e := g.arcs[j.val]
    let C := commonMask (fun v ↦ r[v.val]) (predecessors r) e
    (rowSet (close g (j :: s))).card =
      (representatives r).bitIndices.length -
        ((C &&& representatives r).bitIndices.length - 1) := by
  let r := close g s
  let e := g.arcs[j.val]
  let R := matrixRelation r
  let I := intervalIndices R e.1 e.2
  let L := classLeaders R
  let C := commonMask (fun v ↦ r[v.val]) (predecessors r) e
  let reps := representatives r
  change (rowSet (add r e)).card = reps.bitIndices.length - ((C &&& reps).bitIndices.length - 1)
  have ht := matrixRelation_trans model s
  have hI : I.Nonempty := ⟨e.1, (mem_intervalIndices _ _ _).mpr (by
    have hedge : (model.arc j).val.1 ≤ (model.arc j).val.2 := (model.arc j).property.le
    rw [model.endpoints j] at hedge
    exact ⟨(close_matches model s _ _).mpr (reach_of_le _ le_rfl),
      (close_matches model s _ _).mpr (reach_of_le _ hedge)⟩)⟩
  have relationEq : matrixRelation (add r e) = addArrow R e.2 e.1 := by
    funext x y
    exact propext (matrixRelation_add r e x y)
  have hi : (C &&& reps).bitIndices.length = (L ∩ I).card := by
    apply bitIndices_card
    · intro v
      rw [Nat.testBit_and, Bool.and_eq_true, Finset.mem_inter]
      exact (and_congr (commonMask_testBit r e v) (representatives_testBit r v)).trans and_comm
    · intro k hk
      rw [Nat.testBit_and, representatives_bounded _ _ hk, Bool.and_false]
  have hOld : reps.bitIndices.length = L.card :=
    bitIndices_card L (representatives_testBit _) (representatives_bounded _)
  have hNew : (rowSet (add r e)).card = (classLeaders (addArrow R e.2 e.1)).card := by
    change (rowSet (close g (j :: s))).card = _
    rw [← representatives_length model]
    exact (bitIndices_card _ (representatives_testBit _) (representatives_bounded _)).trans
      (congrArg (fun t ↦ (classLeaders t).card) relationEq)
  have hp : (L ∩ I).Nonempty := by
    let q := I.min' hI
    have hq : q ∈ I := I.min'_mem hI
    refine ⟨q, Finset.mem_inter.mpr ⟨(mem_classLeaders q).mpr ?_, hq⟩⟩
    intro a ha he
    have hh := (interval_congr ht he).mp ((mem_intervalIndices _ _ _).mp hq)
    exact (not_lt_of_ge (I.min'_le _ ((mem_intervalIndices _ _ _).mpr hh))) ha
  have hformula : (classLeaders (addArrow R e.2 e.1)).card = (L \ I).card + 1 :=
    card_classLeaders_addArrow ht hI
  rw [hNew, hformula, hi, hOld]
  have hd := Finset.card_sdiff_add_card_inter L I
  have hpos := Finset.card_pos.mpr hp
  omega

end Counts

theorem close_eq_of_same_seed (model : GraphRealization V g) {s t : List (Fin m)}
    (h : s.toFinset = t.toFinset) : close g s = close g t := by
  have hS : actualSeed model s = actualSeed model t := congrArg (Finset.map model.arc.toEmbedding) h
  apply Vector.ext
  intro i hi
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · apply Bool.eq_iff_iff.mpr
    change arrow (close g s) ⟨i, hi⟩ ⟨j, hj⟩ = true ↔
      arrow (close g t) ⟨i, hi⟩ ⟨j, hj⟩ = true
    rw [close_matches model, close_matches model, hS]
  · exact (close_no_high_bits model s ⟨i, hi⟩ j (le_of_not_gt hj)).trans
      (close_no_high_bits model t ⟨i, hi⟩ j (le_of_not_gt hj)).symm

private theorem testBit_collectSide (xs : List ℕ) (side : ℕ → ℕ) (k : ℕ) :
    (collectSide xs side).testBit k = true ↔ ∃ x ∈ xs, (side x).testBit k = true := by
  induction xs with
  | nil => simp [collectSide]
  | cons x xs ih =>
    change (side x ||| collectSide xs side).testBit k = true ↔ _
    simp only [Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
    aesop

theorem bySource_testBit (g : GraphData n m) (v : ℕ) (e : Fin m) :
    (bySource g v).testBit e.val = true ↔ g.arcs[e.val].1.val = v := by
  rw [bySource, testBit_mask]
  constructor
  · rintro ⟨a, _, ha, hv⟩
    obtain rfl : a = e := Fin.ext hv
    exact beq_iff_eq.mp ha
  · exact fun h ↦ ⟨e, List.mem_finRange e, beq_iff_eq.mpr h, rfl⟩

theorem byTarget_testBit (g : GraphData n m) (v : ℕ) (e : Fin m) :
    (byTarget g v).testBit e.val = true ↔ g.arcs[e.val].2.val = v := by
  rw [byTarget, testBit_mask]
  constructor
  · rintro ⟨a, _, ha, hv⟩
    obtain rfl : a = e := Fin.ext hv
    exact beq_iff_eq.mp ha
  · exact fun h ↦ ⟨e, List.mem_finRange e, beq_iff_eq.mpr h, rfl⟩

/-- This word marks exactly the covers whose two endpoints lie in an interval. -/
theorem intervalArcMask_testBit (g : GraphData n m) (word : ℕ) (e : Fin m) :
    (collectSide word.bitIndices (bySource g) &&&
       collectSide word.bitIndices (byTarget g)).testBit e.val = true ↔
      word.testBit g.arcs[e.val].1.val = true ∧ word.testBit g.arcs[e.val].2.val = true := by
  rw [Nat.testBit_and, Bool.and_eq_true, testBit_collectSide, testBit_collectSide]
  apply and_congr
  · simp only [bySource_testBit, Nat.mem_bitIndices]
    exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ hx, fun h ↦ ⟨_, h, rfl⟩⟩
  · simp only [byTarget_testBit, Nat.mem_bitIndices]
    exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ hx, fun h ↦ ⟨_, h, rfl⟩⟩

/-- The column-wise interval update uses the same one-reversed-edge closure
as the row update, without constructing the whole new vector. -/
theorem predecessors_add (r : Vector Nat n) (e : Fin n × Fin n) (v : Fin n) :
    predecessors (add r e) v =
      if arrow r e.1 v then predecessors r v ||| predecessors r e.2 else predecessors r v := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · let i : Fin n := ⟨k,hk⟩
    apply Bool.eq_iff_iff.mpr
    change (predecessors (add r e) v).testBit i.val = true ↔ _
    rw [predecessors_testBit, arrow_add]
    cases hv : arrow r e.1 v
    · simp only [Bool.false_eq_true, and_false, or_false, ↓reduceIte]
      rw [← predecessors_testBit]
    · simp only [and_true, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
      rw [← predecessors_testBit, ← predecessors_testBit]
  · have h (w : Vector Nat n) (a : Fin n) : (predecessors w a).testBit k = false := by
      apply Bool.eq_false_iff.mpr
      unfold predecessors
      simp only [ne_eq, testBit_mask]
      rintro ⟨i, -, -, he⟩
      exact hk (he ▸ i.isLt)
    rw [h]
    split <;> simp only [Nat.testBit_or, h, Bool.or_self]

private theorem headD_eq_minimum {l : List ℕ} (hord : l.SortedLT) {q : ℕ}
    (hq : q ∈ l) (hmin : ∀ x ∈ l, q ≤ x) : l.headD 0 = q := by
  cases l with
  | nil => simp at hq
  | cons x xs =>
    change x = q
    apply le_antisymm _ (hmin x List.mem_cons_self)
    rcases List.mem_cons.mp hq with he | ht
    · exact he.ge
    · exact ((List.pairwise_cons.mp hord.pairwise).1 _ ht).le

/-- The mask stores exactly the representatives after the interval contraction. -/
theorem representatives_add (r : Vector Nat n) (e : Fin n × Fin n)
    (ht : ∀ ⦃x y z⦄, matrixRelation r x y → matrixRelation r y z → matrixRelation r x z)
    (hI : (intervalIndices (matrixRelation r) e.1 e.2).Nonempty) :
    representatives (add r e) =
      mergeRepresentatives (representatives r)
        (commonMask (fun i ↦ r[i.val]) (predecessors r) e) := by
  classical
  let I := intervalIndices (matrixRelation r) e.1 e.2
  let q := I.min' hI
  let L := classLeaders (matrixRelation r)
  let prev := representatives r
  let C := commonMask (fun i ↦ r[i.val]) (predecessors r) e
  let J := C &&& prev
  change representatives (add r e) = mergeRepresentatives prev C
  have hq : q ∈ I := I.min'_mem hI
  have hqL : q ∈ L := by
    apply (mem_classLeaders q).mpr
    intro x hx hEq
    have hh := (interval_congr ht hEq).mp ((mem_intervalIndices _ _ _).mp hq)
    exact (not_lt_of_ge (I.min'_le _ ((mem_intervalIndices _ _ _).mpr hh))) hx
  have hj (v : Fin n) : J.testBit v.val = true ↔ v ∈ I ∧ v ∈ L := by
    rw [show J = C &&& prev from rfl, Nat.testBit_and, Bool.and_eq_true]
    exact and_congr (commonMask_testBit r e v) (representatives_testBit r v)
  have hqJ : q.val ∈ J.bitIndices := Nat.mem_bitIndices.mpr ((hj q).mpr ⟨hq, hqL⟩)
  have hmin : ∀ x ∈ J.bitIndices, q.val ≤ x := by
    intro x hx
    have hb := Nat.mem_bitIndices.mp hx
    have hxN : x < n := by
      by_contra hn
      have hf := representatives_bounded r x (le_of_not_gt hn)
      change (C &&& prev).testBit x = true at hb
      rw [Nat.testBit_and, show prev.testBit x = false from hf, Bool.and_false] at hb
      contradiction
    exact I.min'_le _ ((hj ⟨x,hxN⟩).mp hb).1
  have hhead := headD_eq_minimum Nat.bitIndices_sorted hqJ hmin
  have hnon : prev &&& C ≠ 0 := by
    intro hh
    have h : J = 0 := (Nat.land_comm _ _).trans hh
    rw [h, Nat.bitIndices_zero] at hqJ
    exact List.not_mem_nil hqJ
  unfold mergeRepresentatives
  rw [if_neg hnon, Nat.land_comm prev C, hhead]
  have hr : matrixRelation (add r e) = addArrow (matrixRelation r) e.2 e.1 := by
    funext x y
    exact propext (matrixRelation_add r e x y)
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · let v : Fin n := ⟨k,hk⟩
    apply Bool.eq_iff_iff.mpr
    change (representatives (add r e)).testBit v.val = true ↔ _
    rw [representatives_testBit, hr, classLeaders_addArrow ht hI]
    change v ∈ (L \ I) ∪ {q} ↔ (prev ^^^ J ||| 2^q.val).testBit v.val = true
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, Nat.testBit_or,
      Nat.testBit_xor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, Fin.val_inj]
    have hL : prev.testBit v.val = true ↔ v ∈ L := representatives_testBit r v
    have hJ := hj v
    cases hp : prev.testBit v.val <;> cases hjv : J.testBit v.val <;>
      simp_all [Bool.xor] <;> exact eq_comm
  · have hn := le_of_not_gt hk
    rw [representatives_bounded _ _ hn, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow,
      show prev.testBit k = false from representatives_bounded r k hn]
    have hqk : q.val ≠ k := fun he ↦ hk (he ▸ q.isLt)
    simp [hqk, representatives_bounded r k hn, prev]

end PolytopalProducts.Codim3.FastTriples
