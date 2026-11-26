import PolytopalProducts.Reach

/-! How one reverse cover changes a transitive preorder. -/

namespace PolytopalProducts.OrderFaces

variable {A : Type*} {r : A → A → Prop}

def equivalentIn (r : A → A → Prop) (x y : A) : Prop := r x y ∧ r y x

/-- Reversing a cover only merges equality classes intersecting its interval;
the same statement applies if the augmented edge already joins comparable classes. -/
theorem equivalentIn_addArrow_iff (ht : ∀ ⦃x y z : A⦄, r x y → r y z → r x z)
    {a b x y : A} :
    equivalentIn (addArrow r b a) x y ↔
      equivalentIn r x y ∨ ((r a x ∧ r x b) ∧ (r a y ∧ r y b)) := by
  change (r x y ∨ (r x b ∧ r a y)) ∧ (r y x ∨ (r y b ∧ r a x)) ↔ _
  constructor
  · rintro ⟨hxy | ⟨hxb, hay⟩, hyx | ⟨hyb, hax⟩⟩
    · exact Or.inl ⟨hxy, hyx⟩
    · exact Or.inr ⟨⟨hax, ht hxy hyb⟩, ⟨ht hax hxy, hyb⟩⟩
    · exact Or.inr ⟨⟨ht hay hyx, hxb⟩, ⟨hay, ht hyx hxb⟩⟩
    · exact Or.inr ⟨⟨hax, hxb⟩, ⟨hay, hyb⟩⟩
  · rintro (⟨hxy, hyx⟩ | ⟨⟨hax, hxb⟩, ⟨hay, hyb⟩⟩)
    · exact ⟨Or.inl hxy, Or.inl hyx⟩
    · exact ⟨Or.inr ⟨hxb, hay⟩, Or.inr ⟨hyb, hax⟩⟩

/-- Interval membership is constant on the old equality classes. -/
theorem interval_congr (ht : ∀ ⦃x y z : A⦄, r x y → r y z → r x z)
    {a b x y : A} (h : equivalentIn r x y) :
    (r a x ∧ r x b) ↔ (r a y ∧ r y b) :=
  ⟨fun ⟨hax, hxb⟩ ↦ ⟨ht hax h.1, ht h.2 hxb⟩,
    fun ⟨hay, hyb⟩ ↦ ⟨ht hay h.2, ht h.1 hyb⟩⟩

section Finite

open scoped Classical

variable [Fintype A] [LinearOrder A]

/-- The least variable index in each equality class. -/
noncomputable def classLeaders (r : A → A → Prop) : Finset A :=
  Finset.univ.filter fun x ↦ ∀ y < x, ¬equivalentIn r x y

/-- The indices in the closed interval of a possibly nonsymmetric preorder. -/
noncomputable def intervalIndices (r : A → A → Prop) (a b : A) : Finset A :=
  Finset.univ.filter fun x ↦ r a x ∧ r x b

@[simp] lemma mem_classLeaders (x : A) :
    x ∈ classLeaders r ↔ ∀ y < x, ¬equivalentIn r x y := by
  simp [classLeaders]

omit [LinearOrder A] in
@[simp] lemma mem_intervalIndices (a b x : A) :
    x ∈ intervalIndices r a b ↔ r a x ∧ r x b := by
  simp [intervalIndices]

/-- Updating the representatives needs only one set difference and the minimum of the interval. -/
theorem classLeaders_addArrow (ht : ∀ ⦃x y z : A⦄, r x y → r y z → r x z)
    {a b : A} (hI : (intervalIndices r a b).Nonempty) :
    classLeaders (addArrow r b a) =
      (classLeaders r \ intervalIndices r a b) ∪ {(intervalIndices r a b).min' hI} := by
  classical
  ext x
  let I := intervalIndices r a b
  let q := I.min' hI
  have hq : q ∈ I := I.min'_mem hI
  rw [mem_classLeaders]
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  change (∀ y < x, ¬equivalentIn (addArrow r b a) x y) ↔ (x ∈ classLeaders r ∧ x ∉ I) ∨ x = q
  by_cases hx : x ∈ I
  · have he (y : A) : equivalentIn (addArrow r b a) x y ↔ y ∈ I := by
      rw [equivalentIn_addArrow_iff ht]
      have hx' := (mem_intervalIndices a b x).mp hx
      exact ⟨fun e ↦ (mem_intervalIndices a b y).mpr
        (e.elim (fun h ↦ (interval_congr ht h).mp hx') And.right),
        fun hy ↦ Or.inr ⟨hx', (mem_intervalIndices a b y).mp hy⟩⟩
    simp only [hx, not_true_eq_false, and_false, false_or]
    simp_rw [he]
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt fun hlt ↦ h q hlt hq) (I.min'_le _ hx)
    · rintro rfl y hy hyI
      exact (not_lt_of_ge (I.min'_le _ hyI)) hy
  · have he (y : A) : equivalentIn (addArrow r b a) x y ↔ equivalentIn r x y := by
      rw [equivalentIn_addArrow_iff ht]
      exact ⟨fun e ↦ e.elim id (fun h ↦ (hx ((mem_intervalIndices a b x).mpr h.1)).elim),
        Or.inl⟩
    have hne : x ≠ q := fun h ↦ hx (h ▸ hq)
    simp only [he, mem_classLeaders, hx, not_false_eq_true, and_true, hne, or_false]

theorem card_classLeaders_addArrow (ht : ∀ ⦃x y z : A⦄, r x y → r y z → r x z)
    {a b : A} (hI : (intervalIndices r a b).Nonempty) :
    (classLeaders (addArrow r b a)).card =
      (classLeaders r \ intervalIndices r a b).card + 1 := by
  classical
  rw [classLeaders_addArrow ht hI, Finset.card_union_of_disjoint, Finset.card_singleton]
  exact (Finset.disjoint_singleton_right.mpr fun h ↦
    (Finset.mem_sdiff.mp h).2 ((intervalIndices r a b).min'_mem hI))

variable {B : Type*}

/-- The number of least representatives equals the number of distinct encoded classes. -/
theorem card_classLeaders_eq_card_image [DecidableEq B] (key : A → B)
    (hkey : ∀ x y, equivalentIn r x y ↔ key x = key y) :
    (classLeaders r).card = (Finset.univ.image key).card := by
  classical
  have hmatch : (classLeaders r).image key = Finset.univ.image key := by
    ext y
    constructor
    · intro hy
      exact Finset.image_subset_image (f := key) (Finset.subset_univ (classLeaders r)) hy
    · intro hy
      obtain ⟨x, _, hxy⟩ := Finset.mem_image.mp hy
      let J := Finset.univ.filter fun w : A ↦ key w = y
      have hJ : J.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
      let j : A := J.min' hJ
      have hj : j ∈ J := J.min'_mem hJ
      have hjy : key j = y := (Finset.mem_filter.mp hj).2
      refine Finset.mem_image.mpr ⟨j, (mem_classLeaders j).mpr ?_, hjy⟩
      intro i hi hji
      have hiy := ((hkey j i).mp hji).symm.trans hjy
      exact (not_lt_of_ge (J.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiy⟩))) hi
  rw [← hmatch]
  apply (Finset.card_image_of_injOn _).symm
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | h | hgt
  · exact False.elim ((mem_classLeaders y).mp hy x hlt ((hkey y x).mpr hxy.symm))
  · exact h
  · exact False.elim ((mem_classLeaders x).mp hx y hgt ((hkey x y).mpr hxy))

end Finite

end PolytopalProducts.OrderFaces
