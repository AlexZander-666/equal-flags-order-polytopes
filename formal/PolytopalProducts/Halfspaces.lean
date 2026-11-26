import PolytopalProducts

/-! Faces of a finite intersection of closed linear halfspaces. -/

noncomputable section

namespace PolytopalProducts.Halfspaces

open Set Filter
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (a : ι → StrongDual ℝ E) (b : ι → ℝ)

/-- Points satisfying all the listed halfspace inequalities. -/
def body : Set E := {x | ∀ i, a i x ≤ b i}

/-- Points of the body that saturate a designated collection of constraints. -/
def face (s : Finset ι) : Set E := {x ∈ body a b | ∀ i ∈ s, a i x = b i}

/-- The simultaneous kernel of the active forms. -/
def tangent (s : Finset ι) : Submodule ℝ E where
  carrier := {d | ∀ i ∈ s, a i d = 0}
  zero_mem' := by simp
  add_mem' hu hv i hi := by
    change a i (_ + _) = 0
    rw [map_add, hu i hi, hv i hi, add_zero]
  smul_mem' c _ hu i hi := by
    change a i (c • _) = 0
    rw [map_smul, hu i hi, smul_zero]

theorem face_isExposed (s : Finset ι) : IsExposed ℝ (body a b) (face a b s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : face a b ∅ = body a b := by ext x; simp [face]
    rw [he]
  | insert i s hi ih =>
    have he : face a b (insert i s) = face a b {i} ∩ face a b s := by
      ext x
      simp only [face, mem_ofPred_eq, Finset.forall_mem_insert, Finset.mem_singleton,
        forall_eq, mem_inter_iff]
      tauto
    rw [he]
    refine IsExposed.inter ?_ ih
    rintro ⟨w, hw⟩
    refine ⟨a i, ?_⟩
    ext x
    change (x ∈ body a b ∧ ∀ j ∈ ({i} : Finset ι), a j x = b j) ↔ _
    simp only [Finset.mem_singleton, forall_eq, mem_ofPred_eq]
    have hw' : a i w = b i := hw.2 i (Finset.mem_singleton_self i)
    constructor
    · rintro ⟨hx, hxi⟩
      exact ⟨hx, fun y hy ↦ (hy i).trans_eq hxi.symm⟩
    · rintro ⟨hx, hxi⟩
      exact ⟨hx, (hx i).antisymm (hw'.symm.trans_le (hxi w hw.1))⟩

theorem convex_body : Convex ℝ (body a b) := by
  intro x hx y hy c d hc hd hcd i
  rw [map_add, map_smul, map_smul]
  change c * a i x + d * a i y ≤ b i
  calc
    _ ≤ c * b i + d * b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hc)
      (mul_le_mul_of_nonneg_left (hy i) hd)
    _ = _ := by linear_combination b i * hcd

variable [Fintype ι]

/-- Exactly the constraints which are tight at every point of the subset. -/
def active (F : Set E) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ ∀ x ∈ F, a i x = b i

theorem mem_active (F : Set E) (i : ι) :
    i ∈ active a b F ↔ ∀ x ∈ F, a i x = b i := by
  classical
  simp [active]

private theorem exists_simultaneous_strict {F : Set E} (hc : Convex ℝ F)
    (hn : F.Nonempty) (hs : F ⊆ body a b) (s : Finset ι)
    (hloose : ∀ i ∈ s, i ∉ active a b F) :
    ∃ x ∈ F, ∀ i ∈ s, a i x < b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hn.some, hn.some_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨x, hx, hxs⟩ := ih fun j hj ↦ hloose j (Finset.mem_insert_of_mem hj)
    have hi' := hloose i (Finset.mem_insert_self i s)
    rw [mem_active] at hi'
    push Not at hi'
    obtain ⟨y, hy, hyi⟩ := hi'
    have hsx := hs hx
    have hsy := hs hy
    have hlt : a i y < b i := lt_of_le_of_ne (hsy i) hyi
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y,
      hc hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro j hj
    rw [map_add, map_smul, map_smul]
    change (1 / 2 : ℝ) * a j x + (1 / 2 : ℝ) * a j y < b j
    rcases Finset.mem_insert.mp hj with rfl | hj
    · linarith only [hsx j, hlt]
    · linarith only [hxs j hj, hsy j]

/-- There is one point on the face strict on every constraint not identically active. -/
theorem exists_strict_point {F : Set E} (hF : IsExposed ℝ (body a b) F)
    (hn : F.Nonempty) :
    ∃ x ∈ F, ∀ i ∉ active a b F, a i x < b i := by
  classical
  obtain ⟨x, hx, hxs⟩ := exists_simultaneous_strict a b
    (hF.convex (convex_body a b)) hn hF.subset (Finset.univ \ active a b F)
    (fun _ hi ↦ (Finset.mem_sdiff.mp hi).2)
  exact ⟨x, hx, fun i hi ↦ hxs i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)⟩

private theorem exists_positive_inside (s : Finset ι) {x d : E}
    (hx : x ∈ face a b s) (hd : d ∈ tangent a s)
    (hstrict : ∀ i ∉ s, a i x < b i) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ face a b s := by
  classical
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ∀ i : ι, a i (x + t • d) ≤ b i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall fun t ↦ by
        rw [map_add, map_smul, hd i hi, smul_zero, add_zero, hx.2 i hi]
    · let f : ℝ → ℝ := fun t ↦ a i (x + t • d)
      have hf : Continuous f := (a i).continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))
      have hz : f 0 < b i := by simpa [f] using hstrict i hi
      exact (hf.continuousAt.eventually_lt continuousAt_const hz).mono fun _ h ↦ h.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ht
  refine ⟨ε/2, by positivity, hball ?_, ?_⟩
  · rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : 0 ≤ ε/2)]
    linarith
  · intro i hi
    rw [map_add, map_smul, hd i hi, smul_zero, add_zero, hx.2 i hi]

/-- Every nonempty exposed face is exactly the intersection of its tight constraints. -/
theorem eq_face_active {F : Set E} (hF : IsExposed ℝ (body a b) F) (hn : F.Nonempty) :
    F = face a b (active a b F) := by
  obtain ⟨x, hx, hstrict⟩ := exists_strict_point a b hF hn
  have hmem {v : E} (hv : v ∈ F) : v ∈ face a b (active a b F) :=
    ⟨hF.subset hv, fun i hi ↦ (mem_active a b F i).mp hi v hv⟩
  refine Set.Subset.antisymm (fun _ ↦ hmem) ?_
  intro y hy
  obtain ⟨u, hu⟩ := hF hn
  have hx' := show x ∈ {z ∈ body a b | ∀ w ∈ body a b, u w ≤ u z} from hu ▸ hx
  have hd : x - y ∈ tangent a (active a b F) := by
    intro i hi
    rw [map_sub, (hmem hx).2 i hi, hy.2 i hi, sub_self]
  obtain ⟨t, ht, hz⟩ := exists_positive_inside a b _ (hmem hx) hd hstrict
  have hmax := hx'.2 _ hz.1
  have hye : u y = u x := by
    refine (hx'.2 y hy.1).antisymm (le_of_not_gt fun hy' ↦ ?_)
    rw [map_add, map_smul, map_sub] at hmax
    have hpos := mul_pos ht (sub_pos.mpr hy')
    change u x + t * (u x - u y) ≤ u x at hmax
    linarith
  rw [hu]
  exact ⟨hy.1, fun z hz ↦ (hx'.2 z hz).trans_eq hye.symm⟩

/-- A face with a point strict off the designated equalities has their simultaneous kernel
as its direction space. -/
theorem vectorSpan_face (s : Finset ι) {x : E} (hx : x ∈ face a b s)
    (hstrict : ∀ i ∉ s, a i x < b i) :
    vectorSpan ℝ (face a b s) = tangent a s := by
  apply le_antisymm
  · rw [vectorSpan_eq_span_vsub_set_right ℝ hx]
    apply Submodule.span_le.mpr
    rintro d ⟨y, hy, rfl⟩ i hi
    change a i (y - x) = 0
    rw [map_sub, hy.2 i hi, hx.2 i hi, sub_self]
  · intro d hd
    obtain ⟨t, ht, hy⟩ := exists_positive_inside a b s hx hd hstrict
    have h := vsub_mem_vectorSpan ℝ hy hx
    have hs : t • d ∈ vectorSpan ℝ (face a b s) := by
      change x + t • d - x ∈ _ at h
      simpa only [add_sub_cancel_left] using h
    simpa only [inv_smul_smul₀ ht.ne'] using (vectorSpan ℝ (face a b s)).smul_mem t⁻¹ hs

/-- The dual span of a list of active constraints. -/
def dualSpan (s : Finset ι) : Submodule ℝ (Module.Dual ℝ E) :=
  Submodule.span ℝ (Set.range fun i : s ↦ (a i.val).toLinearMap)

omit [Fintype ι] in
theorem tangent_eq_dualCoannihilator (s : Finset ι) :
    tangent a s = (dualSpan a s).dualCoannihilator := by
  ext d
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hd
    have hle : dualSpan a s ≤ LinearMap.ker (Module.Dual.eval ℝ E d) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hd i.val i.property
    exact fun f hf ↦ hle hf
  · intro hd i hi
    exact hd _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)

omit [Fintype ι] in
theorem same_face_of_tangent_eq {s t : Finset ι} (he : tangent a s = tangent a t)
    {x : E} (hs : x ∈ face a b s) (ht : x ∈ face a b t) :
    face a b s = face a b t := by
  have h (i j : Finset ι) (hij : tangent a i = tangent a j)
      (hxi : x ∈ face a b i) (hxj : x ∈ face a b j) : face a b i ⊆ face a b j := by
    intro y hy
    have hd : y - x ∈ tangent a i := by
      intro l hl
      rw [map_sub, hy.2 l hl, hxi.2 l hl, sub_self]
    rw [hij] at hd
    refine ⟨hy.1, fun l hl ↦ ?_⟩
    have heq := hd l hl
    rw [map_sub, hxj.2 l hl] at heq
    exact sub_eq_zero.mp heq
  exact Set.Subset.antisymm (h s t he hs ht) (h t s he.symm ht hs)

/-- A nonempty exposed face is cut out by as many of the original supporting
equations as its codimension. -/
theorem exists_face_eq_card_codim [FiniteDimensional ℝ E] {F : Set E}
    (hF : IsExposed ℝ (body a b) F) (hn : F.Nonempty) :
    ∃ s : Finset ι, F = face a b s ∧
      s.card + Module.finrank ℝ (vectorSpan ℝ F) = Module.finrank ℝ E := by
  classical
  let t := active a b F
  obtain ⟨x, hx, hstrict⟩ := exists_strict_point a b hF hn
  have hF' : F = face a b t := eq_face_active a b hF hn
  have hxt : x ∈ face a b t := hF' ▸ hx
  have hd : vectorSpan ℝ F = tangent a t :=
    hF'.symm ▸ vectorSpan_face a b t hxt hstrict
  let v : t → Module.Dual ℝ E := fun i ↦ (a i.val).toLinearMap
  obtain ⟨κ, f, hf, hspan, hlin⟩ := exists_linearIndependent' ℝ v
  let e : κ ↪ ι := ⟨fun j ↦ (f j).val, Subtype.val_injective.comp hf⟩
  let : Fintype κ := Fintype.ofInjective e e.injective
  let s := (Finset.univ : Finset κ).map e
  have hst : s ⊆ t := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (f j).property
  have hx_s : x ∈ face a b s := ⟨hxt.1, fun i hi ↦ hxt.2 i (hst hi)⟩
  have hs : dualSpan a s = Submodule.span ℝ (Set.range (v ∘ f)) := by
    unfold dualSpan
    apply congrArg (Submodule.span ℝ)
    ext z
    constructor
    · rintro ⟨⟨i, hi⟩, hiz⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j, hiz⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨e j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  have hds : dualSpan a s = dualSpan a t := hs.trans hspan
  have htang : tangent a t = tangent a s := by
    rw [tangent_eq_dualCoannihilator, tangent_eq_dualCoannihilator, hds]
  refine ⟨s, hF'.trans (same_face_of_tangent_eq a b htang hxt hx_s), ?_⟩
  have hcard : s.card = Module.finrank ℝ (dualSpan a t) := by
    rw [← hds, hs, finrank_span_eq_card hlin]
    simp [s]
  rw [hcard, hd, tangent_eq_dualCoannihilator]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

end PolytopalProducts.Halfspaces

