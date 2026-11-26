import PolytopalProducts.TruncatedAffineFaces
import PolytopalProducts.PyramidGeometry

noncomputable section
namespace PolytopalProducts.Truncated
open Set Finset ContinuousLinearMap _root_.PolytopalProducts.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exposed_hull (l : StrongDual ℝ E) (S : Set E) (m : ℝ)
    (hbound : ∀ x ∈ S, l x ≤ m) (hmax : ∃ x ∈ S, l x = m) :
    l.toExposed (convexHull ℝ S) = convexHull ℝ {x ∈ S | l x = m} := by
  let F := convexHull ℝ {x ∈ S | l x = m}
  let C : Set E := {x | l x ≤ m ∧ (l x = m → x ∈ F)}
  have hc : Convex ℝ C := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    change l x ≤ m ∧ _ at hx
    change l y ≤ m ∧ _ at hy
    change l (a • x + b • y) ≤ m ∧ _
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    have hm : a * m + b * m = m := by linear_combination m * hab
    refine ⟨(add_le_add (mul_le_mul_of_nonneg_left hx.1 ha.le)
      (mul_le_mul_of_nonneg_left hy.1 hb.le)).trans_eq hm, ?_⟩
    intro he
    have hxe : l x = m := hx.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt ha)
        (mul_le_mul_of_nonneg_left hy.1 hb.le)]
    have hye : l y = m := hy.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.1 ha.le)
        (mul_lt_mul_of_pos_left hlt hb)]
    exact (convex_convexHull ℝ _) (hx.2 hxe) (hy.2 hye) ha.le hb.le hab
  have hall : convexHull ℝ S ⊆ C := convexHull_min (fun x hx ↦
    ⟨hbound x hx, fun he ↦ subset_convexHull ℝ _ ⟨hx, he⟩⟩) hc
  obtain ⟨u, hu, hum⟩ := hmax
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    exact (hall hx).2 ((hall hx).1.antisymm (hum ▸ hh u (subset_convexHull ℝ S hu)))
  · intro hx
    have hx₁ : x ∈ convexHull ℝ S := convexHull_mono (fun _ h ↦ h.1) hx
    have hx₂ : m ≤ l x :=
      convexHull_min (fun y (h : y ∈ {z ∈ S | l z = m}) ↦ h.2.ge)
        (convex_halfSpace_ge l.toLinearMap.isLinear m) hx
    exact ⟨hx₁, fun y hy ↦ (hall hy).1.trans hx₂⟩



abbrev Space := (ℝ × ℝ) × ℝ
def point (i : Fin 7) : Space := (((coord i).1,(coord i).2.1),(coord i).2.2)
def body : Set Space := convexHull ℝ (Set.range point)

def labels (j : Fin 28) : Finset (Fin 7) := univ.filter fun i ↦ listed j i

structure FaceCode where
  index : Fin 28
  deriving DecidableEq, Fintype

private theorem labels_injective : Function.Injective labels := by
  intro j k h
  apply faces_distinct j k
  intro i
  have e := Finset.ext_iff.mp h i
  simpa [labels] using e

instance : PartialOrder FaceCode := PartialOrder.lift (fun v ↦ labels v.index)
  (fun i j h ↦ by cases i; cases j; congr 1; exact labels_injective h)

instance : DecidableLE FaceCode := fun i j ↦ inferInstanceAs (Decidable (labels i.index ⊆ labels j.index))

def hull (j : Fin 28) : Set Space := convexHull ℝ (point '' (labels j : Set (Fin 7)))

def linearScore (a b c : ℝ) : StrongDual ℝ Space :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ) + c • ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ

theorem linearScore_point (a b c : ℝ) (i : Fin 7) :
    linearScore a b c (point i) = score a b c i := by
  simp [linearScore,point,score,smul_eq_mul]

theorem functional_point (l : StrongDual ℝ Space) (i : Fin 7) :
    l (point i) = score (l ((1,0),0)) (l ((0,1),0)) (l ((0,0),1)) i := by
  have e : point i = ((coord i).1:ℝ) • (((1,0),0) : Space) +
      ((coord i).2.1:ℝ) • (((0,1),0) : Space) + ((coord i).2.2:ℝ) • (((0,0),1) : Space) := by
    ext <;> simp [point]
  rw [e,map_add,map_add,map_smul,map_smul,map_smul]
  simp [score,smul_eq_mul,mul_comm]

private def normal (j : Fin 28) : StrongDual ℝ Space :=
  let u := exposing[j.val]
  linearScore u.1 u.2.1 u.2.2.1

private def height (j : Fin 28) : ℝ := exposing[j.val].2.2.2

private theorem normal_exact (j : Fin 28) (i : Fin 7) :
    if listed j i then normal j (point i) = height j else normal j (point i) < height j := by
  have e := exposing_valid j i
  cases b : listed j i <;> simp [b] at e ⊢ <;>
    simp only [normal,linearScore_point,score,height] <;> exact_mod_cast e

private theorem support_hull {l : StrongDual ℝ Space} {m : ℝ} {j : Fin 28}
    (nonempty : (labels j).Nonempty)
    (spec : ∀ i, if listed j i then l (point i) = m else l (point i) < m) :
    l.toExposed body = hull j := by
  obtain ⟨u,hu⟩ := nonempty
  have hbit : listed j u = true := by simpa [labels] using hu
  have bound : ∀ x ∈ Set.range point, l x ≤ m := by
    rintro _ ⟨i,rfl⟩
    have t := spec i
    cases b : listed j i <;> simp only [b,Bool.false_eq_true,ite_false,ite_true] at t <;>
      exact t.le
  have att : ∃ x ∈ Set.range point, l x = m :=
    ⟨point u,⟨u,rfl⟩,by simpa [hbit] using spec u⟩
  rw [body, exposed_hull l _ m bound att,hull]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i,rfl⟩,h⟩
    refine ⟨i,?_,rfl⟩
    have t := spec i
    cases b : listed j i <;> simp [labels,b] at t ⊢
    exact (ne_of_lt t h).elim
  · rintro ⟨i,hi,rfl⟩
    have b : listed j i = true := by simpa [labels] using hi
    exact ⟨⟨i,rfl⟩,by simpa [b] using spec i⟩

theorem hull_exposed (j : Fin 28) : IsExposed ℝ body (hull j) := by
  by_cases e : (labels j).Nonempty
  · rw [← support_hull e (normal_exact j)]
    exact ContinuousLinearMap.toExposed.isExposed
  · simpa [hull,Finset.not_nonempty_iff_eq_empty.mp e] using (isExposed_empty (𝕜 := ℝ) (A := body))

theorem point_mem_hull (i : Fin 7) (j : Fin 28) : point i ∈ hull j ↔ i ∈ labels j := by
  refine ⟨fun hx ↦ ?_,fun h ↦ subset_convexHull ℝ _ ⟨i,h,rfl⟩⟩
  have lower : hull j ⊆ {x | height j ≤ normal j x} := by
    apply convexHull_min _ (convex_halfSpace_ge (normal j).toLinearMap.isLinear _)
    rintro _ ⟨h,hh,rfl⟩
    have b : listed j h = true := by simpa [labels] using hh
    exact (show normal j (point h) = height j by simpa [b] using normal_exact j h).ge
  have t := normal_exact j i
  cases b : listed j i <;> simp [labels,b] at t ⊢
  exact (not_lt_of_ge (lower hx) t).elim

theorem hull_order (i j : FaceCode) : hull i.index ⊆ hull j.index ↔ i ≤ j := by
  refine ⟨fun sub a h ↦ (point_mem_hull a _).mp (sub ((point_mem_hull a _).mpr h)),
    fun sub ↦ convexHull_mono (Set.image_mono sub)⟩

def realized (c : FaceCode) : ExposedFace body := ⟨hull c.index,hull_exposed _⟩

theorem realized_surjective : Function.Surjective realized := by
  intro F
  by_cases nonempty : F.val.Nonempty
  · obtain ⟨l,hl⟩ := F.property nonempty
    obtain ⟨u,_,hu⟩ := Finset.exists_max_image (univ : Finset (Fin 7)) (fun i ↦ l (point i))
      Finset.univ_nonempty
    let h := l (point u)
    classical
    let f (i : Fin 7) := decide (l (point i)=h)
    have active (i : Fin 7) : if f i then l (point i)=h else l (point i)<h := by
      simp only [f,decide_eq_true_eq]
      split <;> rename_i e
      · exact e
      · exact lt_of_le_of_ne (hu i (mem_univ _)) e
    obtain ⟨j,matchj⟩ := classified (a:=l ((1,0),0)) (b:=l ((0,1),0)) (c:=l ((0,0),1)) (h:=h) f (fun i ↦ by simpa only [← functional_point] using active i)
    have see : (labels j).Nonempty := ⟨u,by simp [labels,← matchj,f,h]⟩
    have eq := support_hull (l:=l) (m:=h) see (fun i ↦ by rw [← matchj]; exact active i)
    exact ⟨⟨j⟩,Subtype.ext (eq.symm.trans hl.symm)⟩
  · refine ⟨⟨0⟩,Subtype.ext ?_⟩
    have z : labels 0=∅ := by ext i; simp [labels,empty_code]
    change hull 0 = F.val
    simp [hull,z,Set.not_nonempty_iff_eq_empty.mp nonempty]

def faceIso : FaceCode ≃o ExposedFace body where
  toEquiv := Equiv.ofBijective realized ⟨fun a b h ↦ le_antisymm
    ((hull_order a b).mp (le_of_eq (congrArg Subtype.val h)))
    ((hull_order b a).mp (le_of_eq (congrArg Subtype.val h.symm))),realized_surjective⟩
  map_rel_iff' := hull_order _ _

#print axioms faceIso
end PolytopalProducts.Truncated
