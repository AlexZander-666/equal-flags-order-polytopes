import PolytopalProducts.TruncatedGeometry
import PolytopalProducts.CubeGeometry
namespace PolytopalProducts.Truncated
open PolytopalProducts.Geometry
open Set
noncomputable section

private theorem three_span (A : Set Space) (b c d : Space) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hzero : 0 ∈ A)
    (rep : ∀ z : Space, ∃ u v w : ℝ, u • b + v • c + w • d = z) : vectorSpan ℝ A = ⊤ := by
  have use_point (x : Space) (hx : x ∈ A) : x ∈ vectorSpan ℝ A := by
    simpa using (vsub_mem_vectorSpan ℝ hx hzero)
  apply top_unique
  intro z _
  obtain ⟨u,v,w,rfl⟩ := rep z
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (use_point _ hb))
    (Submodule.smul_mem _ _ (use_point _ hc))) (Submodule.smul_mem _ _ (use_point _ hd))

theorem body_spans : vectorSpan ℝ body = ⊤ := by
  have mem (i : Fin 7) : point i ∈ body := subset_convexHull ℝ _ ⟨i,rfl⟩
  have p0 : point 0 = ((0,0),0) := by norm_num [point, coord, coordinates]
  have p1 : point 1 = ((6,0),0) := by norm_num [point, coord, coordinates]
  have p2 : point 2 = ((0,6),0) := by norm_num [point, coord, coordinates]
  have p3 : point 3 = ((2,2),-2) := by norm_num [point, coord, coordinates]
  apply three_span body _ _ _ (p1 ▸ mem 1) (p2 ▸ mem 2) (p3 ▸ mem 3) (by change ((0,0),0) ∈ body; rw [← p0]; exact mem 0)
  rintro ⟨⟨x,y⟩,z⟩
  refine ⟨(x+z)/6,(y+z)/6,-z/2,?_⟩
  ext <;> simp [smul_eq_mul]

theorem pyramid_spans : vectorSpan ℝ hexagonalPyramid = ⊤ := by
  have mem (i : Polygon.GeneralRealization.Index 3) :
      (Polygon.GeneralRealization.point i, (0:ℝ)) ∈ hexagonalPyramid :=
    subset_convexHull ℝ _ (Or.inr ⟨Polygon.GeneralRealization.point_mem_polytope i, rfl⟩)
  have pc (i : Polygon.GeneralRealization.Index 3) :
      Polygon.GeneralRealization.point i = ((i.val:ℝ),(i.val:ℝ)^2) := rfl
  have p0 : (((0,0),0):Space) ∈ hexagonalPyramid := by simpa [pc] using mem 0
  have p1 : (((1,1),0):Space) ∈ hexagonalPyramid := by
    have h := mem 1
    rw [pc] at h
    change (((((1:Fin 6).val:ℝ),(((1:Fin 6).val:ℝ)^2)),0):Space) ∈ hexagonalPyramid at h
    norm_num at h
    exact h
  have p2 : (((2,4),0):Space) ∈ hexagonalPyramid := by
    have h := mem 2
    rw [pc] at h
    change (((((2:Fin 6).val:ℝ),(((2:Fin 6).val:ℝ)^2)),0):Space) ∈ hexagonalPyramid at h
    norm_num at h
    exact h
  have p3 : (((0,0),1):Space) ∈ hexagonalPyramid :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  apply three_span hexagonalPyramid _ _ _ p1 p2 p3 p0
  rintro ⟨⟨x,y⟩,z⟩
  refine ⟨2*x-y,(y-x)/2,z,?_⟩
  ext <;> simp [smul_eq_mul] <;> ring

theorem both_dimensions : Module.finrank ℝ (vectorSpan ℝ body) = 3 ∧
    Module.finrank ℝ (vectorSpan ℝ hexagonalPyramid) = 3 := by
  rw [body_spans,pyramid_spans]
  norm_num [Space,finrank_top,Module.finrank_prod]

#print axioms both_dimensions
end
end PolytopalProducts.Truncated

