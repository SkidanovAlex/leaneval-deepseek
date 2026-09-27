import Mathlib

namespace Work.EKLComp

/-- If `u` is a unit vector orthogonal to `x₁`, `x₂` and `p`, and `x₁, x₂` are linearly
independent vectors of `ℝ³ = Fin 3 → ℝ`, then `p` lies in the span of `x₁` and `x₂`.

The proof uses the linear functional `f v = ∑ i, u i * v i`.  Since `f u = 1`, `f` is nonzero,
so its kernel has dimension `3 - 1 = 2`.  Both `x₁` and `x₂` lie in `ker f`, and since they are
independent their span is a `2`-dimensional subspace of the `2`-dimensional space `ker f`;
hence `span {x₁, x₂} = ker f`.  Finally `f p = 0`, so `p ∈ ker f = span {x₁, x₂}`. -/
theorem mem_span_pair_of_orthogonal_vector (x1 x2 u p : Fin 3 → ℝ)
    (hu1 : ∑ i, u i * x1 i = 0) (hu2 : ∑ i, u i * x2 i = 0)
    (huu : ∑ i, u i * u i = 1) (hup : ∑ i, u i * p i = 0)
    (hind : LinearIndependent ℝ ![x1, x2]) :
    p ∈ Submodule.span ℝ {x1, x2} := by
  let f : Module.Dual ℝ (Fin 3 → ℝ) := ∑ i, (u i) • (LinearMap.proj i)
  have hfeval : ∀ v : Fin 3 → ℝ, f v = ∑ i, u i * v i := by
    intro v
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hfu : f u = 1 := by rw [hfeval u, huu]
  have hfne : f ≠ 0 := by
    intro h
    have h0 : f u = 0 := by simp [h]
    rw [hfu] at h0
    exact one_ne_zero h0
  have hkerfin : Module.finrank ℝ (LinearMap.ker f) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hfne (K := ℝ) (V₁ := Fin 3 → ℝ)
    rw [Module.finrank_pi, Fintype.card_fin] at h
    omega
  have hspanfin : Module.finrank ℝ (Submodule.span ℝ ({x1, x2} : Set (Fin 3 → ℝ))) = 2 := by
    rw [← Matrix.range_cons_cons_empty x1 x2 ![]]
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hx1 : x1 ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hfeval x1, hu1]
  have hx2 : x2 ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hfeval x2, hu2]
  have hle : Submodule.span ℝ ({x1, x2} : Set (Fin 3 → ℝ)) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact hx1
    · rw [h]; exact hx2
  have heq : Submodule.span ℝ ({x1, x2} : Set (Fin 3 → ℝ)) = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hspanfin, hkerfin])
  rw [heq, LinearMap.mem_ker, hfeval p, hup]

end Work.EKLComp
