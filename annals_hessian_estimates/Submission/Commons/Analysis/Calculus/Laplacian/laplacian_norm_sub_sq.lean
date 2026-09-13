import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin

open scoped RealInnerProductSpace InnerProductSpace

namespace Commons.Analysis.Calculus.Laplacian

/-- The second derivative of the squared distance function `z ↦ ‖z - c‖ ^ 2` in the
direction `v`: it is the constant `2 * ‖v‖ ^ 2`.  Equivalently the Hessian of
`‖· - c‖ ^ 2` is `2` times the inner product, on any real inner product space. -/
theorem fderiv_fderiv_norm_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c x v : E) :
    (fderiv ℝ (fderiv ℝ (fun z : E => ‖z - c‖ ^ 2)) x) v v = 2 * ‖v‖ ^ 2 := by
  have hq : ContDiffAt ℝ 2 (fun z : E => ‖z - c‖ ^ 2) x :=
    ((contDiffAt_id (x := x)).sub contDiffAt_const).norm_sq ℝ
  rw [← Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line hq v]
  have h1 : deriv (fun t : ℝ => ‖(x + t • v) - c‖ ^ 2) =
      fun t : ℝ => 2 * ⟪(x + t • v) - c, v⟫_ℝ := by
    funext t
    have hφ : HasDerivAt (fun s : ℝ => (x + s • v) - c) v t := by
      simpa using ((((hasDerivAt_id t).smul_const v).const_add x).sub_const c)
    exact (hφ.norm_sq).deriv
  rw [h1]
  have hpt : ∀ t : ℝ, ⟪(x + t • v) - c, v⟫_ℝ = ⟪x - c, v⟫_ℝ + t * ‖v‖ ^ 2 := by
    intro t
    have h2 : (x + t • v) - c = (x - c) + t • v := by abel
    rw [h2, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h_eq : (fun t : ℝ => 2 * ⟪(x + t • v) - c, v⟫_ℝ) =
      fun t : ℝ => 2 * (⟪x - c, v⟫_ℝ + t * ‖v‖ ^ 2) := by
    funext t
    rw [hpt t]
  rw [h_eq]
  have h1' : HasDerivAt (fun t : ℝ => t * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).mul_const (‖v‖ ^ 2)
  have h2' : HasDerivAt (fun t : ℝ => ⟪x - c, v⟫_ℝ + t * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 :=
    h1'.const_add _
  have h3 : HasDerivAt (fun t : ℝ => 2 * (⟪x - c, v⟫_ℝ + t * ‖v‖ ^ 2)) (2 * ‖v‖ ^ 2) 0 := by
    simpa using h2'.const_mul (2:ℝ)
  exact h3.deriv

theorem laplacian_norm_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (c : E) :
    Laplacian.laplacian (fun z : E => ‖z - c‖ ^ 2) = fun _ => 2 * (Module.finrank ℝ E : ℝ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun z : E => ‖z - c‖ ^ 2) (stdOrthonormalBasis ℝ E)]
  funext x
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      iteratedFDeriv ℝ 2 (fun z : E => ‖z - c‖ ^ 2) x
        ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] = 2 := by
    intro i
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [fderiv_fderiv_norm_sub_sq]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp [mul_comm]

end Commons.Analysis.Calculus.Laplacian