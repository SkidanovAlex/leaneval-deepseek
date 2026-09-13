import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_laplacian_directional
import Submission.Commons.Analysis.Calculus.FDeriv.second_fderiv_laplacian_diag

open scoped Topology
open scoped BigOperators

namespace Commons.Analysis.Calculus.FDeriv

/-- Second-order chain rule for the composition of `Real.log` with a `C²` function `g` that does
not vanish at the point.

Since `(log)' = fun t => t⁻¹` and `(log)'' = fun t => -(t²)⁻¹`, the second derivative of
`log ∘ g` at `x` in directions `a b` is
`(D²g(x) a b) / g x - ((Dg(x) a) * (Dg(x) b)) / (g x)^2`. -/
theorem iteratedFDeriv_two_log_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) (hx : g x ≠ 0) (a b : E) :
    iteratedFDeriv ℝ 2 (fun z => Real.log (g z)) x ![a, b] =
      (iteratedFDeriv ℝ 2 g x ![a, b]) / g x
        - ((fderiv ℝ g x a) * (fderiv ℝ g x b)) / (g x) ^ 2 := by
  set c : E → ℝ := fun z => (g z)⁻¹ with hc
  have hdiff_c : DifferentiableAt ℝ c x := by
    rw [hc]; exact (hg.differentiableAt (by norm_num)).inv hx
  have hdiff_f : DifferentiableAt ℝ (fun y => fderiv ℝ g y) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Near `x`, the derivative of `log ∘ g` is `(g ·)⁻¹ • fderiv g`.
  have hfeq : fderiv ℝ (fun z => Real.log (g z)) =ᶠ[𝓝 x] fun y => c y • fderiv ℝ g y := by
    filter_upwards [(hg.eventually (by norm_num)).and (hg.continuousAt.eventually_ne hx)] with y hy
    rw [hc]
    exact ((hy.1.differentiableAt (by norm_num)).hasFDerivAt.log hy.2).fderiv
  have hcinv : HasFDerivAt c
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((g x) ^ 2)⁻¹)).comp (fderiv ℝ g x)) x := by
    rw [hc]
    have h := (hasFDerivAt_inv (𝕜 := ℝ) hx).comp x (hg.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [Function.comp_def] using h
  have hcfd : fderiv ℝ c x
      = (ContinuousLinearMap.toSpanSingleton ℝ (-((g x) ^ 2)⁻¹)).comp (fderiv ℝ g x) :=
    hcinv.fderiv
  have hsm : fderiv ℝ (fun y => c y • fderiv ℝ g y) x
      = c x • fderiv ℝ (fun y => fderiv ℝ g y) x
        + (fderiv ℝ c x).smulRight (fderiv ℝ g x) := fderiv_smul hdiff_c hdiff_f
  rw [iteratedFDeriv_two_apply, Filter.EventuallyEq.fderiv_eq hfeq, hsm, hcfd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hc, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [iteratedFDeriv_two_apply g x ![a, b]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem second_fderiv_log_laplacian_diag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) {s : Set E} {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 4 u s) (hL : ∀ z ∈ s, (Laplacian.laplacian u) z ≠ 0) (i : ι) :
    (iteratedFDeriv ℝ 2 (fun z => Real.log ((Laplacian.laplacian u) z)) x) ![v i, v i] =
      (∑ k : ι, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (Laplacian.laplacian u) x
        - ((∑ j : ι, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
            / (Laplacian.laplacian u) x) ^ 2 := by
  -- The Laplacian of a `C⁴` function is `C²`.
  have huAt : ContDiffAt ℝ 4 u x := hu.contDiffAt (hs.mem_nhds hx)
  have h2u : ContDiffAt ℝ 2 (iteratedFDeriv ℝ 2 u) x :=
    huAt.iteratedFDeriv_right (i := 2) (m := 2) (by norm_num)
  have hcon : ContDiffAt ℝ 2 (Laplacian.laplacian u) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
    have := ContDiffAt.sum (𝕜 := ℝ) (n := 2) (x := x) (s := Finset.univ)
      (f := fun (j : ι) (z : E) => (iteratedFDeriv ℝ 2 u z) ![v j, v j])
      (fun j _ => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v j, v j]).contDiff.contDiffAt.comp x h2u)
    simpa using this
  -- Apply the second-order chain rule `D²(log ∘ g) = D²g/g - (Dg)²/g²`.
  rw [iteratedFDeriv_two_log_comp hcon (hL x hx) (v i) (v i)]
  -- Identify the first and second derivatives of the Laplacian.
  rw [show fderiv ℝ (Laplacian.laplacian u) x (v i)
        = ∑ j : ι, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i] from
        fderiv_laplacian_directional v hs hx (hu.of_le (by norm_num)) i]
  rw [show iteratedFDeriv ℝ 2 (Laplacian.laplacian u) x ![v i, v i]
        = ∑ k : ι, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k] from
        second_fderiv_laplacian_diag v hs hx hu i]
  rw [div_pow, pow_two]
  ring

end Commons.Analysis.Calculus.FDeriv