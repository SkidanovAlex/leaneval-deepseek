import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq
import Submission.Commons.Analysis.GaussianMeasure.creation_energy_bound_even_smooth
import Submission.Commons.Analysis.GaussianMeasure.creation_energy_bound_even_of_smooth
import Submission.Commons.Analysis.GaussianMeasure.creation_energy_bound_even_transport

open MeasureTheory Real
open scoped Real Topology InnerProductSpace

/-!
# `creation_energy_bound_even` : proof strategy (verified roadmap)

Target (unchanged below):
for even `u`, even `f` with `D²f ⪰ 2π·Id`, `f - π‖x‖²` convex and polynomial growth of all
derivatives,
`4π ∫ ‖∇u‖² e^{-f} ≤ ∫ (-Δu + ⟪∇f, ∇u⟫)² e^{-f}`,
where `L u := -Δu + ⟪∇f,∇u⟫` is (minus) the weighted Laplacian `-∇*∇` of `e^{-f}`.

## Mathematical route (as used in Regev–Stephens-Davidowitz, and in
Cordero-Erausquin–Fradelizi–Maurey, *Improved log-concavity…*, arXiv:2111.05110, Thm BL-even)

Write `A := Hess u`, `w := ∇u`, `g := ∇f`, `F := Hess f`.

1. **Bochner / Γ₂ identity** (the heart of the proof):
   `∫ (Lu)² e^{-f} = ∫ (‖A‖²_F + ⟪F w, w⟫) e^{-f}`.
   For `u ∈ C³` this follows from two weighted integrations by parts:
   * `∫ (Lu)² e^{-f} = ∫ ⟪∇(Lu), ∇u⟫ e^{-f}`  (weighted IBP with `φ := Lu`),
   * `∫ ⟪(Hess u) ∇u, ∇f⟫ e^{-f} = ∫ (⟪∇div w, w⟫ + ‖A‖²_F) e^{-f}`  (weighted IBP with the
     `C¹` field `(Hess u)∇u`, using `div(Hess u) = ∇Δu`).
2. **Even Brascamp–Lieb gradient bound** (proved below as `bl_gradient_odd`, for `h = ∂_i u`,
   which is *odd* because `u` is even):
   `2π ∫ (∂_i u)² e^{-f} ≤ ∫ ‖∇(∂_i u)‖² e^{-f}`; summing over an orthonormal basis gives
   `2π ∫ ‖w‖² e^{-f} ≤ ∫ ‖A‖²_F e^{-f}`.
3. **Pointwise Hessian bound**: `⟪F w, w⟫ ≥ 2π ‖w‖²` (hypothesis `hH`).
   Combining 1–3: `∫(Lu)² e^{-f} ≥ 2π∫‖w‖² + 2π∫‖w‖² = 4π∫‖w‖²`. ∎

## What is proved in this file

* `even_convex_min`, `pi_mul_norm_sq_add_le`, `exp_neg_le_gauss` : the Gaussian decay
  `e^{-f x} ≤ e^{-f 0} e^{-π‖x‖²}` coming from convexity + evenness (needed for all
  integrability bookkeeping).
* `integrable_mul_exp_neg_of_pow_bound` : `Φ · e^{-f}` is integrable when `Φ` has polynomial
  growth.
* `hessInv_quad_nonneg` : the quadratic form of `hessInv` is nonnegative.
* **`bl_gradient_odd`** : step 2 above, completely proved (uses
  `brascamp_lieb_smooth` + `hessInv_energy` + oddness ⟹ mean zero).  This is a self-contained,
  reusable commons lemma.

## Remaining steps (in order)

(R1) **Weighted divergence theorem with polynomial growth** (general finite-dimensional real
     inner product space `E`): for `V : E → E` of class `C¹` with `‖V x‖, ‖fderiv V x‖` polynomially
     bounded and `c + π‖x‖² ≤ f x`,
     `∫ (∑ i, ⟪fderiv ℝ V x (b i), b i⟫) e^{-f} = ∫ ⟪∇f x, V x⟫ e^{-f}` for any orthonormal basis
     `b`.  Route: the compactly supported case follows from Mathlib's
     `MeasureTheory.integral_bilinear_fderiv_right_eq_neg_left_of_integrable` (one direction at a
     time, summed over `b`); then truncate with a `ContDiffBump` cutoff `χ_R` and let `R → ∞` by
     dominated convergence (the Gaussian lower bound on `f` kills the boundary terms).
(R2) **Weighted IBP / Γ₂ identity** : apply (R1) with `V := φ • ∇u` (`φ ∈ C¹`) to get
     `∫ φ (Lu) e^{-f} = ∫ ⟪∇φ,∇u⟫ e^{-f}`; then apply it with `φ := Lu` (needs `u ∈ C³`) and with
     `V := (Hess u)∇u` to obtain the Γ₂ identity of step 1.  This gives the theorem for `u ∈ C³`.
(R3) **Extension to `u ∈ C²`** (the statement only assumes `ContDiff ℝ 2 u`).
     Two viable routes:
     (a) *Mollification*: `u_ε := u ⋆ ρ_ε` is `C^∞` with the same polynomial growth, still even,
         and `L u_ε → Lu`, `∇u_ε → ∇u` in `L²(e^{-f}dx)`, so the inequality passes to the limit.
     (b) *Weak version of Γ₂ for `C²`*: the distributional identity
         `(Δu)² - ‖A‖²_F = div(((Δu)·Id - Hess u)∇u)`
         holds for `C²` functions (it is pointwise for `C³` functions; for `C²` functions both
         sides converge under local mollification).  Using it together with the `C²`-valid
         identity `∫ (Δu)(∇f·∇u) e^{-f} = ∫ (∇f·∇u)² e^{-f} - ∫⟪F w,w⟫ - ∫⟪Aw,g⟫` and
         `∫ (tr F ‖w‖² + 2⟪Aw,g⟫) e^{-f} = ∫ ‖g‖²‖w‖² e^{-f}` yields the Γ₂ identity directly.
(R4) *(If one works in `EuclideanSpace ℝ (Fin n)` for (R1)–(R3)*: transport the result to a
     general `E` along the linear isometry `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)` given by
     `stdOrthonormalBasis ℝ E`, using `integral_comp_isometry`, `grad_comp_isometry`,
     `fderiv_fderiv_comp_isometry`, `convexOn_comp_linearIsometryEquiv` (all in
     `brascamp_lieb_truncated`) and the isometry-invariance of the Laplacian (trace of the
     Hessian).
-/

namespace Commons.Analysis.GaussianMeasure

noncomputable section

theorem creation_energy_bound_even {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (f u : E → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hu : ContDiff ℝ 2 u) (hueven : ∀ x, u (-x) = u x) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) := by
  exact Commons.Analysis.GaussianMeasure.creation_energy_bound_even_transport
    (fun n f' u' hf' hfe' hH' hconv' hgf' hu' hueven' hgu' =>
      Commons.Analysis.GaussianMeasure.creation_energy_bound_even_of_smooth
        (fun f'' u'' hf'' hfe'' hH'' hconv'' hgf'' hu3'' hueven'' hgu3'' =>
          Commons.Analysis.GaussianMeasure.creation_energy_bound_even_smooth
            f'' u'' hf'' hfe'' hH'' hconv'' hgf'' hu3'' hueven'' hgu3'')
        f' u' hf' hfe' hH' hconv' hgf' hu' hueven' hgu')
    f u hf hfe hH hconv hgf hu hueven hgu

end
end Commons.Analysis.GaussianMeasure
