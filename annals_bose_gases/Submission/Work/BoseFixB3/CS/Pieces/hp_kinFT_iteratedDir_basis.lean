import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

noncomputable section
open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Norm of one term of the multiplier `fourierPowSMulRight (-innerSL ℝ) ⬝ w N` specialised to a
single direction `x`: `‖(-(2πI))^N • (x^N) • z‖ = (2π)^N |x|^N ‖z‖`.  (The norm of the complex
factor `-(2πI)` is `2π`.) -/
lemma hp_norm_neg_two_pi_I_pow_smul (z : ℂ) (x : ℝ) (N : ℕ) :
    ‖(-(2 * (Real.pi : ℂ) * Complex.I)) ^ N • (x ^ N : ℝ) • z‖
      = (2 * Real.pi) ^ N * |x| ^ N * ‖z‖ := by
  have ha : ‖(-(2 * (Real.pi : ℂ) * Complex.I))‖ = 2 * Real.pi := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg Real.pi_nonneg, Complex.norm_ofNat]
  rw [norm_smul, norm_smul, norm_pow, ha, Real.norm_eq_abs, abs_pow]
  ring

/-- The `p`-convention Fourier transform (`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`) turns the
`N`-fold coordinate derivative in the direction `kcStdBasis k` into multiplication by
`|p k|^N`. -/
theorem hp_kinFT_iteratedDir_basis (u : EuclideanSpace ℝ (Fin 3) → ℂ) (k : Fin 3) (N : ℕ)
    (p : EuclideanSpace ℝ (Fin 3)) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcs : HasCompactSupport u) :
    ‖Submission.BoseGases.kinFT
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          (iteratedFDeriv ℝ N u x) (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)) p‖
      = |p k| ^ N * ‖Submission.BoseGases.kinFT u p‖ := by
  -- All iterated derivatives of `u` are continuous with compact support, hence integrable.
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ → Integrable (iteratedFDeriv ℝ n u) := by
    intro n _
    exact (hu.continuous_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport (hcs.iteratedFDeriv n)
  -- Mathlib's Fourier transform of the `N`-th derivative of `u`.
  have hfour := Real.fourier_iteratedFDeriv (N := (⊤ : ℕ∞)) (f := u) hu hInt (n := N) le_top
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
    Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  set w : E3 := (2 * Real.pi)⁻¹ • p with hw
  -- Evaluating a multilinear map commutes with the (Bochner) Fourier integral.
  have heval :
      (𝓕 (fun x => (iteratedFDeriv ℝ N u x) (fun _ : Fin N => Submission.BoseGases.kcStdBasis k)))
          w
        = ((𝓕 (iteratedFDeriv ℝ N u)) w)
            (fun _ : Fin N => Submission.BoseGases.kcStdBasis k) := by
    rw [Real.fourier_eq, Real.fourier_eq]
    have hI' : Integrable (fun v : E3 => 𝐞 (-inner ℝ v w) • (iteratedFDeriv ℝ N u v)) volume :=
      (Real.fourierIntegral_convergent_iff (μ := volume) (f := iteratedFDeriv ℝ N u) w).mpr
        (hInt N le_top)
    rw [ContinuousMultilinearMap.integral_apply hI']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    rfl
  rw [heval, hfour, VectorFourier.fourierPowSMulRight_apply]
  -- Each of the `N` inner products is `-w k`.
  have hinner : ∀ i : Fin N, ((-innerSL ℝ) w) (Submission.BoseGases.kcStdBasis k) = -(w k) := by
    intro i
    rw [show ((-innerSL ℝ) w) (Submission.BoseGases.kcStdBasis k)
          = -(((innerSL ℝ) w) (Submission.BoseGases.kcStdBasis k)) from rfl]
    rw [innerSL_apply_apply, real_inner_comm]
    rw [show inner ℝ (Submission.BoseGases.kcStdBasis k) w = w k by
      rw [Submission.BoseGases.kcStdBasis, EuclideanSpace.inner_single_left]; simp]
  have hprod : (∏ i : Fin N, ((-innerSL ℝ) w) (Submission.BoseGases.kcStdBasis k))
      = (-(w k)) ^ N := by
    rw [Finset.prod_congr rfl (fun i _ => hinner i)]
    simp
  rw [hprod]
  have hwk : w k = (2 * Real.pi)⁻¹ * p k := by
    rw [hw]; simp
  rw [hwk, hp_norm_neg_two_pi_I_pow_smul]
  have harith : (2 * Real.pi) ^ N * |(-((2 * Real.pi)⁻¹ * p k))| ^ N = |p k| ^ N := by
    rw [abs_neg, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi)), ← mul_pow]
    congr 1
    rw [show (2 * Real.pi) * ((2 * Real.pi)⁻¹ * |p k|) = |p k| by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]]
  rw [harith]

end

end Work.BoseFixB3.CS.Pieces
