import Submission.NBody.LYZPsi
import Mathlib

/-!
# The length bound for `m_λ`-geodesics (Liu--Yan--Zhou, Lemma 4.1)

Combining the straight-line bound for the action potential with the triangle inequality and the
length/Cauchy--Schwarz estimate, we obtain the basic estimate

    `l_m(γ) ≤ T + Ψ(T)`

for an `h`-minimiser `γ` joining `x` to `x* + T • b`, where `b` is a unit vector for the mass
norm and `Ψ(T) = A + B log(2T + 2M + 1)`.  The two "numerical" inputs (`A` dominating the
action potential from `x` to `x*`, and `B` dominating the potential integral along the ray) are
supplied as hypotheses, so that this file is free of the constants.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Length bound for an `h`-minimiser** (Liu--Yan--Zhou, Lemma 4.1). -/
theorem massLength_le_psi {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {τ T A B M : ℝ}
    (hτ : 0 ≤ τ) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 τ < ⊤)
    (hmin : actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ))
    (hγτ : γ τ = xstar + T • b)
    (hb : ‖b‖_[m] = 1)
    (hncseg : ∀ t ∈ Set.Icc (0:ℝ) T, WithoutCollisions (xstar + t • b))
    (hΦ₁ : actionPot m h (γ 0) xstar < ⊤)
    (hA : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hpot : ∫ t in (0:ℝ)..T, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hlog : 0 ≤ Real.log (2 * T + 2 * M + 1)) :
    massLength m γ 0 τ ≤ T + lyzPsi A B M T := by
  set W : ℝ := ∫ t in (0:ℝ)..T, U m (xstar + t • b) with hW
  have hW' : W ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1) := hpot
  have hsqrt : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
  have hsq : (Real.sqrt (2 * h)) ^ 2 = 2 * h := Real.sq_sqrt (by linarith)
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact intervalIntegral.integral_nonneg_of_forall hT.le (fun t => U_nonneg hm _)
  -- the straight-line bound
  have hstraight : actionPot m h xstar (xstar + T • b)
      ≤ ENNReal.ofReal (Real.sqrt (2 * h) * T)
        + ENNReal.ofReal ((Real.sqrt (2 * h))⁻¹ * W) := by
    rw [hW]; exact actionPot_le_of_straight hh hm hb hT xstar hncseg
  have hΦ₂lt : actionPot m h xstar (xstar + T • b) < ⊤ := by
    refine lt_of_le_of_lt hstraight ?_
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  -- the Cauchy--Schwarz length estimate
  have hmm : Real.sqrt (2 * h) * massLength m γ 0 τ
      ≤ (actionPot m h (γ 0) (xstar + T • b)).toReal := by
    have h := massLength_le_actionOn hh hm hτ hac hnc hfin
    rw [hmin, hγτ] at h
    exact h
  -- triangle inequality for the action potential
  have htri := actionPot_triangle m h (γ 0) xstar (xstar + T • b)
  have hAB : actionPot m h (γ 0) xstar + actionPot m h xstar (xstar + T • b) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hΦ₁.ne, hΦ₂lt.ne⟩
  have h3 : (actionPot m h (γ 0) (xstar + T • b)).toReal
      ≤ (actionPot m h (γ 0) xstar).toReal + (actionPot m h xstar (xstar + T • b)).toReal :=
    (ENNReal.toReal_mono hAB htri).trans ENNReal.toReal_add_le
  -- evaluating the straight-line bound in the reals
  have hΦ₂val : (actionPot m h xstar (xstar + T • b)).toReal
      ≤ Real.sqrt (2 * h) * T + (Real.sqrt (2 * h))⁻¹ * W := by
    have hlt : ENNReal.ofReal (Real.sqrt (2 * h) * T)
        + ENNReal.ofReal ((Real.sqrt (2 * h))⁻¹ * W) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    refine (ENNReal.toReal_mono hlt hstraight).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hbound : Real.sqrt (2 * h) * massLength m γ 0 τ
      ≤ (actionPot m h (γ 0) xstar).toReal
        + (Real.sqrt (2 * h) * T + (Real.sqrt (2 * h))⁻¹ * W) :=
    hmm.trans (h3.trans (add_le_add le_rfl hΦ₂val))
  -- the potential integral is absorbed by `B log`
  have hWle : (Real.sqrt (2 * h))⁻¹ * W
      ≤ Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by
    have h2 : (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1))
        = Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by
      have h3 : (Real.sqrt (2 * h))⁻¹ * (2 * h) = Real.sqrt (2 * h) := by
        have h4 : (Real.sqrt (2 * h))⁻¹ * (Real.sqrt (2 * h)) ^ 2 = Real.sqrt (2 * h) := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
        rwa [hsq] at h4
      rw [show (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1))
          = ((Real.sqrt (2 * h))⁻¹ * (2 * h)) * (B * Real.log (2 * T + 2 * M + 1)) by ring, h3]
    calc (Real.sqrt (2 * h))⁻¹ * W
        ≤ (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1)) :=
          mul_le_mul_of_nonneg_left hW' (inv_nonneg.mpr hsqrt.le)
      _ = Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := h2
  have hkey : Real.sqrt (2 * h) * massLength m γ 0 τ
      ≤ (actionPot m h (γ 0) xstar).toReal + Real.sqrt (2 * h) * T
        + Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by linarith
  -- divide by `√(2h)`
  have hgoal : massLength m γ 0 τ
      ≤ (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal + T
        + B * Real.log (2 * T + 2 * M + 1) := by
    have hmul : Real.sqrt (2 * h) * massLength m γ 0 τ
        ≤ Real.sqrt (2 * h) * ((Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal + T
            + B * Real.log (2 * T + 2 * M + 1)) := by
      have hrhs : Real.sqrt (2 * h)
            * ((Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal + T
              + B * Real.log (2 * T + 2 * M + 1))
          = (actionPot m h (γ 0) xstar).toReal + Real.sqrt (2 * h) * T
            + Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by
        rw [mul_add, mul_add,
          show Real.sqrt (2 * h) * ((Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal)
            = (Real.sqrt (2 * h) * (Real.sqrt (2 * h))⁻¹) * (actionPot m h (γ 0) xstar).toReal
            by ring,
          mul_inv_cancel₀ hsqrt.ne', one_mul]
      rw [hrhs]; exact hkey
    exact (mul_le_mul_iff_of_pos_left hsqrt).mp hmul
  rw [lyzPsi]
  linarith [hgoal, hA]

end Submission.NBody
