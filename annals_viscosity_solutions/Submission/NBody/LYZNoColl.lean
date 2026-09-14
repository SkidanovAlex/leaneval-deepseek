import Submission.NBody.LYZSub
import Mathlib

/-!
# The length bounds for `m_λ`-geodesics, without the collision-freeness hypothesis

The lemmas `massLength_le_actionOn` / `massLength_le_psi` / `massLength_le_psi_sub` of
`LYZLength`, `LYZBound` and `LYZSub` take collision-freeness of the curve as a hypothesis.  In the
dyadic induction of Liu--Yan--Zhou this hypothesis is *not* available (the collision-freeness of
the geodesic is one of the conclusions), and it is in fact unnecessary: the pointwise AM--GM
estimate used in the proof holds at collisions too (where the Lagrangian is `⊤`).  This module
records the three `hnc`-free variants.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

theorem massLength_le_actionOn' {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hfin : actionOn m h γ a b < ⊤) :
    Real.sqrt (2 * h) * massLength m γ a b ≤ (actionOn m h γ a b).toReal := by
  have hsqrt : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
  have hpt : ∀ t ∈ Set.Ioc a b,
      ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]) ≤ lagrangian m h (γ t) (deriv γ t) := by
    intro t ht
    exact ofReal_sqrt_mul_weightedNorm_le_lagrangian hh hm (γ t) (deriv γ t)
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]))
      ≤ actionOn m h γ a b := by
    rw [actionOn]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpt t ht
  have hsplit : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m]))
      = ENNReal.ofReal (Real.sqrt (2 * h)) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul hsqrt.le]
  have hne : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m])) ≠ ⊤ := by
    intro htop
    have hAtop : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (Real.sqrt (2 * h) * ‖deriv γ t‖_[m])) = ⊤ := by
      rw [hsplit, htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))]
    rw [hAtop] at h1
    exact absurd h1 (not_le.mpr hfin)
  have hmeas := aestronglyMeasurable_weightedNorm_deriv (m := m) hac
  have hint : Integrable (fun t : ℝ => ‖deriv γ t‖_[m]) (volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun t => weightedNorm_nonneg m _)).mp hne
  have hbridge : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m]))
      = ENNReal.ofReal (massLength m γ a b) := by
    rw [massLength, intervalIntegral.integral_of_le hab]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => weightedNorm_nonneg m _)).symm
  have hmain : ENNReal.ofReal (Real.sqrt (2 * h) * massLength m γ a b) ≤ actionOn m h γ a b := by
    rw [hsplit, hbridge, ← ENNReal.ofReal_mul hsqrt.le] at h1
    exact h1
  have hml : 0 ≤ massLength m γ a b :=
    intervalIntegral.integral_nonneg_of_forall hab fun t => weightedNorm_nonneg m _
  have := ENNReal.toReal_mono hfin.ne hmain
  rwa [ENNReal.toReal_ofReal (mul_nonneg hsqrt.le hml)] at this

theorem massLength_le_psi' {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {τ T A B M : ℝ}
    (hτ : 0 ≤ τ) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
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
    have h := massLength_le_actionOn' hh hm hτ hac hfin
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

theorem massLength_le_psi_sub' {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {σ τ D A B M : ℝ}
    (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hD : 0 < D)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hγσ : γ σ = xstar + D • b) (hb : ‖b‖_[m] = 1)
    (hncseg : ∀ t ∈ Set.Icc (0:ℝ) D, WithoutCollisions (xstar + t • b))
    (hΦ₁ : actionPot m h (γ 0) xstar < ⊤)
    (hA : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hpot : ∫ t in (0:ℝ)..D, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * D + 2 * M + 1))
    (hlog : 0 ≤ Real.log (2 * D + 2 * M + 1)) :
    massLength m γ 0 σ ≤ D + lyzPsi A B M D := by
  rcases eq_or_lt_of_le hσ0 with h0 | h0
  · rw [← h0, massLength]
    simp only [intervalIntegral.integral_same]
    have := lyzPsi_nonneg hA0 hB0 hM0 (le_of_lt hD)
    linarith
  rcases lt_or_eq_of_le hστ with hlt | heq
  · have hacσ : AbsolutelyContinuousOnInterval γ 0 σ :=
      hac.mono (by rw [uIcc_of_le hσ0, uIcc_of_le (le_trans hσ0 hστ)]
                   exact Set.Icc_subset_Icc_right hστ)
    have hminσ : IsHMinimizer m h γ 0 σ := IsHMinimizer.sub_left_of_le hac hmin hfin h0 hlt.le
    have hfinσ : actionOn m h γ 0 σ < ⊤ := actionOn_lt_top_of_le hσ0 hστ hfin
    exact massLength_le_psi' hh hm hσ0 hD hacσ hfinσ hminσ hγσ hb hncseg hΦ₁ hA hpot hlog
  · rw [heq]
    exact massLength_le_psi' hh hm (le_trans hσ0 (le_of_eq heq)) hD hac hfin hmin
      (heq ▸ hγσ) hb hncseg hΦ₁ hA hpot hlog

end Submission.NBody
