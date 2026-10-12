import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Fourier.fourier_decay_mul_update
import Submission.Work.SmallBoxTBWord.Defs
import Submission.Work.SmallBoxTBWord.chi_support_and_deriv_bound
import Submission.Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniform `(1+‖p‖)⁻³` decay of the windowed amplitude `tBamp`

`tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})dz` is the `p`-convention Fourier
transform of the compactly supported `C^∞` function `z ↦ χ(z)Φ(x_{i←z})`
(`kinFT_eq_fourier`), evaluated at `(2π)⁻¹ • p`.  The general Fourier-decay estimate
`Commons.Analysis.Fourier.fourier_decay_mul_update` bounds it by
`C·(1+‖(2π)⁻¹•p‖)⁻³·(derivative data)`, uniformly in `x` on the box `abox N a`; the
`(2π)` factor and the `1+‖p‖` comparison are absorbed into the constant.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.SmallBoxTBWord

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-! ## Auxiliary analytic facts -/

/-- A vector of `ℝ³` all of whose coordinates are bounded by `C` has norm at most `√3·C`. -/
private lemma norm_le_of_coord_abs_le {C : ℝ} (hC : 0 ≤ C) {y : ℝ³}
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ _k : Fin 3, C ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  · exact hb

/-- Absorption of the `(2π)` scaling of the Fourier variable:
`K·(1+r/c)⁻³ ≤ K·c³/(1+r)³` for `K ≥ 0`, `c ≥ 1`, `r ≥ 0`. -/
private lemma zpow_neg_three_le (K c r : ℝ) (hK : 0 ≤ K) (hc : 1 ≤ c) (hr : 0 ≤ r) :
    K * (1 + r / c) ^ (-(3:ℤ)) ≤ K * c ^ 3 / (1 + r) ^ 3 := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have h1r : 0 ≤ 1 + r := by linarith
  have hbase : 0 < 1 + r / c := by positivity
  have hdiv : 1 + r / c = (c + r) / c := by field_simp
  have hexp : (1 + r / c) ^ 3 = (c + r) ^ 3 / c ^ 3 := by rw [hdiv, div_pow]
  have hle : (1 + r) ^ 3 / c ^ 3 ≤ (1 + r / c) ^ 3 := by
    rw [hexp]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h1r (by linarith) 3) (by positivity)
  have hpos1 : 0 < (1 + r / c) ^ 3 := pow_pos hbase 3
  have hpos2 : 0 < (1 + r) ^ 3 / c ^ 3 := by positivity
  have hinv : ((1 + r / c) ^ 3)⁻¹ ≤ c ^ 3 / (1 + r) ^ 3 := by
    have h := (inv_le_inv₀ hpos1 hpos2).mpr hle
    rwa [inv_div] at h
  have hzpow : (1 + r / c) ^ (-(3:ℤ)) = ((1 + r / c) ^ 3)⁻¹ := by simp [zpow_neg]
  rw [hzpow]
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinv hK

/-! ## The decay estimate -/

theorem tBamp_decay {N : ℕ} {a : ℝ} (ha : 0 < a) {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N a → ∀ (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)), ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨R0, hR0pos, hR0supp, G, hGnn, hGbd⟩ := chi_support_and_deriv_bound hχ hcs
  set R : ℝ := max R0 1 with hRdef
  set S : ℝ := max R (3 * a) with hSdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRS : R ≤ S := le_max_left _ _
  have hSnn : 0 ≤ S := le_of_lt (lt_of_lt_of_le hRpos hRS)
  obtain ⟨Cd, hCd0, hCd⟩ := Commons.Analysis.Fourier.fourier_decay_mul_update N R S hRpos hRS
  obtain ⟨M, hMnn, hMbd⟩ := complexified_iteratedFDeriv_bound (N := N) hSnn hΦ
  refine ⟨Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) * (2*π)^3,
    by positivity, ?_⟩
  intro x hx i p
  have hxS : ∀ j : Fin N, ‖x j‖ ≤ S := by
    intro j
    have hmem : x j ∈ Submission.BoseGases.acube a := hx j
    rw [Submission.BoseGases.mem_acube_iff] at hmem
    have habs : ∀ k : Fin 3, |(x j) k| ≤ a / 2 := by
      intro k
      rw [abs_le]
      exact ⟨by linarith [(hmem k).1], (hmem k).2⟩
    have h1 : ‖x j‖ ≤ Real.sqrt 3 * (a / 2) := norm_le_of_coord_abs_le (by positivity) habs
    have h2 : Real.sqrt 3 * (a / 2) ≤ 3 * a := by
      have hs : Real.sqrt 3 ≤ 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      nlinarith
    linarith [h1, h2, le_max_right R (3 * a)]
  have hchi3 : ContDiff ℝ 3 (fun z : ℝ³ => (χ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hPhi3 : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgsupp : ∀ z : ℝ³, (fun z : ℝ³ => (χ z : ℂ)) z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz
    have hzmem : z ∈ tsupport χ := subset_tsupport χ (by simpa using hz)
    have h1 : z ∈ Metric.closedBall (0 : ℝ³) R0 := hR0supp hzmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    exact le_trans h1 (le_max_left _ _)
  have hdec := hCd (fun z : ℝ³ => (χ z : ℂ)) G hchi3 hgsupp hGbd
      (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) M hPhi3 hMbd x hxS i ((2*π)⁻¹ • p)
  have hconv : tBamp χ p Φ i x = Submission.BoseGases.kinFT
      (fun z : ℝ³ => (χ z : ℂ) * (Φ (Function.update x i z) : ℂ)) p := by
    rw [tBamp, Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  refine hdec.trans ?_
  have hnorm_xi : ‖(2 * π)⁻¹ • p‖ = ‖p‖ / (2 * π) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2*π)⁻¹), inv_mul_eq_div]
  rw [hnorm_xi]
  have hK : 0 ≤ Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) :=
    mul_nonneg (mul_nonneg hCd0 (by positivity)) (by positivity)
  have := zpow_neg_three_le
    (Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|))
    (2*π) ‖p‖ hK (by linarith [Real.pi_gt_three]) (norm_nonneg p)
  simpa using this

end Work.SmallBoxTBWord
