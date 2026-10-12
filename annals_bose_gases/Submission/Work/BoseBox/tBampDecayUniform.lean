import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.SmallBoxTBWord.tBamp_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniform `(1+‖p‖)⁻³` decay of the windowed amplitude, with uniform data

`tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})dz` is the `p`-convention Fourier
transform of `z ↦ χ(z)Φ(x_{i←z})`.  The core Fourier-decay estimate
`Commons.Analysis.Fourier.fourier_decay_mul_update` bounds the Fourier transform of
`g·(Φ∘(x_{i←·}))` by `C·(1+Σ|G|)·(1+Σ|M|)·(1+‖ξ‖)⁻³` from *finite-order* (order `3`)
data: a support radius `R` for `g`, derivative bounds `G` on `g`, and derivative bounds
`M` on `Φ` on the ball of radius `S`, with `R ≤ S` (so that the update `x_{i←z}` stays in
that ball).

This file extracts the corresponding statement for `tBamp` itself: from a *uniform family*
of data `(R, S, G, M)` valid for every `t : ι`, one gets a single constant `C` with
`‖tBamp (χ t) p (Φ t) i x‖ ≤ C/(1+‖p‖)³` for all `t`, all `x` with `‖x j‖ ≤ S`, all `i`, `p`.

This is the version needed when the windows `χ t` are only `C³` and are not known to be
smooth/compactly supported (e.g. the sliding cutoffs), so that the sharp `tBamp_decay`
(which needs `C^∞` + compact support) cannot be applied directly.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.BoseBox

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

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

theorem tBampDecayUniform {N : ℕ} {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    {ι : Type*} {χ : ι → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : ι → Submission.BoseGases.X N → ℝ} {G M : ℕ → ℝ}
    (hχcd : ∀ t : ι, ContDiff ℝ 3 (fun z : EuclideanSpace ℝ (Fin 3) => (χ t z : ℂ)))
    (hχsupp : ∀ (t : ι) (z : EuclideanSpace ℝ (Fin 3)), χ t z ≠ 0 → ‖z‖ ≤ R)
    (hχG : ∀ (t : ι) (k : ℕ), k ≤ 3 → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin 3) => (χ t z : ℂ)) z‖ ≤ G k)
    (hΦcd : ∀ t : ι, ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Φ t y : ℂ)))
    (hΦM : ∀ (t : ι) (k : ℕ), k ≤ 3 → ∀ y : Submission.BoseGases.X N,
      (∀ j : Fin N, ‖y j‖ ≤ S) →
      ‖iteratedFDeriv ℝ k (fun y : Submission.BoseGases.X N => (Φ t y : ℂ)) y‖ ≤ M k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ι) (x : Submission.BoseGases.X N), (∀ j : Fin N, ‖x j‖ ≤ S) →
      ∀ (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)),
      ‖Work.SmallBoxTBWord.tBamp (χ t) p (Φ t) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨Cd, hCd0, hCd⟩ := Commons.Analysis.Fourier.fourier_decay_mul_update N R S hR hRS
  refine ⟨Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) * (2*π)^3,
    by positivity, ?_⟩
  intro t x hx i p
  have hchi3 : ContDiff ℝ 3 (fun z : ℝ³ => (χ t z : ℂ)) := hχcd t
  have hPhi3 : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Φ t y : ℂ)) := hΦcd t
  have hgsupp : ∀ z : ℝ³, (fun z : ℝ³ => (χ t z : ℂ)) z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz
    exact hχsupp t z (by simpa [Ne, Complex.ofReal_eq_zero] using hz)
  have hGbd : ∀ k, k ≤ 3 → ∀ z : ℝ³,
      ‖iteratedFDeriv ℝ k (fun z : ℝ³ => (χ t z : ℂ)) z‖ ≤ G k :=
    fun k hk z => hχG t k hk z
  have hMbd : ∀ k, k ≤ 3 → ∀ y : Submission.BoseGases.X N, (∀ j : Fin N, ‖y j‖ ≤ S) →
      ‖iteratedFDeriv ℝ k (fun y : Submission.BoseGases.X N => (Φ t y : ℂ)) y‖ ≤ M k :=
    fun k hk y hy => hΦM t k hk y hy
  have hdec := hCd (fun z : ℝ³ => (χ t z : ℂ)) G hchi3 hgsupp hGbd
      (fun y : Submission.BoseGases.X N => (Φ t y : ℂ)) M hPhi3 hMbd x hx i ((2*π)⁻¹ • p)
  have hconv : Work.SmallBoxTBWord.tBamp (χ t) p (Φ t) i x = Submission.BoseGases.kinFT
      (fun z : ℝ³ => (χ t z : ℂ) * (Φ t (Function.update x i z) : ℂ)) p := by
    rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
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

end Work.BoseBox
