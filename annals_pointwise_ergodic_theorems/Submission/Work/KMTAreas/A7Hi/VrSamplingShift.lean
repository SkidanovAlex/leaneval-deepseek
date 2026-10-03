import Mathlib
import Submission.Work.KMTAreas.A7Hi.integral_le_latticeVrSampling
import Submission.Work.BourgainPlan.IonescuWainger.exists_kernel_lattice_weight_le
import Submission.Work.KMTAreas.A7.variationalNorm_integral_le

/-!
# The shift-uniform `Vʳ` lattice sampling comparison

This file supplies the **shift-uniformity** of the quantitative Shannon/decimation comparison for
`Vʳ`-valued families, which is the ingredient every "decimation" argument in the `A7`/`A7Hi`/
`A7Rep`/`A7MixedG` fibre estimates needs and which is *not* among the two one-sided lattice
comparisons already in the tree (`A7Hi.latticeVrSampling_le_integral`,
`A7Hi.LatticeVrSamplingIntegralLe`, `A7Hi.integral_le_latticeVrSampling`): those are stated for the
lattice `ℤ`, whereas the fibre estimates have to compare the *sublattice* `a + qℤ` with `ℤ`, and
the sublattice summand `Σ_t (Vʳ_n (h_n (a + q t)))^p` is (up to the density factor `q`) the
lattice sum of the *translated* family `t ↦ h (t + a/q)`.

The content proved here is that the lattice sum `Σ_m (Vʳ_n (h_n (θ + m)))^p` is bounded by a
constant times the lattice sum `Σ_m (Vʳ_n (h_n m))^p`, **uniformly in the shift `θ ∈ ℝ`**, for a
`[-β,β]`-band-limited Schwartz family, `β < 1/2`.  The proof is the one from the quantitative
Shannon sampling theorem: the reproducing identity `h t = Σ_m ψ (t - m) h m` (with `𝓕ψ ≡ 1` on the
band and `𝓕ψ ≡ 0` off the Nyquist band `[-1/2,1/2]`), the subadditivity of the variational norm
across the resulting absolutely convergent series, and the weighted Schur/Hölder step with the
lattice weight `(m ↦ ‖ψ (θ + m - j)‖)`, whose row *and* column sums are bounded by the lattice mass
of `ψ` (`Commons.Analysis.Fourier.schwartz_lattice_sum_bound`).

As a corollary we record the two "density" comparisons between the sublattice `a + qℤ` and the
full lattice `ℤ`, in the form in which the decimation arguments consume them.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## The sampling window of a general band, and the lattice mass of a Schwartz function -/

/-- **A sampling window for the band `[-β,β]`**, `0 < β < 1/2`: a Schwartz function whose Fourier
transform equals `1` on `[-β,β]` and vanishes off the Nyquist band `[-1/2,1/2]`.  It is the inverse
Fourier transform of a smooth bump of inner radius `β` and outer radius `(β + 1/2)/2`. -/
theorem exists_samplingWindowHi (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 2) :
    ∃ ψ : SchwartzMap ℝ ℂ,
      (∀ ξ ∈ Set.Icc (-β) β, FourierTransform.fourier ψ ξ = 1) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2:ℝ)) (1/2) → FourierTransform.fourier ψ ξ = 0) := by
  have hr : β < (β + 1/2) / 2 := by linarith
  have hr' : (β + 1/2) / 2 < 1/2 := by linarith
  let bump : ContDiffBump (0:ℝ) := ⟨β, (β + 1/2) / 2, hβ, hr⟩
  have hdiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => ((bump x : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (bump x : ℝ)) := bump.contDiff
    exact Complex.ofRealCLM.contDiff.comp h1
  have hcs : HasCompactSupport (fun x : ℝ => ((bump x : ℝ) : ℂ)) :=
    bump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let χ : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hdiff
  let ψ : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv χ
  have hcoe : (ψ : ℝ → ℂ) = FourierTransformInv.fourierInv (χ : ℝ → ℂ) := by
    funext a
    exact congrFun (SchwartzMap.fourierInv_coe χ) a
  have hFint : MeasureTheory.Integrable (FourierTransform.fourier (χ : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 χ).integrable
  have hfun : FourierTransform.fourier (FourierTransformInv.fourierInv (χ : ℝ → ℂ))
      = (χ : ℝ → ℂ) :=
    χ.continuous.fourier_fourierInv_eq χ.integrable hFint
  have h1 : ∀ ξ : ℝ, FourierTransform.fourier ψ ξ = (χ : ℝ → ℂ) ξ := by
    intro ξ
    rw [SchwartzMap.fourier_coe, hcoe]
    exact congrFun hfun ξ
  have hrIn : bump.rIn = β := rfl
  have hrOut : bump.rOut = (β + 1/2) / 2 := rfl
  refine ⟨ψ, ?_, ?_⟩
  · intro ξ hξ
    rw [h1 ξ, HasCompactSupport.toSchwartzMap_toFun]
    have hmem : ξ ∈ Metric.closedBall (0:ℝ) bump.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩ <;> rw [hrIn] <;> linarith [hξ.1, hξ.2]
    exact_mod_cast bump.one_of_mem_closedBall hmem
  · intro ξ hξ
    rw [h1 ξ, HasCompactSupport.toSchwartzMap_toFun]
    have hmem : bump.rOut ≤ dist ξ (0:ℝ) := by
      rw [hrOut, dist_zero_right, Real.norm_eq_abs]
      rcases lt_or_ge ξ (-(1/2:ℝ)) with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have h3 : (1/2:ℝ) < ξ := by
          by_contra hc
          exact hξ ⟨by linarith, by linarith⟩
        rw [abs_of_nonneg (by linarith)]; linarith
    exact_mod_cast bump.zero_of_le_dist hmem

/-- **The lattice mass of a Schwartz function is finite and uniform in the centre.**  For every
`ψ : SchwartzMap ℝ ℂ` there is `A > 0` with `Σ_m ‖ψ (t - m)‖ₑ ≤ A` and `Σ_m ‖ψ (t + m)‖ₑ ≤ A` for
every `t : ℝ`. -/
theorem latticeMassHi (ψ : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧
      (∀ t : ℝ, (∑' n : ℤ, ‖ψ (t - (n:ℝ))‖ₑ) ≤ ENNReal.ofReal A) ∧
      (∀ t : ℝ, (∑' n : ℤ, ‖ψ (t + (n:ℝ))‖ₑ) ≤ ENNReal.ofReal A) := by
  obtain ⟨M, hMpos, hM⟩ := Commons.Analysis.Fourier.schwartz_lattice_sum_bound ψ
  obtain ⟨B, hBpos, hBdecay⟩ := Commons.Analysis.Fourier.schwartzMap_real_decay ψ 2
  have hsumAbs : ∀ t : ℝ, Summable (fun n : ℤ => (1 + |t - (n:ℝ)|) ^ (-(2:ℝ))) := by
    intro t
    exact Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
      (fun n => Commons.Analysis.Fourier.lattice_decay_pointwise t n)
      (Commons.Analysis.Fourier.summable_int_one_div_abs_shift_half_sq ⌊t⌋)
  have hsumNorm : ∀ t : ℝ, Summable (fun n : ℤ => ‖ψ (t - (n:ℝ))‖) := by
    intro t
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => hBdecay (t - (n:ℝ))) ((hsumAbs t).mul_left B)
  refine ⟨M, hMpos, ?_, ?_⟩
  · intro t
    have hconv : (∑' n : ℤ, ‖ψ (t - (n:ℝ))‖ₑ)
        = ∑' n : ℤ, ENNReal.ofReal ‖ψ (t - (n:ℝ))‖ :=
      tsum_congr (fun n => (ofReal_norm _).symm)
    rw [hconv, ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hsumNorm t)]
    exact ENNReal.ofReal_le_ofReal (hM t)
  · intro t
    have hconv : (∑' n : ℤ, ‖ψ (t + (n:ℝ))‖ₑ)
        = ∑' n : ℤ, ENNReal.ofReal ‖ψ (t + (n:ℝ))‖ :=
      tsum_congr (fun n => (ofReal_norm _).symm)
    have hneg : (∑' n : ℤ, ENNReal.ofReal ‖ψ (t + (n:ℝ))‖)
        = ∑' n : ℤ, ENNReal.ofReal ‖ψ (t - (n:ℝ))‖ := by
      rw [← Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => ENNReal.ofReal ‖ψ (t - (n:ℝ))‖)]
      refine tsum_congr (fun n => ?_)
      rw [Equiv.neg_apply]
      exact congrArg (fun u => ENNReal.ofReal ‖ψ u‖) (by push_cast; ring)
    rw [hconv, hneg, ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hsumNorm t)]
    exact ENNReal.ofReal_le_ofReal (hM t)

/-! ## The weighted Schur (weighted-Hölder) step on `ℤ × ℤ` -/

/-- Weighted Schur test for a `ℤ × ℤ`-matrix of `ℝ≥0∞`-weights: if the row sums are bounded by `A`
and the column sums by `B`, then `Σ_x (Σ_m W x m * v m)^p ≤ ofReal (A^(p-1) * B) * Σ_m v m^p`.
This is the weighted power-mean (Hölder) inequality applied at each row, followed by Tonelli and the
column bound. -/
theorem weightedSchurHi (p : ℝ) (hp : 1 < p) {W : ℤ → ℤ → ENNReal} {v : ℤ → ENNReal}
    {A B : ℝ} (hA : 0 ≤ A)
    (hrow : ∀ x : ℤ, (∑' m : ℤ, W x m) ≤ ENNReal.ofReal A)
    (hcol : ∀ m : ℤ, (∑' x : ℤ, W x m) ≤ ENNReal.ofReal B) :
    (∑' x : ℤ, (∑' m : ℤ, W x m * v m) ^ p)
      ≤ ENNReal.ofReal (A ^ (p - 1) * B) * (∑' m : ℤ, v m ^ p) := by
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hpoint : ∀ x : ℤ, (∑' m : ℤ, W x m * v m) ^ p
      ≤ ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, W x m * v m ^ p) := by
    intro x
    have h := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral_measure
      (Measure.count : Measure ℤ) hp (f := v) (w := fun m : ℤ => W x m)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    simp only [MeasureTheory.lintegral_count] at h
    rw [tsum_congr (fun m : ℤ => mul_comm (v m) (W x m)),
      tsum_congr (fun m : ℤ => mul_comm (v m ^ p) (W x m))] at h
    exact h.trans (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hrow x) hp1) bot_le)
  calc (∑' x : ℤ, (∑' m : ℤ, W x m * v m) ^ p)
      ≤ ∑' x : ℤ, ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, W x m * v m ^ p) :=
        ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal A ^ (p - 1) * (∑' x : ℤ, ∑' m : ℤ, W x m * v m ^ p) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, (∑' x : ℤ, W x m) * v m ^ p) := by
        congr 1
        rw [ENNReal.tsum_comm]
        exact tsum_congr (fun m => ENNReal.tsum_mul_right)
    _ ≤ ENNReal.ofReal A ^ (p - 1) * (∑' m : ℤ, ENNReal.ofReal B * v m ^ p) := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        exact ENNReal.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_right (hcol m) bot_le)
    _ = ENNReal.ofReal A ^ (p - 1) * (ENNReal.ofReal B * (∑' m : ℤ, v m ^ p)) := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (A ^ (p - 1) * B) * (∑' m : ℤ, v m ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA hp1, ENNReal.ofReal_mul (Real.rpow_nonneg hA _),
          mul_assoc]

/-! ## The shift-uniform lattice comparison -/

/-! ## The shifted "samples ≤ integral" comparison, and the two-sided form -/

end

end Work.KMTAreas.A7Hi
