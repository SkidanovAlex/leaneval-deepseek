import Mathlib
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound
import Submission.Commons.Analysis.Fourier.fourier_comp_mul_left

/-!
# The sampling kernel of the decimated lattice-sampling comparison

This module fixes the *analytical* objects used by the `Vʳ`-decimated sampling comparison
`Work.KMTAreas.A7Rep.decimatedVrSamplingSeqBdd`.

The comparison compares the `ℓ^p(ℤ; Vʳ)`-norm of a band-limited family with the corresponding norm
over the sublattice `qℤ + r₀`, weighted by the density `q`.  The mechanism is the classical
*quantitative Shannon sampling theorem*: if `γ` is integrable, continuous and band-limited to
`[-β,β]` with `β q ≤ 1/4`, then the rescaled function `u ↦ γ (q u + r₀)` is band-limited to
`[-1/4,1/4]`, hence reproduced from its unit-lattice samples by the *fixed* kernel `K = 𝓕⁻χ`, where
`χ` is a Schwartz bump which is `1` on `[-1/4,1/4]` and `0` outside `[-1/2,1/2]`:

  `γ (q u + r₀) = ∑_m K (u - m) · γ (q m + r₀)`.

Because `β q ≤ 1/4` is a *uniform* gap below the Nyquist rate `1/2`, the kernel `K` (hence all the
lattice weights) does not depend on `β` or `q`.

## Contents

* `exists_schwartzMap_eq_one_Icc_tight` — a Schwartz bump equal to `1` on `[-c₀,c₀]` and *vanishing
  outside* `[-1/2,1/2]` (the tightness of the support is what removes the aliasing error).
* `samplingChi`, `samplingKernel = 𝓕⁻ samplingChi` — the fixed cutoff and kernel at `c₀ = 1/4`.
* the two quantitative lattice bounds on `K`: its column (row) sum `∑_m ‖K (u - m)‖` is bounded,
  and it decays like `(1+u²)⁻¹`.
-/

namespace Work.KMTAreas.A7Rep

open MeasureTheory
open scoped FourierTransform ENNReal BigOperators ContDiff

noncomputable section

/-! ## The tight Schwartz bump -/

/-- **A Schwartz bump which is `1` on `[-c₀,c₀]` and vanishes outside `[-1/2,1/2]`**, for
`0 < c₀ < 1/2`.  (The published `Commons.Analysis.Fourier.exists_schwartzMap_eq_one_Icc` produces a
bump of radius `a+1`, which is far too wide for the aliasing estimate; here the outer radius is
squeezed below the Nyquist rate.) -/
theorem exists_schwartzMap_eq_one_Icc_tight (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 2) :
    ∃ χ : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, ξ ∈ Set.Icc (-c₀) c₀ → (χ : ℝ → ℂ) ξ = 1) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) → (χ : ℝ → ℂ) ξ = 0) := by
  set rOut : ℝ := (c₀ + 1 / 2) / 2 with hrOut_def
  set rIn : ℝ := (c₀ + rOut) / 2 with hrIn_def
  have hrOut_pos : 0 < rOut := by rw [hrOut_def]; linarith
  have hrOut_lt : rOut < 1 / 2 := by rw [hrOut_def]; linarith
  have hrIn_lt_rOut : rIn < rOut := by rw [hrIn_def]; linarith
  have hrIn_pos : 0 < rIn := by rw [hrIn_def]; linarith
  have hc₀_lt_rIn : c₀ < rIn := by rw [hrIn_def]; linarith
  let bump : ContDiffBump (0 : ℝ) := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  let χ : ℝ → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hχ_diff : ContDiff ℝ ∞ χ :=
    (Complex.ofRealCLM.contDiff (n := ∞)).comp (bump.contDiff (n := ⊤))
  have hχ_cs : HasCompactSupport χ :=
    bump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨hχ_cs.toSchwartzMap hχ_diff, ?_, ?_⟩
  · intro ξ hξ
    rw [HasCompactSupport.toSchwartzMap_toFun]
    show ((bump ξ : ℝ) : ℂ) = 1
    rw [bump.one_of_mem_closedBall]
    · norm_num
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  · intro ξ hξ
    rw [HasCompactSupport.toSchwartzMap_toFun]
    show ((bump ξ : ℝ) : ℂ) = 0
    rw [bump.zero_of_le_dist]
    · norm_num
    · rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
      have h1 : 1 / 2 < |ξ| := by
        by_contra hle
        rw [not_lt] at hle
        have h2 := abs_le.mp hle
        exact hξ ⟨by linarith [h2.1], by linarith [h2.2]⟩
      linarith

/-! ## The fixed cutoff and kernel at the gap `1/4` -/

/-- The fixed Schwartz cutoff `χ` of the sampling kernel: `1` on `[-1/4,1/4]`, vanishing outside
`[-1/2,1/2]`. -/
def samplingChi : SchwartzMap ℝ ℂ :=
  Classical.choose
    (exists_schwartzMap_eq_one_Icc_tight (1 / 4) (by norm_num) (by norm_num))

/-- The defining property of `samplingChi`: it is `1` on `[-1/4,1/4]`. -/
theorem samplingChi_one :
    ∀ ξ : ℝ, ξ ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → (samplingChi : ℝ → ℂ) ξ = 1 :=
  (Classical.choose_spec
    (exists_schwartzMap_eq_one_Icc_tight (1 / 4) (by norm_num) (by norm_num))).1

/-- The defining property of `samplingChi`: it vanishes outside `[-1/2,1/2]`. -/
theorem samplingChi_zero :
    ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) → (samplingChi : ℝ → ℂ) ξ = 0 :=
  (Classical.choose_spec
    (exists_schwartzMap_eq_one_Icc_tight (1 / 4) (by norm_num) (by norm_num))).2

/-- **The sampling kernel** `K = 𝓕⁻χ`: the reproducing kernel of the band `[-1/4,1/4]` used by the
decimated sampling comparison. -/
def samplingKernel : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv samplingChi

/-- The kernel `samplingKernel` is `𝓕⁻` of `samplingChi` as a function. -/
theorem samplingKernel_coe :
    (samplingKernel : ℝ → ℂ)
      = FourierTransformInv.fourierInv (samplingChi : ℝ → ℂ) :=
  SchwartzMap.fourierInv_coe samplingChi

/-! ## The quantitative lattice bounds -/

/-- Polynomial decay of the sampling kernel: `‖K u‖ ≤ C / (1+u²)`. -/
theorem samplingKernel_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, ‖(samplingKernel : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) :=
  Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq samplingKernel

/-- Decay of the sampling kernel in the form used by the lattice estimates:
`‖K u‖ ≤ B * (1 + |u|) ^ (-(2:ℝ))`. -/
theorem samplingKernel_decay_abs :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, ‖(samplingKernel : ℝ → ℂ) u‖ ≤ B * (1 + |u|) ^ (-(2:ℝ)) :=
  Commons.Analysis.Fourier.schwartzMap_real_decay samplingKernel 2

/-- **The uniform lattice bound for the sampling kernel**: the sum of `‖K (u - m)‖` over the
lattice is bounded uniformly in `u`.  This is the weight bound used by the row/column estimates of
the sampling comparison. -/
theorem samplingKernel_latticeBound :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℝ, ∑' m : ℤ, ‖(samplingKernel : ℝ → ℂ) (u - (m : ℝ))‖ ≤ A :=
  Commons.Analysis.Fourier.schwartz_lattice_sum_bound samplingKernel

/-- **The `ℝ≥0∞`-form of the uniform lattice bound for the sampling kernel**, which is the form
used by the `ℓ^p` estimates: `∑'_m ‖K (u - m)‖ₑ ≤ ofReal A` for every `u`, with a fixed `A`. -/
theorem samplingKernel_latticeBoundENN :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℝ,
      (∑' m : ℤ, ‖(samplingKernel : ℝ → ℂ) (u - (m : ℝ))‖ₑ) ≤ ENNReal.ofReal A := by
  obtain ⟨A, hApos, hAlat⟩ := samplingKernel_latticeBound
  obtain ⟨B, hBpos, hBdec⟩ := samplingKernel_decay_abs
  refine ⟨A, hApos, fun u => ?_⟩
  have hsum : Summable (fun m : ℤ => ‖(samplingKernel : ℝ → ℂ) (u - (m : ℝ))‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      ((Commons.Analysis.Fourier.summable_int_one_div_abs_shift_half_sq ⌊u⌋).mul_left B)
    refine le_trans (hBdec (u - (m : ℝ))) (mul_le_mul_of_nonneg_left ?_ hBpos.le)
    simpa only [one_div] using Commons.Analysis.Fourier.lattice_decay_pointwise u m
  rw [show (∑' m : ℤ, ‖(samplingKernel : ℝ → ℂ) (u - (m : ℝ))‖ₑ)
        = ∑' m : ℤ, ENNReal.ofReal ‖(samplingKernel : ℝ → ℂ) (u - (m : ℝ))‖ from
      tsum_congr (fun m => by simp),
    ← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) hsum]
  exact ENNReal.ofReal_le_ofReal (hAlat u)

end

end Work.KMTAreas.A7Rep
