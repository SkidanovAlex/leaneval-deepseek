import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution

/-!
# The band-limited reproducing kernel on `ℝ`

The main result of this file, `band_limited_reproducing_kernel`, produces a single kernel
`K : ℝ → ℂ` which is integrable, decays like `(1 + x ^ 2)⁻¹`, and reproduces every
`L¹`-function `g` whose Fourier transform is supported in the band `[-1/2, 1/2]`:

`g x = ∫ y, g y * K (x - y)`  at every continuity point `x` of `g`.

It is the special case `a = 1/2` of the general-band statement
`band_limited_reproducing_kernel_general`.

Take `K = 𝓕⁻ χ` for a smooth bump `χ` which is identically `1` on the band (so that
`𝓕 K = χ`); the reproducing identity is then the Fourier inversion formula for the
band-limited function `g` combined with the elementary identity
`𝓕⁻ (χ * 𝓕 g) = g ⋆ (𝓕⁻ χ)` (`fourierInv_mul_fourier_eq_convolution`).  Since `χ` is
compactly supported and smooth, `K = 𝓕⁻ χ` is Schwartz, hence integrable with the
required polynomial decay.

## Main results

* `exists_schwartzMap_eq_one_Icc`: for `a > 0`, a Schwartz multiplier equal to `1` on
  the band `[-a, a]`.
* `schwartzMap_decay_one_add_sq`: polynomial decay of a complex-valued Schwartz function.
* `bandlimited_reconstruction_real`: the reproducing identity on `ℝ`, general band.
* `band_limited_reproducing_kernel_general`: the existence of the kernel, general band.
* `band_limited_reproducing_kernel`: the band `[-1/2, 1/2]`.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace

noncomputable section

/-- For every `a` there is a Schwartz function on `ℝ` which is identically `1` on the band
`[-a, a]`: the smooth bump of radius `a + 1`. -/
lemma exists_schwartzMap_eq_one_Icc (a : ℝ) (ha : 0 < a) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ ξ : ℝ, ξ ∈ Set.Icc (-a) a → (φ : ℝ → ℂ) ξ = 1 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨a + 1, a + 2, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hχ_diff : ContDiff ℝ ∞ χ :=
    (Complex.ofRealCLM.contDiff (n := ∞)).comp (bump.contDiff (n := ⊤))
  have hχ_cs : HasCompactSupport χ :=
    bump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨hχ_cs.toSchwartzMap hχ_diff, ?_⟩
  intro ξ hξ
  rw [HasCompactSupport.toSchwartzMap_toFun]
  have hmem : ξ ∈ Metric.closedBall (0 : ℝ) bump.rIn := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    have : bump.rIn = a + 1 := rfl
    rw [this]
    exact abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hb1 : (bump : ℝ → ℝ) ξ = 1 := bump.one_of_mem_closedBall hmem
  show ((bump ξ : ℝ) : ℂ) = 1
  rw [hb1]; norm_num

/-- Polynomial decay of a complex-valued Schwartz function on `ℝ`:
there is `C > 0` with `‖K x‖ ≤ C / (1 + x ^ 2)` for every `x`. -/
lemma schwartzMap_decay_one_add_sq (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2) := by
  set S : ℝ := ((Finset.Iic ((2, 0) : ℕ × ℕ)).sup
    (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2)) K with hS
  refine ⟨max (4 * S) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have hb : (1 + |x|) ^ 2 * ‖K x‖ ≤ 4 * S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((2, 0) : ℕ × ℕ))
      (k := 2) (n := 0) le_rfl le_rfl K x
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_zero, ← hS] at h
    norm_num at h
    exact h
  have hden2 : (0:ℝ) < 1 + x ^ 2 := by positivity
  rw [le_div_iff₀ hden2]
  have h1 : (1:ℝ) + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  calc ‖K x‖ * (1 + x ^ 2) ≤ ‖K x‖ * (1 + |x|) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (1 + |x|) ^ 2 * ‖K x‖ := mul_comm _ _
    _ ≤ 4 * S := hb
    _ ≤ max (4 * S) 1 := le_max_left _ _

/-- **Reproducing identity on `ℝ`.**  If `g` is integrable, has Fourier transform vanishing
outside the band `[-a, a]`, and `m` is a Schwartz function equal to `1` on that band, then at
every continuity point `x` of `g`,
`g x = ∫ y, g y * (𝓕⁻ m) (x - y)`. -/
theorem bandlimited_reconstruction_real (a : ℝ) (m : SchwartzMap ℝ ℂ)
    (hm : ∀ ξ : ℝ, ξ ∈ Set.Icc (-a) a → (m : ℝ → ℂ) ξ = 1)
    (g : ℝ → ℂ) (hg : Integrable g)
    (hbl : ∀ ξ : ℝ, ξ ∉ Set.Icc (-a) a → 𝓕 g ξ = 0)
    (x : ℝ) (hx : ContinuousAt g x) :
    g x = ∫ y : ℝ, g y * (𝓕⁻ (m : ℝ → ℂ)) (x - y) := by
  have hm_int : Integrable (m : ℝ → ℂ) := m.integrable
  have h𝓕g_cont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg
  have h𝓕g_supp : Function.support (𝓕 g) ⊆ Set.Icc (-a) a := by
    intro ξ hξ
    by_contra h
    exact hξ (hbl ξ h)
  have h𝓕g_int : Integrable (𝓕 g) :=
    h𝓕g_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc h𝓕g_supp)
  have hmul : (fun ξ => (m : ℝ → ℂ) ξ * 𝓕 g ξ) = 𝓕 g := by
    funext ξ
    by_cases h : ξ ∈ Set.Icc (-a) a
    · rw [hm ξ h, one_mul]
    · rw [hbl ξ h, mul_zero]
  calc g x = 𝓕⁻ (𝓕 g) x := (hg.fourierInv_fourier_eq h𝓕g_int hx).symm
    _ = 𝓕⁻ (fun ξ => (m : ℝ → ℂ) ξ * 𝓕 g ξ) x := by rw [hmul]
    _ = ∫ y : ℝ, g y * 𝓕⁻ (m : ℝ → ℂ) (x - y) :=
        fourierInv_mul_fourier_eq_convolution hm_int hg x

/-- **The band-limited reproducing kernel, general band.**  For every `a` there is an integrable
kernel `K : ℝ → ℂ` with `‖K x‖ ≤ C / (1 + x ^ 2)` which reproduces every integrable function
whose Fourier transform vanishes outside `[-a, a]`, at each of its continuity points. -/
theorem band_limited_reproducing_kernel_general (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ → ℂ, MeasureTheory.Integrable K ∧ (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2)) ∧
      ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-a) a → FourierTransform.fourier g ξ = 0) →
        ∀ x : ℝ, ContinuousAt g x → g x = ∫ y : ℝ, g y * K (x - y) := by
  obtain ⟨m, hm⟩ := exists_schwartzMap_eq_one_Icc a ha
  refine ⟨fun z => ((𝓕⁻ m : SchwartzMap ℝ ℂ) : ℝ → ℂ) z, (𝓕⁻ m).integrable, ?_, ?_⟩
  · obtain ⟨C, hC, hb⟩ := schwartzMap_decay_one_add_sq (𝓕⁻ m)
    exact ⟨C, hC, fun x => hb x⟩
  · intro g hg hbl x hx
    rw [bandlimited_reconstruction_real a m hm g hg hbl x hx]
    apply integral_congr_ae
    filter_upwards with y
    rw [SchwartzMap.fourierInv_coe]

theorem band_limited_reproducing_kernel :
    ∃ K : ℝ → ℂ, MeasureTheory.Integrable K ∧ (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2)) ∧
      ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier g ξ = 0) →
        ∀ x : ℝ, ContinuousAt g x → g x = ∫ y : ℝ, g y * K (x - y) :=
  band_limited_reproducing_kernel_general (1 / 2) (by norm_num)

end

end Commons.Analysis.Fourier