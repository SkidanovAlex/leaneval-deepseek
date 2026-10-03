/-
# `Work.KMTPlan.A6.MdlCoreGainBook` — the bookkeeping and wiring of
`Work.KMTPlan.A6.MdlCoreGain` (area A6, §8 of Krause–Mirek–Tao)

This module contains **verbatim copies of every declaration of
`Submission/Work/KMTPlan/A6/MdlCoreGainEstimate.lean` except its final target**
`Work.KMTPlan.A6.MdlCoreGainEstimate`.

## Why it exists (the import cycle)

The target file `MdlCoreGainEstimate.lean` reduces `MdlCoreGain` to the frozen-`t` slice estimate
`MdlSliceCoreGain` (the paper's `model-est-2` at `(2,2,1)`), which is produced by the assembly
modules `MdlSliceCoreGainBig` / `MdlSliceCoreGainAll` / `MdlSliceCoreGainMemLp2`.  Those three
files `import Submission.Work.KMTPlan.A6.MdlCoreGainEstimate` (they use the seven bookkeeping
lemmas `Btwist_zero_left_fun`, `eLpNorm_variationalNorm_zero`, `mdlSliceJ_eq_zero_of_left_zero`,
`mdlSliceJ_eq_zero_of_right_zero`, `eq_zero_of_eLpNorm_two_eq_zero`, `memLp_two_count_of_ne_top`
and `one_le_lossWeight_mdl`), so the target file *cannot* import them: that would be an import
cycle.

This module breaks the cycle: it declares exactly the same names (same namespace
`Work.KMTPlan.A6`, hence fully interchangeable) while importing **nothing** from the target file,
so any consumer — in particular `MdlSliceCoreGainBig` and everything above it — may
`import Submission.Work.KMTPlan.A6.MdlCoreGainBook` instead of the target file.  Once that one
import line is repointed in `MdlSliceCoreGainBig.lean`, the target file can import whatever proves
`MdlSliceCoreGain` and becomes immediately provable.

`Submission/Work/KMTPlan/A6/MdlCoreGainEstimate.lean` itself now imports this module, so the
declarations are *not* duplicated: there is exactly one copy of each name.

-/
import Mathlib
import Submission.Work.KMTPlan.A6.varNorm_integral_le
import Submission.Work.KMTPlan.A6.MdlSliceIntervalIntegrable
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract
open Work.KMTAreas.A7

/-! ## Elementary bookkeeping -/

/-- The twisted bilinear multiplier vanishes when its first argument does. -/
theorem Btwist_zero_left_fun (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (k : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ 0 k = 0 := by
  funext x
  simp [Btwist]

/-- The twisted bilinear multiplier vanishes when its second argument does. -/
theorem Btwist_zero_right_fun (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h 0 = 0 := by
  funext x
  simp [Btwist]

/-- The variational norm of the zero sequence is zero. -/
theorem variationalNorm_zero {r : ℝ≥0} (hr : 1 ≤ r) :
    variationalNorm r (fun _ : ℕ => (0 : ℂ)) = 0 := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  rw [variationalNorm]
  refine le_antisymm ?_ (by simp)
  have h1 : (⨆ n, ‖(fun _ : ℕ => (0 : ℂ)) n‖ₑ) ≤ 0 := iSup_le fun n => by simp
  have h2 : (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
      ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) => (fun _ : ℕ => (0 : ℂ)) (N (i + 1))
        - (fun _ : ℕ => (0 : ℂ)) (N i))‖) ≤ 0 := by
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    have h0 : (fun i : Fin J => (fun _ : ℕ => (0 : ℂ)) (N (i + 1))
        - (fun _ : ℕ => (0 : ℂ)) (N i)) = (0 : Fin J → ℂ) := by
      funext i
      simp
    rw [h0, WithLp.toLp_zero, norm_zero, ENNReal.ofReal_zero]
  calc (⨆ n, ‖(fun _ : ℕ => (0 : ℂ)) n‖ₑ) + (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) => (fun _ : ℕ => (0 : ℂ)) (N (i + 1))
          - (fun _ : ℕ => (0 : ℂ)) (N i))‖) ≤ 0 + 0 := add_le_add h1 h2
    _ = 0 := by simp

/-- The `ℓ¹` norm of the variational norm of a vanishing family is zero. -/
theorem eLpNorm_variationalNorm_zero {r : ℝ≥0} (hr : 1 ≤ r) :
    eLpNorm (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) 1 Measure.count = 0 := by
  rw [show (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ)))
      = (fun _ : ℤ => (0 : ℝ≥0∞)) from funext fun _ => variationalNorm_zero hr]
  simp

/-- The variational norm of the model tuple is measurable in `x` (the domain `ℤ` is countable). -/
theorem aestronglyMeasurable_variationalNorm_mdlPartJ (r : ℝ≥0) (ρ : ℝ) (P : ℤ[X])
    (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    AEStronglyMeasurable (fun x : ℤ => variationalNorm r
      (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)) Measure.count :=
  (measurable_of_countable _).aestronglyMeasurable

/-! ## The `t`-integration: from the frozen-`t` slice estimate to the target

The design of `Submission/Work/KMTPlan/A6/MdlDefs.lean` splits the paper's Theorem `model-est-2`
(estimate `all-all-large-2` at `(2,2,1)`, the large-scale part of `Work.KMTContract.AreaA6`) into

* `MdlSliceCoreGain` — the *frozen-`t`* slice estimate, uniform in `t ∈ [1/2,1]`
  (`Submission/Work/KMTPlan/A6/MdlSliceCoreGainEstimate.lean`), and
* the present target `MdlCoreGain` — the same estimate for the `t`-*integrated* model tuple
  `mdlPartJ = ∫_{1/2}^1 mdlSliceJ · dt` (`mdlPartJ_eq_intervalIntegral`, proved in `MdlDefs`).

The passage from the slice form to the integrated form is the Minkowski step for the variational
norm: `V^r(∫_t H t ·) ≤ ∫⁻_t V^r(H t ·)` — this is `Work.KMTPlan.A6.varNorm_integral_le`
(proved in `A6/varNorm_integral_le.lean`), applied pointwise in `x` after
`mdlPartJ_eq_intervalIntegral`.  Integrating in `x` (Tonelli over the countable type `ℤ`, via
`lintegral_count` and `lintegral_tsum`) and using that the slice bound is a *constant* in `t` on
an interval of measure `1/2` then gives the target with the constant `K(Λ)` replaced by
`K(Λ) + 1 > 0`, which makes the case of an infinite `ℓ²`-norm on the right trivial.

The two analytic inputs of that bookkeeping are isolated in `MdlCoreGain_of_slice`: the pointwise
Minkowski step `hMink` (from `varNorm_integral_le` plus `mdlPartJ_eq_intervalIntegral`) and the
measurability `hsec` of the sliced integrand (both for `f, g ∈ ℓ²`, the only non-degenerate
case).  The three measurability facts on which they rest — the measurability and the interval
integrability of the single time slices `t ↦ mdlSliceJ … t n x`, and the passage from the slices
to the variational norm — are the isolated pieces of the `t`-integration and are *not*
established here. -/

/-! ### The trivial (degenerate) cases of the target

If `f = 0` or `g = 0` then the model tuple vanishes; if `f ∉ ℓ²` or `g ∉ ℓ²` then the right-hand
side of the target is `⊤`.  Both are used in the assembly below. -/

/-- A function with vanishing `ℓ²`-norm (for the counting measure on `ℤ`) is zero. -/
theorem eq_zero_of_eLpNorm_two_eq_zero {f : ℤ → ℂ} (h : eLpNorm f 2 Measure.count = 0) :
    f = 0 := by
  have hmeas : AEStronglyMeasurable f Measure.count := (measurable_of_countable f).aestronglyMeasurable
  have hae : f =ᵐ[Measure.count] 0 := (MeasureTheory.eLpNorm_eq_zero_iff (by norm_num)).mp h
  funext x
  by_contra hx
  have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | ¬ f y = 0} := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx
  have hzero : Measure.count {y : ℤ | ¬ f y = 0} = 0 := by
    rw [← ae_iff]
    exact hae
  have hle : Measure.count ({x} : Set ℤ) ≤ 0 := by
    rw [← hzero]
    exact MeasureTheory.measure_mono hsub
  rw [Measure.count_singleton] at hle
  exact one_ne_zero (le_zero_iff.mp hle)

/-- An `ℓ²`-membership from a non-infinite `ℓ²`-`eLpNorm` (the domain `ℤ` is countable, so the
a.e. strong measurability is automatic). -/
theorem memLp_two_count_of_ne_top {f : ℤ → ℂ} (h : eLpNorm f 2 Measure.count ≠ ⊤) :
    MemLp f 2 Measure.count :=
  MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr h)

/-- The `t`-slice of the model tuple vanishes on the zero function on the left. -/
theorem mdlSliceJ_eq_zero_of_left_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) :
    mdlSliceJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ t = 0 := by
  funext n x
  rw [mdlSliceJ_apply]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h]
    have hF : mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ (0 : ℤ → ℂ) = 0 := by
      simp [mdlF]
    rw [hF, Tle_zero_right, Btwist_zero_left_fun]
    simp
  · rw [if_neg h]
    simp

/-- The `t`-slice of the model tuple vanishes on the zero function on the right. -/
theorem mdlSliceJ_eq_zero_of_right_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) :
    mdlSliceJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ t = 0 := by
  funext n x
  rw [mdlSliceJ_apply]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h]
    have hG : mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ (0 : ℤ → ℂ) = 0 := by
      simp [mdlG]
    rw [hG, Tle_zero_right, Btwist_zero_right_fun]
    simp
  · rw [if_neg h]
    simp

/-- The model tuple vanishes on the zero function on the left. -/
theorem mdlPartJ_eq_zero_of_left_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    mdlPartJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ = 0 := by
  funext n x
  rw [mdlPartJ_eq_intervalIntegral]
  simp [mdlSliceJ_eq_zero_of_left_zero]

/-- The model tuple vanishes on the zero function on the right. -/
theorem mdlPartJ_eq_zero_of_right_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    mdlPartJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ = 0 := by
  funext n x
  rw [mdlPartJ_eq_intervalIntegral]
  simp [mdlSliceJ_eq_zero_of_right_zero]

/-- The `ℓ¹`-norm of the variational norm of the model tuple is zero when `f = 0`. -/
theorem eLpNorm_variationalNorm_mdlPartJ_left_zero {r : ℝ≥0} (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X])
    (C₀ : ℕ) (a : ℕ → ℝ≥0) (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
      mdlPartJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ n x)) 1 Measure.count = 0 := by
  have hfam : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
      mdlPartJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ n x))
      = (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
    funext x
    simp only [mdlPartJ_eq_zero_of_left_zero, Pi.zero_apply]
  rw [hfam]
  exact eLpNorm_variationalNorm_zero hr

/-- The `ℓ¹`-norm of the variational norm of the model tuple is zero when `g = 0`. -/
theorem eLpNorm_variationalNorm_mdlPartJ_right_zero {r : ℝ≥0} (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X])
    (C₀ : ℕ) (a : ℕ → ℝ≥0) (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
      mdlPartJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ n x)) 1 Measure.count = 0 := by
  have hfam : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
      mdlPartJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ n x))
      = (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
    funext x
    simp only [mdlPartJ_eq_zero_of_right_zero, Pi.zero_apply]
  rw [hfam]
  exact eLpNorm_variationalNorm_zero hr

/-! ### The pointwise Minkowski step -/

/-- The loss weight `⟨L⟩^c · 2^{cρL}` is at least `1` (`⟨L⟩ ≥ 1`, `2^{cρL} ≥ 1`). -/
theorem one_le_lossWeight_mdl {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hL : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR]
    have h0 : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (Int.natCast_nonneg l₁) (le_trans (le_max_left _ _) (le_max_left _ _))
    exact_mod_cast h0
  rw [lossWeight]
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A := Real.one_le_rpow (by linarith) hA
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- **The pointwise Minkowski step for the model tuple**: the `r`-variational norm of the
`t`-integral of the slices is at most the `t`-integral of the `r`-variational norms of the slices.
This is `varNorm_integral_le` composed with the identity `mdlPartJ = ∫_{1/2}^1 mdlSliceJ · dt`
(`mdlPartJ_eq_intervalIntegral`). -/
theorem varNorm_mdlPartJ_le_integral (r : ℝ≥0) (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (x : ℤ)
    (hint : ∀ n : ℕ, IntervalIntegrable
      (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) volume (1 / 2) 1)
    (hmeas : ∀ n : ℕ, Measurable
      (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) :
    variationalNorm r (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
  rw [funext (fun n => mdlPartJ_eq_intervalIntegral ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)]
  exact varNorm_integral_le r hr _ x hint hmeas

/-! ### The `t`-integration -/

/-- **The `t`-integration step, in the form in which the assembly uses it.**  If the variational
norm of the model tuple is bounded pointwise in `x` by the `t`-integral of the variational norms
of its frozen-`t` slices, and that `t`-integrand is measurable in `t`, then the slice estimate for
each `t` integrates to the target estimate.

The hypotheses `hMink` and `hsec` are stated for `f, g ∈ ℓ²`, which is the only non-degenerate
case of the target (if `f ∉ ℓ²` or `g ∉ ℓ²`, the right-hand side is `⊤`). -/
theorem MdlCoreGain_of_slice (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) (hr : 1 ≤ r)
    (hslice : MdlSliceCoreGain P r C₀ j₁ j₂)
    (hMink : ∀ (ρ : ℝ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) → ∀ x : ℤ,
      variationalNorm r (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)
        ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
    (hsec : ∀ (ρ : ℝ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) → ∀ x : ℤ,
      AEMeasurable (fun t : ℝ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) :
    MdlCoreGain P r C₀ j₁ j₂ := by
  obtain ⟨c, hc, A, hA, ρ₀, hρ₀, hslice'⟩ := hslice
  refine ⟨c, hc, A, hA, ρ₀, hρ₀, fun ρ hρ hρle => ?_⟩
  obtain ⟨K, hK⟩ := hslice' ρ hρ hρle
  refine ⟨fun Λ => K Λ + 1, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ₁ hQ₂ => ?_⟩
  set s : Set ℝ := Set.uIoc (1 / 2 : ℝ) 1 with hs
  set W : ℝ≥0∞ := ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
      * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) with hW
  -- The three degenerate cases: `f = 0` (a.e.), `g = 0` (a.e.), and `f ∉ ℓ²`.
  by_cases hf0 : eLpNorm f 2 Measure.count = 0
  · rw [eq_zero_of_eLpNorm_two_eq_zero hf0]
    rw [eLpNorm_variationalNorm_mdlPartJ_left_zero hr]
    exact bot_le
  by_cases hg0 : eLpNorm g 2 Measure.count = 0
  · rw [eq_zero_of_eLpNorm_two_eq_zero hg0]
    rw [eLpNorm_variationalNorm_mdlPartJ_right_zero hr]
    exact bot_le
  -- The right-hand side is `⊤` as soon as `f` or `g` is not in `ℓ²`.
  have hW0 : W ≠ 0 := by
    rw [hW, Ne, ENNReal.ofReal_eq_zero, not_le]
    refine mul_pos ?_ (Real.rpow_pos_of_pos (by norm_num) _)
    exact lt_of_lt_of_le zero_lt_one (one_le_lossWeight_mdl hA hρ.le l₁ l₂ k₁ k₂)
  have hK0 : ((K Λ + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (by positivity : (0 : ℝ≥0) < K Λ + 1))
  by_cases hfT : eLpNorm f 2 Measure.count = ⊤
  · have htop : ((K Λ + 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
        * eLpNorm g 2 Measure.count = ⊤ := by
      rw [hfT, ENNReal.mul_top (mul_ne_zero hK0 hW0), ENNReal.top_mul hg0]
    rw [htop]
    exact le_top
  by_cases hgT : eLpNorm g 2 Measure.count = ⊤
  · have htop : ((K Λ + 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
        * eLpNorm g 2 Measure.count = ⊤ := by
      rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hK0 hW0) hf0)]
    rw [htop]
    exact le_top
  -- The main case: `f, g ∈ ℓ²`.
  have hf2 : MemLp f 2 Measure.count := memLp_two_count_of_ne_top hfT
  have hg2 : MemLp g 2 Measure.count := memLp_two_count_of_ne_top hgT
  have hslice_t : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
      ≤ (K Λ : ℝ≥0∞) * W * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
    fun t ht => hK a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hQ₁ hQ₂
  have hstep1 : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => ∫⁻ t in s, variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hMink ρ a l₁ l₂ k₁ k₂ f g hf2 hg2 hQ₁ hQ₂ x)
  have hstep2 : eLpNorm (fun x : ℤ => ∫⁻ t in s, variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
      = ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count := by
    have hleft : eLpNorm (fun x : ℤ => ∫⁻ t in s, variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
        = ∑' x : ℤ, (∫⁻ t in s, variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [MeasureTheory.lintegral_count]
    have hright : (∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count)
        = ∫⁻ t in s, ∑' x : ℤ, variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
      refine lintegral_congr_ae ?_
      filter_upwards with t
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [MeasureTheory.lintegral_count]
    rw [hleft, hright]
    exact (MeasureTheory.lintegral_tsum (μ := volume.restrict s)
      (f := fun (x : ℤ) (t : ℝ) => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
      (fun x => hsec ρ a l₁ l₂ k₁ k₂ f g hf2 hg2 hQ₁ hQ₂ x)).symm
  have hstep3 : ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
      ≤ ((K Λ + 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count := by
    set C : ℝ≥0∞ := (K Λ : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
      * eLpNorm g 2 Measure.count with hC
    have hle1 : ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count ≤ C := by
      calc ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
          ≤ ∫⁻ _t in s, C := by
            refine lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
            refine hslice_t t ?_
            rw [hs] at ht
            rw [← Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
            exact Set.uIoc_subset_uIcc ht
        _ = C * volume s := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
        _ ≤ C := by
            rw [hs, Real.volume_uIoc]
            have hvv : (ENNReal.ofReal |1 - (1 / 2 : ℝ)|) ≤ (1 : ℝ≥0∞) := by
              rw [show |1 - (1 / 2 : ℝ)| = 1 / 2 by norm_num]
              exact ENNReal.ofReal_le_one.mpr (by norm_num)
            calc C * ENNReal.ofReal |1 - (1 / 2 : ℝ)| ≤ C * 1 :=
                  mul_le_mul_of_nonneg_left hvv zero_le
              _ = C := mul_one C
    have hle2 : C ≤ ((K Λ + 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
        * eLpNorm g 2 Measure.count := by
      rw [hC, ENNReal.coe_add, ENNReal.coe_one]
      gcongr
      exact le_add_of_nonneg_right zero_le
    exact hle1.trans hle2
  exact hstep1.trans (hstep2.le.trans hstep3)

/-! ## The `t`-integration, with the measurability inputs isolated

The two facts about the single time slices on which the `t`-integration rests — `Measurable` of
`t ↦ mdlSliceJ … t n x` (which is unconditional) and its `IntervalIntegrable`-ness on `[1/2,1]`
for `f, g ∈ ℓ²` — are isolated as the hypotheses `hmeas`, `hint` of the theorem below, so that
they can be supplied from separate modules. -/

/-- **The `t`-integration of the frozen-`t` slice estimate**, with the measurability and
integrability of the single time slices as explicit hypotheses. -/
theorem MdlCoreGain_of_sliceMeas (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) (hr : 1 ≤ r)
    (hslice : MdlSliceCoreGain P r C₀ j₁ j₂)
    (hmeas : ∀ (ρ : ℝ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (n : ℕ) (x : ℤ),
      Measurable (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
    (hint : ∀ (ρ : ℝ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (n : ℕ) (x : ℤ),
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
      IntervalIntegrable (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        volume (1 / 2) 1) :
    MdlCoreGain P r C₀ j₁ j₂ :=
  MdlCoreGain_of_slice P r C₀ j₁ j₂ hr hslice
    (fun ρ a l₁ l₂ k₁ k₂ f g hf hg hQ₁ hQ₂ x =>
      varNorm_mdlPartJ_le_integral r hr ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ x
        (fun n => hint ρ a l₁ l₂ k₁ k₂ f g n x hf hg hQ₁ hQ₂)
        (fun n => hmeas ρ a l₁ l₂ k₁ k₂ f g n x))
    (fun ρ a l₁ l₂ k₁ k₂ f g _hf _hg _hQ₁ _hQ₂ x =>
      (Submission.PointwiseErgodicTheorems.measurable_variationalNorm
        (lt_of_lt_of_le zero_lt_one hr)
        (u := fun (n : ℕ) (t : ℝ) => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        (fun n => hmeas ρ a l₁ l₂ k₁ k₂ f g n x)).aemeasurable.restrict)

/-- **The `t`-integration of the slice estimate with the slice measurability discharged.**  The
only remaining input besides the frozen-`t` slice estimate `MdlSliceCoreGain` is the interval
integrability of the single time slices on `[1/2,1]` for `f, g ∈ ℓ²`. -/
theorem MdlCoreGain_of_sliceMeasInt (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) (hr : 1 ≤ r)
    (hslice : MdlSliceCoreGain P r C₀ j₁ j₂)
    (hint : ∀ (ρ : ℝ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (n : ℕ) (x : ℤ),
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
      IntervalIntegrable (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        volume (1 / 2) 1) :
    MdlCoreGain P r C₀ j₁ j₂ :=
  MdlCoreGain_of_sliceMeas P r C₀ j₁ j₂ hr hslice
    (fun ρ a l₁ l₂ k₁ k₂ f g n x =>
      MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x)
    hint

/-- **The `t`-integration of the frozen-`t` slice estimate, with every input apart from the
slice estimate itself discharged.**  The only hypothesis is `MdlSliceCoreGain P r C₀ j₁ j₂` (the
separate live target `Submission/Work/KMTPlan/A6/MdlSliceCoreGainEstimate.lean`). -/
theorem MdlCoreGain_of_sliceCoreGain (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) (hr : 1 ≤ r)
    (hslice : MdlSliceCoreGain P r C₀ j₁ j₂) :
    MdlCoreGain P r C₀ j₁ j₂ :=
  MdlCoreGain_of_sliceMeasInt P r C₀ j₁ j₂ hr hslice
    (fun ρ a l₁ l₂ k₁ k₂ f g n x hf hg hk₁ hk₂ =>
      MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x hf hg hk₁ hk₂)


end

end Work.KMTPlan.A6
