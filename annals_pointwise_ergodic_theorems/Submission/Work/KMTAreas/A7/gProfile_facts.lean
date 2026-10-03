/-
# Facts about the fixed frequency profile `gProfile d k₂` of the `g`-side bump

`gProfile` (`Submission/Work/KMTAreas/A7/randSymbG_aux.lean`) is the fixed profile of the `g`-side
randomised cut-off: with `σ = gScale d N k₂` one has
`varphitildeN d N k₂ ξ = gProfile d k₂ (σ ξ)`.

* `k₂ = 0`: `gProfile d 0 = η = kmtEta`, the KMT cutoff `1` on `[-1/2,1/2]`, `0` off `[-1,1]`;
* `k₂ ≥ 1`: `gProfile d k₂ = η - η(2^d ·)`, which vanishes on `[-2^{-d-1}, 2^{-d-1}]` and is
  supported in `[-1,1]`.

This module records the five elementary facts about it (smoothness, support, the value at `0`, the
constancy near `0`, and the sup bound `‖gProfile d k₂ u‖ ≤ 1`) used by the Mikhlin-bound analysis of
the symbol.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux

set_option autoImplicit false

namespace Work.KMTAreas.A7

open Work.KMTContract

/-- The KMT cutoff `η = kmtEta` is `𝒞²` (indeed `𝒞^∞`), being the complexification of a
`ContDiffBump`. -/
private lemma contDiff_kmtEta_ : ContDiff ℝ 2 kmtEta := by
  show ContDiff ℝ 2 fun x : ℝ => ((kmtBump x : ℝ) : ℂ)
  exact Complex.ofRealCLM.contDiff.comp kmtBump.contDiff

/-- The `k₂ ≥ 1` profile `η - η(2^d ·)` vanishes off `[-1,1]`. -/
private lemma kmtEta_sub_rescale_eq_zero (d : ℕ) (u : ℝ) (hu : 1 ≤ |u|) :
    kmtEta u - kmtEta ((2:ℝ)^d * u) = 0 := by
  rw [kmtEta_zero hu]
  have h2 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have h3 : 1 ≤ |(2:ℝ)^d * u| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^d)]
    nlinarith [h2, hu, abs_nonneg u]
  rw [kmtEta_zero h3, sub_zero]

/-- The `k₂ ≥ 1` profile `η - η(2^d ·)` vanishes on `[-2^{-d-1}, 2^{-d-1}]`. -/
private lemma kmtEta_sub_rescale_eq_zero_of_le (d : ℕ) (u : ℝ)
    (hu : |u| ≤ 1/(2 * (2:ℝ)^d)) : kmtEta u - kmtEta ((2:ℝ)^d * u) = 0 := by
  have h2 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have h2pos : (0:ℝ) < (2:ℝ)^d := by positivity
  have hle : 1/(2 * (2:ℝ)^d) ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
    linarith
  have hu' : |u| ≤ 1/2 := le_trans hu hle
  have h3 : |(2:ℝ)^d * u| ≤ 1/2 := by
    rw [abs_mul, abs_of_nonneg h2pos.le]
    calc (2:ℝ)^d * |u| ≤ (2:ℝ)^d * (1/(2 * (2:ℝ)^d)) :=
          mul_le_mul_of_nonneg_left hu h2pos.le
      _ = 1/2 := by field_simp
  rw [kmtEta_one hu', kmtEta_one h3, sub_self]

/-- The `k₂ ≥ 1` profile `η - η(2^d ·)` takes values in `[-1,1]` (it is the difference of two
`[0,1]`-valued real functions). -/
private lemma norm_kmtEta_sub_le (a b : ℝ) : ‖kmtEta a - kmtEta b‖ ≤ 1 := by
  have ha : 0 ≤ kmtBump a := kmtBump.nonneg
  have ha' : kmtBump a ≤ 1 := kmtBump.le_one
  have hb : 0 ≤ kmtBump b := kmtBump.nonneg
  have hb' : kmtBump b ≤ 1 := kmtBump.le_one
  show ‖(((kmtBump a : ℝ) : ℂ) - ((kmtBump b : ℝ) : ℂ))‖ ≤ 1
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith

/-- **The elementary facts about the `g`-side frequency profile `gProfile d k₂`:**
smoothness, support in `[-1,1]`, the value at `0`, constancy on the ball where the profile is
non-vanishing, and the sup bound `1`. -/
theorem gProfile_facts (d k₂ : ℕ) :
    ContDiff ℝ 2 (gProfile d k₂) ∧
    (∀ u : ℝ, 1 ≤ |u| → gProfile d k₂ u = 0) ∧
    gProfile d k₂ 0 = (if k₂ = 0 then 1 else 0) ∧
    (∀ u : ℝ, |u| ≤ (if k₂ = 0 then 1/2 else 1/(2 * (2 : ℝ)^d)) →
      gProfile d k₂ u = gProfile d k₂ 0) ∧
    (∀ u : ℝ, ‖gProfile d k₂ u‖ ≤ 1) := by
  have hdef : gProfile d k₂ = if k₂ = 0 then kmtEta
      else fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u) := rfl
  have key : ∀ u : ℝ, gProfile d k₂ u =
      (if k₂ = 0 then kmtEta u else kmtEta u - kmtEta ((2 : ℝ) ^ d * u)) := by
    intro u
    by_cases h : k₂ = 0
    · rw [hdef, if_pos h, if_pos h]
    · rw [hdef, if_neg h, if_neg h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : k₂ = 0
    · have hg : gProfile d k₂ = kmtEta := by rw [hdef, if_pos h]
      rw [hg]; exact contDiff_kmtEta_
    · have hg : gProfile d k₂ = fun u : ℝ => kmtEta u - kmtEta ((2:ℝ)^d * u) := by
        rw [hdef, if_neg h]
      rw [hg]
      exact contDiff_kmtEta_.sub (contDiff_kmtEta_.comp (contDiff_const.mul contDiff_id))
  · intro u hu
    rw [key u]
    by_cases h : k₂ = 0
    · rw [if_pos h]; exact kmtEta_zero hu
    · rw [if_neg h]; exact kmtEta_sub_rescale_eq_zero d u hu
  · rw [key 0]
    by_cases h : k₂ = 0
    · rw [if_pos h, if_pos h]
      exact kmtEta_one (by norm_num)
    · rw [if_neg h, if_neg h]
      exact kmtEta_sub_rescale_eq_zero_of_le d 0 (by rw [abs_zero]; positivity)
  · intro u hu
    rw [key u, key 0]
    by_cases h : k₂ = 0
    · rw [if_pos h, if_pos h]
      simp only [if_pos h] at hu
      rw [kmtEta_one hu, kmtEta_one (by norm_num : |(0:ℝ)| ≤ 1/2)]
    · rw [if_neg h, if_neg h]
      simp only [if_neg h] at hu
      rw [kmtEta_sub_rescale_eq_zero_of_le d u hu,
        kmtEta_sub_rescale_eq_zero_of_le d 0 (by rw [abs_zero]; positivity)]
  · intro u
    rw [key u]
    by_cases h : k₂ = 0
    · rw [if_pos h]; exact norm_kmtEta_le u
    · rw [if_neg h]; exact norm_kmtEta_sub_le u ((2:ℝ)^d * u)

end Work.KMTAreas.A7
