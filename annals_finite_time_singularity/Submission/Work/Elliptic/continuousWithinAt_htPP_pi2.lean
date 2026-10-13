import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.HardyTwoDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false

/-- Pointwise bound: if `htU f` and its derivative are bounded on `(0,π/2)` by `Cu`, `Cu'`
(the latter two being nonnegative), then at any point `θ` where the two bounds hold,
`|htPP f θ| ≤ (40 Cu'^2 + 80 Cu Cu') |sin 2θ|`.  Since `sin 2θ → 0` as `θ → π/2`,
this is the squeeze estimate used below. -/
lemma abs_htPP_le_pi2 (f : ℝ → ℝ) (Cu Cu' : ℝ) (hCu : 0 ≤ Cu) (hCu' : 0 ≤ Cu') (θ : ℝ)
    (hu : |htU f θ| ≤ Cu) (hu' : |deriv (htU f) θ| ≤ Cu') :
    |htPP f θ| ≤ (40 * Cu'^2 + 80 * Cu * Cu') * |Real.sin (2 * θ)| := by
  have hs : |Real.sin (2*θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
  have hp2 : (deriv (htU f) θ)^2 ≤ Cu'^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hCu'])
  have hunfold : htPP f θ = Real.sin (2*θ) * (40 * Real.cos (2*θ) * (deriv (htU f) θ)^2 - 80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ) := by
    simp only [htPP]; ring
  rw [hunfold, abs_mul]
  have h1 : |40 * Real.cos (2*θ) * (deriv (htU f) θ)^2| ≤ 40 * Cu'^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 40), abs_sq]
    have : |Real.cos (2*θ)| * (deriv (htU f) θ)^2 ≤ 1 * Cu'^2 :=
      mul_le_mul hc hp2 (sq_nonneg _) (by norm_num)
    nlinarith [this]
  have h2 : |80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ| ≤ 80 * Cu * Cu' := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 80)]
    have hsq : |Real.sin (2*θ)| * |htU f θ| ≤ 1 * Cu :=
      mul_le_mul hs hu (abs_nonneg _) (by norm_num)
    have : |Real.sin (2*θ)| * |htU f θ| * |deriv (htU f) θ| ≤ 1 * Cu * Cu' :=
      mul_le_mul hsq hu' (abs_nonneg _) (by positivity)
    nlinarith [this]
  have habs : |40 * Real.cos (2*θ) * (deriv (htU f) θ)^2 - 80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ| ≤
      |40 * Real.cos (2*θ) * (deriv (htU f) θ)^2| + |80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ| := by
    have h := abs_sub_le (40 * Real.cos (2*θ) * (deriv (htU f) θ)^2) 0 (80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ)
    simpa using h
  have hinner : |40 * Real.cos (2*θ) * (deriv (htU f) θ)^2 - 80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ| ≤ 40 * Cu'^2 + 80 * Cu * Cu' :=
    habs.trans (add_le_add h1 h2)
  calc |Real.sin (2*θ)| * |40 * Real.cos (2*θ) * (deriv (htU f) θ)^2 - 80 * Real.sin (2*θ) * htU f θ * deriv (htU f) θ|
      ≤ |Real.sin (2*θ)| * (40 * Cu'^2 + 80 * Cu * Cu') := mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = (40 * Cu'^2 + 80 * Cu * Cu') * |Real.sin (2*θ)| := by ring

theorem continuousWithinAt_htPP_pi2 (f : ℝ → ℝ) (Cu Cu' : ℝ)
    (hu : ∀ x ∈ Set.Ioo 0 (π / 2), |Work.Elliptic.htU f x| ≤ Cu)
    (hu' : ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (Work.Elliptic.htU f) x| ≤ Cu') :
    ContinuousWithinAt (Work.Elliptic.htPP f) (Set.Icc 0 (π / 2)) (π / 2) := by
  have hCu : 0 ≤ Cu := by
    have hx : (π/4) ∈ Set.Ioo 0 (π/2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact (abs_nonneg _).trans (hu (π/4) hx)
  have hCu' : 0 ≤ Cu' := by
    have hx : (π/4) ∈ Set.Ioo 0 (π/2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact (abs_nonneg _).trans (hu' (π/4) hx)
  set K := 40 * Cu'^2 + 80 * Cu * Cu' with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; nlinarith [sq_nonneg Cu', mul_nonneg hCu hCu']
  rw [ContinuousWithinAt, htPP_pi2]
  have hbound : ∀ᶠ θ in 𝓝[Set.Icc 0 (π / 2)] (π / 2), |htPP f θ| ≤ K * |Real.sin (2 * θ)| := by
    have hne : Set.Ioi (π/4) ∈ 𝓝[Set.Icc 0 (π / 2)] (π / 2) :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos]))
    filter_upwards [hne, self_mem_nhdsWithin] with θ hθ hθmem
    have hθ' : π/4 < θ := hθ
    rcases lt_or_eq_of_le hθmem.2 with hlt | heq
    · have hmem : θ ∈ Set.Ioo 0 (π/2) := ⟨by linarith [Real.pi_pos, hθ'], hlt⟩
      rw [hKdef]
      exact abs_htPP_le_pi2 f Cu Cu' hCu hCu' θ (hu θ hmem) (hu' θ hmem)
    · rw [heq, htPP_pi2 f]
      have : Real.sin (2 * (π / 2)) = 0 := by rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
      rw [this]; simp
  have hsincont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have h1 : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
    have ht := hsincont.tendsto (π / 2)
    have hval : Real.sin (2 * (π / 2)) = 0 := by rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rw [hval] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun θ : ℝ => K * |Real.sin (2 * θ)|) (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
    have h2 : Tendsto (fun θ : ℝ => |Real.sin (2 * θ)|) (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
      have := h1.norm
      simpa [Real.norm_eq_abs] using this
    have := h2.const_mul K
    simpa using this
  have hff : Tendsto (fun θ : ℝ => |htPP f θ|) (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun θ => abs_nonneg _)) hbound hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hff)

end Work.Elliptic
