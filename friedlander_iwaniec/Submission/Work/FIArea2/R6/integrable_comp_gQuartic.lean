import Mathlib
import Submission.Work.FIArea2.Sec6Defs

set_option autoImplicit false

namespace Work.FIArea2.R6

open MeasureTheory

/-- **Lower bound for the quartic form (7.1).**  Writing `a = t₁²`, `b = t₂²` (both `≥ 0`),
`g(t) = a² − 2γab + b²` and
`g(t) − ((1−|γ|)/2)(a+b)² = ((1+|γ|)/2)(a−b)² + 2ab(|γ|−γ) ≥ 0`. -/
private lemma gQuartic_ge (γ : ℝ) (t : ℝ × ℝ) :
    (1 - |γ|) / 2 * (t.1 ^ 2 + t.2 ^ 2) ^ 2 ≤ Work.FIArea2.gQuartic γ t := by
  have hkey : Work.FIArea2.gQuartic γ t - (1 - |γ|) / 2 * (t.1 ^ 2 + t.2 ^ 2) ^ 2
      = (1 + |γ|) / 2 * (t.1 ^ 2 - t.2 ^ 2) ^ 2
        + 2 * (t.1 ^ 2 * t.2 ^ 2) * (|γ| - γ) := by
    unfold Work.FIArea2.gQuartic
    ring
  have hterm1 : 0 ≤ (1 + |γ|) / 2 * (t.1 ^ 2 - t.2 ^ 2) ^ 2 := by
    apply mul_nonneg
    · linarith [abs_nonneg γ]
    · exact sq_nonneg _
  have hterm2 : 0 ≤ 2 * (t.1 ^ 2 * t.2 ^ 2) * (|γ| - γ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact sub_nonneg.mpr (le_abs_self γ)
  linarith [hkey, hterm1, hterm2]

/-- **Coercivity of the quartic form** when `|γ| < 1`: if `g(t) ≤ R₀` then `t` lies in the ball of
radius `(R₀/c)^{1/4}`, `c = (1−|γ|)/2 > 0`.  Indeed `c·(t₁²+t₂²)² ≤ g(t) ≤ R₀`, so
`t₁²+t₂² ≤ √(R₀/c)`, and `‖t‖ ≤ √(t₁²+t₂²)` for the product (sup) norm on `ℝ × ℝ`. -/
private lemma gQuartic_coercive (γ : ℝ) (hγ : |γ| < 1) (R₀ : ℝ) (_hR₀ : 0 ≤ R₀) :
    ∀ t : ℝ × ℝ, Work.FIArea2.gQuartic γ t ≤ R₀ →
      ‖t‖ ≤ Real.sqrt (Real.sqrt (R₀ / ((1 - |γ|) / 2))) := by
  intro t ht
  set c : ℝ := (1 - |γ|) / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hSnn : 0 ≤ t.1 ^ 2 + t.2 ^ 2 := by positivity
  have hbound : c * (t.1 ^ 2 + t.2 ^ 2) ^ 2 ≤ R₀ := by
    have h1 : (1 - |γ|) / 2 * (t.1 ^ 2 + t.2 ^ 2) ^ 2 ≤ R₀ := le_trans (gQuartic_ge γ t) ht
    rwa [← hcdef] at h1
  have hX : (t.1 ^ 2 + t.2 ^ 2) ^ 2 ≤ R₀ / c := by
    rw [le_div_iff₀ hcpos]
    linarith [hbound]
  have hS_le : t.1 ^ 2 + t.2 ^ 2 ≤ Real.sqrt (R₀ / c) := by
    have h := Real.sqrt_le_sqrt hX
    rwa [Real.sqrt_sq hSnn] at h
  have hsqrtnn : 0 ≤ Real.sqrt (t.1 ^ 2 + t.2 ^ 2) := Real.sqrt_nonneg _
  have h1 : |t.1| ≤ Real.sqrt (t.1 ^ 2 + t.2 ^ 2) := by
    have hsq : |t.1| ^ 2 ≤ (Real.sqrt (t.1 ^ 2 + t.2 ^ 2)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt hSnn]
      nlinarith [sq_nonneg t.2]
    have h := sq_le_sq.mp hsq
    simpa [abs_of_nonneg hsqrtnn] using h
  have h2 : |t.2| ≤ Real.sqrt (t.1 ^ 2 + t.2 ^ 2) := by
    have hsq : |t.2| ^ 2 ≤ (Real.sqrt (t.1 ^ 2 + t.2 ^ 2)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt hSnn]
      nlinarith [sq_nonneg t.1]
    have h := sq_le_sq.mp hsq
    simpa [abs_of_nonneg hsqrtnn] using h
  have hnorm : ‖t‖ ≤ Real.sqrt (t.1 ^ 2 + t.2 ^ 2) := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le h1 h2
  calc ‖t‖ ≤ Real.sqrt (t.1 ^ 2 + t.2 ^ 2) := hnorm
    _ ≤ Real.sqrt (Real.sqrt (R₀ / c)) := Real.sqrt_le_sqrt hS_le

/-- **Integrability of `F ∘ gQuartic γ`.**  Let `F : ℝ → ℝ` be continuous with compact support and
`|γ| < 1`.  Then `t ↦ F (g(t))`, `g(t) = t₁⁴ − 2γt₁²t₂² + t₂⁴`, is continuous and of compact
support: `F` vanishes off some ball `|x| ≤ R₀`, and `g` is coercive, so `F(g(t)) = 0` once
`‖t‖ > (R₀/c)^{1/4}`.  Hence it is integrable (`Continuous.integrable_of_hasCompactSupport`). -/
theorem integrable_comp_gQuartic (F : ℝ → ℝ) (hF : Continuous F) (hcs : HasCompactSupport F) (γ : ℝ) (hγ : |γ| < 1) : MeasureTheory.Integrable (fun t : ℝ × ℝ => F (Work.FIArea2.gQuartic γ t)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hF.comp (by unfold Work.FIArea2.gQuartic; fun_prop)
  · rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
    have hev : F =ᶠ[Filter.coclosedCompact ℝ] 0 := hasCompactSupport_iff_eventuallyEq.mp hcs
    rw [Filter.coclosedCompact_eq_cocompact] at hev
    have hm : {x : ℝ | F x = 0} ∈ Filter.cocompact ℝ := hev
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℝ)] at hm
    obtain ⟨r, hr⟩ := hm
    set R₀ : ℝ := max r 0 with hR₀def
    have hR₀0 : 0 ≤ R₀ := le_max_right _ _
    have hFzero : ∀ x : ℝ, R₀ < |x| → F x = 0 := by
      intro x hx
      apply hr
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      linarith [le_max_left r 0]
    have hm2 : {t : ℝ × ℝ | F (Work.FIArea2.gQuartic γ t) = 0} ∈ Filter.cocompact (ℝ × ℝ) := by
      rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℝ × ℝ)]
      refine ⟨Real.sqrt (Real.sqrt (R₀ / ((1 - |γ|) / 2))), ?_⟩
      intro t ht
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at ht
      have ht' : Real.sqrt (Real.sqrt (R₀ / ((1 - |γ|) / 2))) < ‖t‖ := not_le.mp ht
      have hgt : R₀ < Work.FIArea2.gQuartic γ t := by
        by_contra hcon
        have hle : Work.FIArea2.gQuartic γ t ≤ R₀ := not_lt.mp hcon
        have := gQuartic_coercive γ hγ R₀ hR₀0 t hle
        linarith
      have hpos : 0 < Work.FIArea2.gQuartic γ t := lt_of_le_of_lt hR₀0 hgt
      show F (Work.FIArea2.gQuartic γ t) = 0
      exact hFzero _ (by rw [abs_of_pos hpos]; exact hgt)
    exact hm2

end Work.FIArea2.R6
