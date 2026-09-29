import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.amoM_strip

/-!
# The strip section of the complexified almost Mathieu cocycle

Avila--Jitomirskaya, *The Ten Martini Problem*, Ann. of Math. 170 (2009).  For energy
`z = E` with `Im E ≥ 4`, the section equation

`M x = z - 2λ cos (2π (x - α)) - 1 / M (x - α)`

has an analytic solution on a horizontal strip `{|Im x| < σ}` whose values are bounded
between `Im z / 2` and `‖z‖ + 2λ cosh (2πσ) + 2 / Im z`, for a suitable `σ > 0` that
depends only on `λ` and `Im z`.

The existence of the solution for a *fixed* admissible `σ` is proved by the Banach
fixed-point/geometric-iteration argument in `amoM_strip` (the iterate
`x ↦ z - 2λ cos (2π (x - α)) - 1 / (·)(x - α)` is a contraction of factor `4 / (Im z)^2 ≤ 1/4`
on the set of `ℍ`-valued bounded functions on the strip).  Here we only supply the
strip half-width: `2λ sinh (2πσ) ≤ Im z / 2 - 2 / Im z` is satisfiable for small `σ > 0`
because `Im z ≥ 4` makes the right-hand side positive.
-/

open Filter Topology

namespace Work.TMComp.MAnalytic

noncomputable section

/-- For `λ > 0` and `Y ≥ 4` there is `σ > 0` with `2λ sinh (2πσ) ≤ Y/2 - 2/Y`.
The right-hand side equals `(Y² - 4)/(2Y)`, which is positive, while
`σ ↦ 2λ sinh (2πσ)` is continuous with value `0` at `σ = 0`. -/
theorem strip_sigma_exists {lam Y : ℝ} (hlam : 0 < lam) (hY : 4 ≤ Y) :
    ∃ σ : ℝ, 0 < σ ∧ 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ Y / 2 - 2 / Y := by
  have hYpos : 0 < Y := by linarith
  have hc : 0 < Y / 2 - 2 / Y := by
    have hYne : Y ≠ 0 := ne_of_gt hYpos
    have h : Y / 2 - 2 / Y = (Y ^ 2 - 4) / (2 * Y) := by
      field_simp
      ring
    rw [h]
    exact div_pos (by nlinarith) (by positivity)
  have hcont : ContinuousAt (fun σ : ℝ => 2 * lam * Real.sinh (2 * Real.pi * σ)) 0 := by
    fun_prop
  have hf0 : (fun σ : ℝ => 2 * lam * Real.sinh (2 * Real.pi * σ)) 0 = 0 := by simp
  have hmem : Set.Iio (Y / 2 - 2 / Y)
      ∈ 𝓝 ((fun σ : ℝ => 2 * lam * Real.sinh (2 * Real.pi * σ)) 0) := by
    rw [hf0]
    exact isOpen_Iio.mem_nhds hc
  have hev : ∀ᶠ σ in 𝓝 (0 : ℝ), 2 * lam * Real.sinh (2 * Real.pi * σ) < Y / 2 - 2 / Y :=
    hcont.eventually_mem hmem
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, le_of_lt (hε ?_)⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

theorem strip_section {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) :
    ∃ σ : ℝ, 0 < σ ∧ 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im ∧
      ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M {x : ℂ | |x.im| < σ} ∧
        (∀ x : ℂ, |x.im| < σ →
          z.im / 2 ≤ ‖M x‖ ∧
          ‖M x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im) ∧
        (∀ x : ℂ, |x.im| < σ →
          M x = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / M (x - α)) := by
  obtain ⟨σ, hσpos, hσz⟩ := strip_sigma_exists hlam hz
  obtain ⟨M, hM_an, hM_bd, hM_eq, _⟩ := amoM_strip hlam hz hσpos hσz
  exact ⟨σ, hσpos, hσz, M, hM_an, hM_bd, hM_eq⟩

end

end Work.TMComp.MAnalytic
