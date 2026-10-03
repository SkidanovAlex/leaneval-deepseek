import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

namespace Work.Horn

open Filter Topology Metric
open scoped Topology

noncomputable section

/-! ## Helper facts about `π(w) = exp(2πiw)` and the lift `ζ ↦ log ζ/(2πi)` -/

/-- `π(a + b) = π(a) · π(b)`. -/
theorem piExp_add_pdleg (a b : ℂ) :
    MandelDim.piExp (a + b) = MandelDim.piExp a * MandelDim.piExp b := by
  rw [MandelDim.piExp, MandelDim.piExp, MandelDim.piExp, ← Complex.exp_add]
  congr 1
  ring

/-- Imaginary part of the lift `log ζ/(2πi)`: it is `-log ‖ζ‖/(2π)`, which tends to `-∞` as
`‖ζ‖ → ∞` uniformly in `arg ζ`. -/
theorem im_log_div_two_pi_I_pdleg (ζ : ℂ) :
    (Complex.log ζ / (2 * Real.pi * Complex.I)).im = -(Real.log ‖ζ‖) / (2 * Real.pi) := by
  rw [Complex.div_im, Complex.log_re, Complex.log_im]
  have h1 : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
  have h2 : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq ((2 : ℂ) * ↑Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [show ((2 : ℂ) * ↑Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h1, h2, h3]
  field_simp
  ring

/-- A set is eventually true along the lower end (i.e. `Im w → -∞`) iff it contains a half
plane `{Im w ≤ b}`. -/
theorem eventually_lowerEnd_iff_pdleg {p : ℂ → Prop} :
    (∀ᶠ w in MandelDim.lowerEnd, p w) ↔ ∃ b : ℝ, ∀ w : ℂ, w.im ≤ b → p w := by
  rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [Filter.mem_atBot_sets] at ht
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, fun w hw => hts (hb w.im hw)⟩
  · rintro ⟨b, hb⟩
    refine ⟨{y : ℝ | y ≤ b}, ?_, ?_⟩
    · rw [Filter.mem_atBot_sets]; exact ⟨b, fun y hy => hy⟩
    · intro w hw
      exact hb w hw

/-- **Linear growth of the pushed-down horn map at the lower end.**

For `d : ParabData f₀ D₀` and a lower-end limit `cl` of the lifted horn map
(`E_lower`: `d.E w - w → cl` as `Im w → -∞`), the pushed-down horn map is asymptotically
linear at `∞` with slope `piExp cl ≠ 0`: for every `ε > 0` there is `R` such that for every
`ζ` with `‖ζ‖ ≥ R` the value `pushdown d.E ζ` is `ε`-close (relatively) to `piExp cl * ζ`.

Proof sketch: `pushdown d.E ζ = piExp (E w)` and `piExp w = ζ` for `w = log ζ / (2πi)`, whose
imaginary part `-log ‖ζ‖ / (2π)` tends to `-∞` (uniformly in `Re w = arg ζ / (2π)`, which stays
bounded), so `d.E w - w → cl` applies; then
`piExp (E w) = piExp w * piExp (E w - w)`.

This is the horn-specific input that rules out `exp z - 1`-style counterexamples for the
properness of the petal spreads. -/
theorem pushdown_lower_end_linear_growth {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    ∀ ε > 0, ∃ R : ℝ, ∀ ζ : ℂ, R ≤ ‖ζ‖ →
      ‖MandelDim.pushdown d.E ζ - MandelDim.piExp cl * ζ‖ ≤ ε * ‖ζ‖ := by
  intro ε hε
  -- Step 1: continuity of `π` at `cl` gives a tolerance `δ` for `d.E w - w - cl`.
  have hcont : ContinuousAt MandelDim.piExp cl := by
    unfold MandelDim.piExp
    fun_prop
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  -- Step 2: `d.E w - w → cl` along the lower end, in half-plane form.
  obtain ⟨b, hb⟩ := eventually_lowerEnd_iff_pdleg.mp
    (hcl.eventually (Metric.ball_mem_nhds cl hδpos))
  -- Step 3: the threshold `R`.
  refine ⟨Real.exp (-(2 * Real.pi * b)) + 1, fun ζ hζR => ?_⟩
  have hRpos : (0 : ℝ) < Real.exp (-(2 * Real.pi * b)) + 1 := by positivity
  have hζne : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζR
    linarith
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlogR : -(2 * Real.pi * b) ≤ Real.log (Real.exp (-(2 * Real.pi * b)) + 1) := by
    have h : Real.log (Real.exp (-(2 * Real.pi * b))) ≤
        Real.log (Real.exp (-(2 * Real.pi * b)) + 1) :=
      Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right zero_le_one)
    simpa using h
  have hlogζ : Real.log (Real.exp (-(2 * Real.pi * b)) + 1) ≤ Real.log ‖ζ‖ :=
    Real.log_le_log hRpos hζR
  -- Step 4: the lift `w = log ζ/(2πi)` has imaginary part below `b`.
  set w : ℂ := Complex.log ζ / (2 * Real.pi * Complex.I) with hwdef
  have hwim : w.im ≤ b := by
    rw [hwdef, im_log_div_two_pi_I_pdleg]
    have h1 : -(Real.log ‖ζ‖) / (2 * Real.pi) ≤
        -(Real.log (Real.exp (-(2 * Real.pi * b)) + 1)) / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ h2pi.le
      linarith
    have h2 : -(Real.log (Real.exp (-(2 * Real.pi * b)) + 1)) / (2 * Real.pi) ≤ b := by
      rw [div_le_iff₀ h2pi, mul_comm b (2 * Real.pi)]
      linarith
    linarith
  -- Step 5: apply the limit hypothesis at `w`.
  have hdist : dist (d.E w - w) cl < δ := hb w hwim
  have hpi : ‖MandelDim.piExp (d.E w - w) - MandelDim.piExp cl‖ < ε := by
    simpa [dist_eq_norm] using hδ hdist
  -- Step 6: `pushdown d.E ζ = ζ * piExp (d.E w - w)` and the conclusion.
  have hpush : MandelDim.pushdown d.E ζ = MandelDim.piExp (d.E w) := by
    rw [MandelDim.pushdown_of_ne d.E hζne, hwdef]
  have hzeta : ζ = MandelDim.piExp w := (MandelDim.piExp_log_div ζ hζne).symm
  have hsplit : MandelDim.piExp (d.E w) =
      MandelDim.piExp (d.E w - w) * MandelDim.piExp w := by
    rw [← piExp_add_pdleg, sub_add_cancel]
  calc ‖MandelDim.pushdown d.E ζ - MandelDim.piExp cl * ζ‖
      = ‖(MandelDim.piExp (d.E w - w) - MandelDim.piExp cl) * MandelDim.piExp w‖ := by
        rw [hpush, hzeta, hsplit]
        congr 1
        ring
    _ = ‖MandelDim.piExp (d.E w - w) - MandelDim.piExp cl‖ * ‖MandelDim.piExp w‖ := by
        rw [norm_mul]
    _ = ‖MandelDim.piExp (d.E w - w) - MandelDim.piExp cl‖ * ‖ζ‖ := by
        rw [← hzeta]
    _ ≤ ε * ‖ζ‖ := mul_le_mul_of_nonneg_right hpi.le (norm_nonneg ζ)

end

end Work.Horn
