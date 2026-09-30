import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.liouville_logForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Lower bound for `log ‖Θ‖` from the modified height.**

If `Θ` is a logarithm of `φ α'` (`α' ≠ 0`, `Θ ≠ 0`) whose modified height `hmod α' Θ` is at
most `σ`, then `log ‖Θ‖ ≥ -(d σ + d log 2)`, where `d = [K : ℚ]`.

This is the one-term case of the Liouville estimate `liouville_logForm`: the modified-height
bound gives the height bound `h(α') ≤ d σ`, and the Liouville estimate for the single form
`Θ = 1 · Θ` gives `log ‖Θ‖ ≥ -h(α') - d log 2`. -/
theorem log_norm_lamP_ge {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α' : K) (Θ : ℂ) (σ : ℝ)
    (hΘ : Complex.exp Θ = φ α') (hα' : α' ≠ 0) (hΘne : Θ ≠ 0)
    (hmodle : hmod α' Θ ≤ σ) :
    Real.log ‖Θ‖ ≥ -((Module.finrank ℚ K : ℝ) * σ + (Module.finrank ℚ K : ℝ) * Real.log 2) := by
  have hdpos : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hle : Height.logHeight₁ α' / (Module.finrank ℚ K : ℝ) ≤ σ := by
    rw [hmod] at hmodle
    exact le_trans (le_max_left _ _) hmodle
  have hmul : Height.logHeight₁ α' ≤ (Module.finrank ℚ K : ℝ) * σ := by
    have h := (div_le_iff₀ hdpos).mp hle
    linarith
  have hliou := liouville_logForm φ (fun _ : Fin 1 => α') (fun _ => hα')
      (fun _ => Θ) (fun _ => hΘ) (fun _ => 1) (by simpa using hΘne)
  have hliou' : Real.log ‖Θ‖ ≥
      -Height.logHeight₁ α' - (Module.finrank ℚ K : ℝ) * Real.log 2 := by
    simpa using hliou
  linarith

end Work.BW
