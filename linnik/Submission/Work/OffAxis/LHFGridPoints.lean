import Mathlib
import Submission.Work.OffAxis.G72Sub2Aux

set_option maxHeartbeats 2000000
namespace Work.OffAxis

open Work.ZeroFreeTables.OffAxis

/-- `LHF 0 σ = 0` for every `σ`: the integrand `(e^{0·y} - 1)·cos(σy)·g72 y` vanishes identically. -/
private lemma LHF_zero_eq (σ : ℝ) : LHF 0 σ = 0 := by
  rw [LHF_eq_integral]
  simp

/--
`LHF s σ ≤ 9/50` on the finite grid `s ∈ {0, 1/2, 1}`, `σ ∈ {3/2, 2, 5/2, 3, 7/2}`.

Each grid point is evaluated through the closed form `LHF_eq_closed`
`LHF s σ = (RA72 s σ - RA72 0 σ) + e^{2s}(cos(2σ) RB72 s σ + sin(2σ) RI72 s σ)
  - (cos(2σ) RB72 0 σ + sin(2σ) RI72 0 σ)`,
whose rational parts are rational numbers at the grid points, and then bounded using the
rational enclosures of `e, e²` (`exp_bounds_e`) and of `cos θ, sin θ` at `θ = 3,…,7`
(`trig_bounds`); `nlinarith` closes each of the resulting bilinear interval estimates.
-/
theorem LHFGridPoints : ∀ s σ : ℝ, (s = 0 ∨ s = 1/2 ∨ s = 1) → (σ = 3/2 ∨ σ = 2 ∨ σ = 5/2 ∨ σ = 3 ∨ σ = 7/2) → Work.OffAxis.LHF s σ ≤ 9/50 := by
  intro s σ hs hσ
  rcases hs with rfl | rfl | rfl
  · rcases hσ with rfl | rfl | rfl | rfl | rfl <;> (rw [LHF_zero_eq]; norm_num)
  · rcases hσ with rfl | rfl | rfl | rfl | rfl
    · have hcl := LHF_eq_closed (s := (1/2 : ℝ)) (σ := (3/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1/2 : ℝ)) (σ := (2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1/2 : ℝ)) (σ := (5/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1/2 : ℝ)) (σ := (3 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1/2 : ℝ)) (σ := (7/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
  · rcases hσ with rfl | rfl | rfl | rfl | rfl
    · have hcl := LHF_eq_closed (s := (1 : ℝ)) (σ := (3/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1 : ℝ)) (σ := (2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1 : ℝ)) (σ := (5/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1 : ℝ)) (σ := (3 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]
    · have hcl := LHF_eq_closed (s := (1 : ℝ)) (σ := (7/2 : ℝ)) (by norm_num) (by norm_num)
      rw [hcl]
      norm_num [RA72, RB72, RI72]
      nlinarith [exp_bounds_e, trig_bounds]

end Work.OffAxis
