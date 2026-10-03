import Mathlib
import Submission.Work.FIArea6Road.TauHeartDefs

namespace Work.FIArea6Road

/-- For `Pa : Params` we have `3 ≤ Pa.x`, hence `1 < log x` (since `log 3 > 1`, as `e < 3`). -/
private lemma one_lt_log_x (Pa : Work.FITop.Params) : 1 < Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h1 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
  have h3 : 1 < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  linarith

/-- `θ = (log x)^{-A'} < 1`: `log x > 1` and `-A' < 0`. -/
private lemma theta_lt_one (Pa : Work.FITop.Params) : Pa.θ < 1 := by
  have hlog : 1 < Real.log (Pa.x : ℝ) := one_lt_log_x Pa
  have hA' : 0 < Pa.A' := by nlinarith [Pa.hA, Pa.hA']
  rw [Pa.hθ]
  exact Real.rpow_lt_one_of_one_lt_of_neg hlog (by linarith)

/-- `η ≤ 1/4`, from `x^{1/4+η} < N < x^{1/2}(log x)^{-B} ≤ x^{1/2}`. -/
private lemma eta_le_quarter (Pa : Work.FITop.Params) : Pa.η ≤ 1 / 4 := by
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := le_of_lt (one_lt_log_x Pa)
  have hx1 : 1 < (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hpowle : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith [Pa.hB])
  have hxhalf : (0 : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    apply Real.rpow_nonneg
    linarith
  have hupper : Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    refine lt_of_lt_of_le Pa.hNhi ?_
    calc (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left hpowle hxhalf
      _ = (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := mul_one _
  have hlt : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) :=
    lt_trans Pa.hNlo hupper
  have h := (Real.rpow_lt_rpow_left_iff hx1).mp hlt
  linarith

/-- `2π√2 < 16` (`π < 4`, `√2 < 2`). -/
private lemma two_pi_sqrt_two_lt_sixteen : 2 * Real.pi * Real.sqrt 2 < 16 := by
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 : Real.pi * Real.sqrt 2 < 4 * Real.sqrt 2 := mul_lt_mul_of_pos_right Real.pi_lt_four hp
  have h3 : (4 : ℝ) * Real.sqrt 2 < 4 * 2 := mul_lt_mul_of_pos_left h2 (by norm_num)
  linarith

/-- `16 ≤ (log x)^{A' - A}` whenever `log x ≥ 2` and `A' - A ≥ 2^20`. -/
private lemma sixteen_le_rpow {L A A' : ℝ} (hL : 2 ≤ L) (hAA : (2 : ℝ) ^ (20 : ℕ) ≤ A' - A) :
    (16 : ℝ) ≤ L ^ (A' - A) := by
  -- `16 = 2^4 ≤ 2^{2^20} ≤ (log x)^{2^20} ≤ (log x)^{A' - A}`
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have h16a : (16 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (20 : ℕ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (4 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ))
    have h24 : (16 : ℝ) ≤ (2 : ℝ) ^ (4 : ℝ) := by norm_num
    linarith
  have h16b : (2 : ℝ) ^ ((2 : ℝ) ^ (20 : ℕ)) ≤ L ^ ((2 : ℝ) ^ (20 : ℕ)) :=
    Real.rpow_le_rpow (by norm_num) hL (by positivity)
  have hmono : L ^ ((2 : ℝ) ^ (20 : ℕ)) ≤ L ^ (A' - A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hAA
  linarith [h16a, h16b, hmono]

/-- The saving separation: for all `x ≥ e²`, `2π√2·θ ≤ ϑ`. -/
private lemma two_pi_sqrt_two_mul_theta_le_vartheta
    (Pa : Work.FITop.Params) (hx : Real.exp 2 ≤ (Pa.x : ℝ)) :
    2 * Real.pi * Real.sqrt 2 * Pa.θ ≤ Pa.ϑ := by
  have hxpos : 0 < (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hL : (2 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log (Pa.x : ℝ) := by linarith
  have hAA : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' - Pa.A := by
    nlinarith [Pa.hA, Pa.hA']
  have hbig : (16 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A' - Pa.A) :=
    sixteen_le_rpow hL hAA
  have hb : 2 * Real.pi * Real.sqrt 2 < (Real.log (Pa.x : ℝ)) ^ (Pa.A' - Pa.A) :=
    lt_of_lt_of_le two_pi_sqrt_two_lt_sixteen hbig
  have hθpos : 0 < (Real.log (Pa.x : ℝ)) ^ (-Pa.A') := Real.rpow_pos_of_pos hLpos _
  calc 2 * Real.pi * Real.sqrt 2 * Pa.θ
      = 2 * Real.pi * Real.sqrt 2 * (Real.log (Pa.x : ℝ)) ^ (-Pa.A') := by rw [Pa.hθ]
    _ ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A' - Pa.A)
          * (Real.log (Pa.x : ℝ)) ^ (-Pa.A') := le_of_lt (mul_lt_mul_of_pos_right hb hθpos)
    _ = (Real.log (Pa.x : ℝ)) ^ (-Pa.A) := by
        rw [← Real.rpow_add hLpos]
        congr 1
        ring
    _ = Pa.ϑ := by rw [Pa.hϑ]

/-- **Three elementary arithmetic facts about the parameter set `Params` (4.4)–(4.19).**

* `θ < 1`: `θ = (log x)^{−A'}` with `A' ≥ 2A + 2^20 > 0` and `log x ≥ log 3 > 1`.
* `η ≤ 1/4`: from `x^{1/4+η} < N < x^{1/2}·(log x)^{−B}` (`hNlo`, `hNhi`).
* The **saving separation** `2π√2·θ ≤ ϑ` for all large enough `x`: since
  `A' − A ≥ A + 2^20 ≥ 2^20` and `θ/ϑ = (log x)^{−(A'−A)}`, this is
  `2π√2 ≤ (log x)^{A'−A}`; taking `x0 = Real.exp 2` gives `(log x)^{A'−A} ≥ 2^{2^20} ≥ 16 ≥ 2π√2`
  (monotonicity of `Real.rpow` in base and exponent; `Real.pi_lt_four`, `Real.sqrt_two_lt_two`).
  This is the separation `θ ≪ ϑ` which kills the axis-free points of the *cut* sector. -/
theorem TauHeartArith :
    (∀ Pa : Work.FITop.Params, Pa.θ < 1) ∧
    (∀ Pa : Work.FITop.Params, Pa.η ≤ 1 / 4) ∧
    (∃ x0 : ℝ, 0 < x0 ∧ ∀ Pa : Work.FITop.Params, x0 ≤ (Pa.x : ℝ) →
      2 * Real.pi * Real.sqrt 2 * Pa.θ ≤ Pa.ϑ) :=
  ⟨theta_lt_one, eta_le_quarter,
    Real.exp 2, Real.exp_pos 2, two_pi_sqrt_two_mul_theta_le_vartheta⟩

end Work.FIArea6Road
