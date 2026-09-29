import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.pd_upper
import Submission.Work.TMC16Core.Basic.singular_of_ne_zero

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- For `λ > 1` the Lyapunov exponent of the spectrum is `log λ` (via `P_BJ`). -/
theorem lyap_eq_log (h7 : Work.TMC16Core.P_BJ) {α b₀ lam : ℝ} (hα : Irrational α)
    (hb₀ : 0 ≤ b₀) (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ}
    (hE : E ∈ amoSpec α lam) : lyap α lam (E : ℂ) = Real.log lam := by
  have h1 : (1 : ℝ) ≤ Real.exp (16 * b₀ / 9) := Real.one_le_exp (by positivity)
  have hlam1 : 1 < lam := lt_of_le_of_lt h1 hlam
  have hlogpos : 0 < Real.log lam := Real.log_pos hlam1
  have hbj := h7 α lam hα (ne_of_gt (lt_trans zero_lt_one hlam1)) E hE
  rw [hbj, abs_of_pos (lt_trans zero_lt_one hlam1), max_eq_right hlogpos.le]

theorem one_lt_lam {b₀ lam : ℝ} (hb₀ : 0 ≤ b₀) (hlam : Real.exp (16 * b₀ / 9) < lam) :
    1 < lam :=
  lt_of_le_of_lt (Real.one_le_exp (by positivity)) hlam

/-- The eventual local-uniform upper bound for the continuants, at rate `log λ + ε`. -/
theorem pd_eventually_bound (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ amoSpec α lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (n + 1)‖ ≤ Real.exp ((n : ℝ) * (Real.log lam + ε)) := by
  have hL := lyap_eq_log h7 hα hb₀ hlam hE
  obtain ⟨n₀, hn₀⟩ := Work.TMC16Core.Basic.pd_upper h4 hα (E : ℂ) ε hε
  refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn ζ => ?_⟩
  refine le_trans (hn₀ n hn ζ) (Real.exp_le_exp.mpr ?_)
  rw [hL]

/-- `0` is eventually `(m,k)`-singular for every fixed `m > 0`. -/
theorem sing_zero {α lam θ : ℝ} {E : ℝ} {u : ℤ → ℂ}
    (hu : IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) {m : ℝ} (hm : 0 < m) :
    ∀ᶠ k : ℕ in Filter.atTop, IsSingular α lam θ (E : ℂ) m k 0 := by
  obtain ⟨C, hC⟩ := hu.2.2
  exact Work.TMC16Core.Basic.singular_of_ne_zero hu.2.1 hC hu0 hm

/-! ## The Diophantine-only forms (C16 consumes only the Diophantine case of C7)

`P_BJ_dioph` is the restriction of C7 to Diophantine frequencies; it is proved in the
workspace (`Work.TMComp.RedC7T.D_BJ_dioph_uncond`).  The versions below are the ones the C16
chain uses; they require `0 < b₀` (`DiophBelow α 0` is unsatisfiable, see
`diophBelow_zero_false`). -/

/-- `DiophBelow α 0` is unsatisfiable: `fracDist ≤ 1/2` while the bound reads `1 ≤ fracDist`. -/
theorem diophBelow_zero_false {α : ℝ} (h : DiophBelow α 0) : False := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have h1 := hN (max N 1) (le_max_left _ _)
  simp only [zero_mul, neg_zero, Real.exp_zero] at h1
  have h2 : fracDist (((max N 1 : ℕ) : ℝ) * α) ≤ 1 / 2 := by
    rw [fracDist]; exact abs_sub_round _
  linarith

/-- `P_BJ` implies the Diophantine-only form. -/
theorem p_bj_dioph_of_p_bj (h : Work.TMC16Core.P_BJ) : Work.TMC16Core.P_BJ_dioph := by
  intro α lam b₀ hα _hb₀ _hD hlam E hE
  exact h α lam hα hlam E hE

/-- For `λ > 1` the Lyapunov exponent of the spectrum is `log λ`, from the Diophantine case
of C7 only. -/
theorem lyap_eq_log_dioph (h7 : Work.TMC16Core.P_BJ_dioph) {α b₀ lam : ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hD : DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ}
    (hE : E ∈ amoSpec α lam) : lyap α lam (E : ℂ) = Real.log lam := by
  have h1 : (1 : ℝ) ≤ Real.exp (16 * b₀ / 9) := Real.one_le_exp (by positivity)
  have hlam1 : 1 < lam := lt_of_le_of_lt h1 hlam
  have hlogpos : 0 < Real.log lam := Real.log_pos hlam1
  have hbj := h7 α lam b₀ hα hb₀ hD (ne_of_gt (lt_trans zero_lt_one hlam1)) E hE
  rw [hbj, abs_of_pos (lt_trans zero_lt_one hlam1), max_eq_right hlogpos.le]

/-- The eventual local-uniform upper bound for the continuants, at rate `log λ + ε`, from the
Diophantine case of C7 only. -/
theorem pd_eventually_bound_dioph (h4 : Work.TMC16Core.P_LEBasics)
    (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 < b₀) (hD : DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ amoSpec α lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (n + 1)‖ ≤ Real.exp ((n : ℝ) * (Real.log lam + ε)) := by
  have hL := lyap_eq_log_dioph h7 hα hb₀ hD hlam hE
  obtain ⟨n₀, hn₀⟩ := Work.TMC16Core.Basic.pd_upper h4 hα (E : ℂ) ε hε
  refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn ζ => ?_⟩
  refine le_trans (hn₀ n hn ζ) (Real.exp_le_exp.mpr ?_)
  rw [hL]


end Work.TMC16Core.Core
