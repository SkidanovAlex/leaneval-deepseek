import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.RhoPerDefs
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.slabGlobalExtendPeriodic
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.derivRhoHNeg
import Submission.Work.RPB.B5.extend_rho_per
import Submission.Work.RPB.B5.rhoPer_deriv_pos

open scoped ContDiff

set_option autoImplicit false

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary estimates for the three branches -/

lemma sqrt2_pos' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt2_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

lemma one_le_sqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rwa [Real.sqrt_one] at h

lemma sqrt17_lt_seven : Real.sqrt 17 < 7 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]

lemma sqrt17_ge_four : (4 : ℝ) ≤ Real.sqrt 17 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]

lemma nine_eighth_lt_sqrt2 : (9 : ℝ) / 8 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- `sig` rewritten in the variable `u = x + √2`. -/
lemma sig_eq' (x : ℝ) :
    sig x = (x + Real.sqrt 2) ^ 2 / 2 - Real.sqrt 2 * (x + Real.sqrt 2) := by
  rw [sig]
  ring_nf
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

lemma sig_contDiff : ContDiff ℝ 8 sig := by unfold sig; fun_prop

/-- For `x ∈ [-√2, 0]`, `|sig x| = √2 u - u²/2 ≤ √2 u` with `u = x + √2`. -/
lemma sig_abs_le_rp {x : ℝ} (h1 : -Real.sqrt 2 ≤ x) (h2 : x + Real.sqrt 2 ≤ 2 * Real.sqrt 2) :
    |sig x| ≤ Real.sqrt 2 * (x + Real.sqrt 2) := by
  have hp := sqrt2_pos'
  have hu0 : 0 ≤ x + Real.sqrt 2 := by linarith
  rw [sig_eq' x]
  have hle : (x + Real.sqrt 2) ^ 2 / 2 - Real.sqrt 2 * (x + Real.sqrt 2) ≤ 0 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr h2)]
  rw [abs_of_nonpos hle]
  nlinarith [sq_nonneg (x + Real.sqrt 2)]

lemma rhoMid_pos' (x : ℝ) (h : -1 < x + Real.sqrt 2) : 0 < rhoMid x := by
  rw [rhoMid]
  have h' : 0 < 1 + x + Real.sqrt 2 := by linarith
  exact mul_pos (by positivity) h'

lemma rhoMid_le' (x : ℝ) (h : x ≤ 5) : rhoMid x ≤ Real.pi ^ 2 / 4 := by
  rw [rhoMid]
  have hp : (0 : ℝ) < Real.pi ^ 2 / 32 := by positivity
  have h1 : 1 + x + Real.sqrt 2 ≤ 8 := by
    have := sqrt2_lt_two
    linarith
  nlinarith [hp, h1]

lemma rhoQuad_pos' (x : ℝ) (h : -Real.sqrt 2 < x) : 0 < rhoQuad x := by
  rw [rhoQuad]
  have hp := sqrt2_pos'
  have h' : -1 < x / Real.sqrt 2 := by
    rw [lt_div_iff₀ hp]
    nlinarith
  exact mul_pos (by positivity) (pow_pos (by linarith) 2)

lemma rhoQuad_nonneg' (x : ℝ) : 0 ≤ rhoQuad x := by rw [rhoQuad]; positivity

lemma rhoQuad_le' (x : ℝ) (h1 : -Real.sqrt 2 ≤ x) (h2 : x ≤ 0) :
    rhoQuad x ≤ Real.pi ^ 2 / 4 := by
  rw [rhoQuad]
  have hp := sqrt2_pos'
  have ha : -1 ≤ x / Real.sqrt 2 := by
    rw [le_div_iff₀ hp]; nlinarith
  have hb : x / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hp)
  have hsq : (1 + x / Real.sqrt 2) ^ 2 ≤ 1 := by nlinarith
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  nlinarith

/-- The statement of the extension theorem that is proved in the sibling file
`Submission/Work/RPB/B5/extend_rho_per.lean`. -/
lemma extend_rho_per_stmt (ρh : ℝ → ℝ → ℝ → ℝ)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1))
    (hh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (hhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 1,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0)
    (hhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 0, 0 < ρh τ t σ) :
    ∃ (ρe : ℝ → ℝ → ℝ → ℝ) (L : ℝ), 0 < L ∧
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρe z.1 z.2.1 z.2.2) ∧
      (∀ τ t σ, ρe τ (t + 2 * Real.pi) σ = ρe τ t σ) ∧
      (∀ τ t, ρe τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| < 1 / 2 → ρe τ t σ = ρh τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 → |ρh τ t σ| ≤ L * |σ|) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
        deriv (fun s : ℝ => ρe τ t s) σ < 0) := by
  exact extend_rho_per ρh hh hh0 hhper hhmono hhpos

end Work.RPB.B5

end
