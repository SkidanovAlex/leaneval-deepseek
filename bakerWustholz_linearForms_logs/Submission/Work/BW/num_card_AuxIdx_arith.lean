import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- Arithmetic core of BW §13 (11): `pT ≤ 11.75 r D ≤ 16 rD`, so `0.001·h·pT ≤ 0.001·S·D/d`
with `S = 16 r d h` and `D = pD r d σ`. -/
theorem num_card_AuxIdx_arith {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    0.001 * (h : ℝ) * (pT r d σ : ℝ) ≤ 0.001 * (pS r d h : ℝ) * pD r d σ / (d : ℝ) := by
  have hD0 : 0 ≤ pD r d σ := le_of_lt (pD_pos hr hd σ hσ)
  have hTle : (pT r d σ : ℝ) ≤ 11.75 * (r : ℝ) * pD r d σ := by
    rw [pT]
    apply Nat.floor_le
    positivity
  have hS : (pS r d h : ℝ) = 16 * (r : ℝ) * (d : ℝ) * (h : ℝ) := by
    simp only [pS]; push_cast; ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  rw [hS]
  have hrw : 0.001 * (16 * (r : ℝ) * (d : ℝ) * (h : ℝ)) * pD r d σ / (d : ℝ)
      = 0.001 * 16 * (r : ℝ) * (h : ℝ) * pD r d σ := by
    field_simp
  rw [hrw]
  have h1 : 0.001 * (h : ℝ) * (pT r d σ : ℝ)
      ≤ 0.001 * (h : ℝ) * (11.75 * (r : ℝ) * pD r d σ) := by
    apply mul_le_mul_of_nonneg_left hTle
    positivity
  have h2 : 0.001 * (h : ℝ) * (11.75 * (r : ℝ) * pD r d σ)
      ≤ 0.001 * 16 * (r : ℝ) * (h : ℝ) * pD r d σ := by
    nlinarith [hD0, hh, hr0]
  linarith

end Work.BW
