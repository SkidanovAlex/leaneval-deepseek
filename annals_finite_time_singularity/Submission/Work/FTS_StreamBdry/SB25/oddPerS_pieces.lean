import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# B8a `oddPerS_pieces`

`Work.FTS_StreamBdry.SB25.OddPerSPieces P`: the odd `π`-periodic extension `oddPerS P` of the
`θ > 0` piece of `P` (`Work.FTS.StreamBdryIface.oddPerS`,

`oddPerS P w θ = if θ < -π/2 then -oddCore(-π-θ) else if θ ≤ π/2 then oddCore θ else -oddCore(π-θ)`

with `oddCore` the odd extension across `θ = 0`) is odd on the strip and agrees with `P`,
`-P(-·)`, `-P(π-·)` on the three pieces `(0,π/2]`, `[-π/2,0)`, `(π/2,π)`.

The argument is a pure case analysis in `θ`: no smoothness, decay or boundary information about
`P` is used, and the hypothesis `P · (π/2) = 0` is in fact not needed for any of the five
conjuncts (it only records that the pieces glue continously at `θ = π/2`).
-/

noncomputable section
open scoped Real

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (oddPerS)

/-- The `θ > 0` piece of `oddPerS`, odd-extended across `θ = 0`:
`oddCore P w θ = P w θ` for `θ > 0`, `= -P w (-θ)` for `θ < 0`, `= 0` at `θ = 0`. -/
def oddCore (P : ℝ → ℝ → ℝ) (w θ : ℝ) : ℝ :=
  if 0 < θ then P w θ else if θ < 0 then -P w (-θ) else 0

/-- `oddCore` on the positive half-line. -/
lemma oddCore_of_pos (P : ℝ → ℝ → ℝ) (w θ : ℝ) (h : 0 < θ) : oddCore P w θ = P w θ := by
  simp only [oddCore]; rw [ite_eq_left h]

/-- `oddCore` on the negative half-line. -/
lemma oddCore_of_neg (P : ℝ → ℝ → ℝ) (w θ : ℝ) (h : θ < 0) : oddCore P w θ = -P w (-θ) := by
  simp only [oddCore]
  rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]

/-- `oddCore` at the origin. -/
lemma oddCore_of_zero (P : ℝ → ℝ → ℝ) (w : ℝ) : oddCore P w 0 = 0 := by
  simp [oddCore]

/-- `oddCore` is odd. -/
lemma oddCore_neg (P : ℝ → ℝ → ℝ) (w θ : ℝ) : oddCore P w (-θ) = -oddCore P w θ := by
  rcases lt_trichotomy θ 0 with h | h | h
  · rw [oddCore_of_pos P w (-θ) (by linarith), oddCore_of_neg P w θ h]; ring
  · subst h; simp [oddCore_of_zero]
  · rw [oddCore_of_neg P w (-θ) (by linarith), oddCore_of_pos P w θ h, neg_neg]

/-- The definition of `oddPerS`, unfolded (definitional). -/
lemma oddPerS_eq (P : ℝ → ℝ → ℝ) (w θ : ℝ) :
    oddPerS P w θ =
      (if θ < -(π / 2) then -oddCore P w (-π - θ)
       else if θ ≤ π / 2 then oddCore P w θ else -oddCore P w (π - θ)) := rfl

/-- `oddPerS` below the strip. -/
lemma oddPerS_of_lt {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h : θ < -(π / 2)) :
    oddPerS P w θ = -oddCore P w (-π - θ) := by
  rw [oddPerS_eq, ite_eq_left h]

/-- `oddPerS` inside the strip `[-π/2, π/2]`. -/
lemma oddPerS_of_mid {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h1 : -(π / 2) ≤ θ) (h2 : θ ≤ π / 2) :
    oddPerS P w θ = oddCore P w θ := by
  rw [oddPerS_eq, ite_eq_right (by linarith : ¬ θ < -(π / 2)), ite_eq_left h2]

/-- `oddPerS` above the strip. -/
lemma oddPerS_of_gt {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h : π / 2 < θ) :
    oddPerS P w θ = -oddCore P w (π - θ) := by
  rw [oddPerS_eq, ite_eq_right (by linarith [Real.pi_pos] : ¬ θ < -(π / 2)),
    ite_eq_right (by linarith : ¬ θ ≤ π / 2)]

theorem oddPerS_pieces (P : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.OddPerSPieces P := by
  intro _h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- oddness on the strip
    intro w θ
    rcases lt_trichotomy θ (-(π / 2)) with hlt | heq | hge
    · -- `θ < -π/2`: the reflection lands above the strip
      have hgt' : π / 2 < -θ := by linarith
      rw [oddPerS_of_gt hgt', oddPerS_of_lt hlt,
        show π - -θ = -(-π - θ) by ring, oddCore_neg]
    · -- `θ = -π/2`
      subst heq
      rw [oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
        oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
        show -(-(π / 2)) = π / 2 by ring, oddCore_neg]
      ring
    · -- `-π/2 < θ`
      by_cases hle : θ ≤ π / 2
      · rw [oddPerS_of_mid (by linarith) (by linarith),
          oddPerS_of_mid (le_of_lt hge) hle, oddCore_neg]
      · -- `π/2 < θ`: the reflection lands below the strip
        have hgt : π / 2 < θ := lt_of_not_ge hle
        have hlt' : -θ < -(π / 2) := by linarith
        rw [oddPerS_of_lt hlt', oddPerS_of_gt hgt,
          show -π - -θ = -(π - θ) by ring, oddCore_neg]
  · -- the `θ > 0` piece
    intro w θ hpos hle
    rw [oddPerS_of_mid (by linarith) hle, oddCore_of_pos P w θ hpos]
  · -- the `θ < 0` piece
    intro w θ hge hneg
    rw [oddPerS_of_mid hge (by linarith), oddCore_of_neg P w θ hneg]
  · -- the `θ > π/2` piece
    intro w θ hgt hlt
    rw [oddPerS_of_gt hgt, oddCore_of_pos P w (π - θ) (by linarith : 0 < π - θ)]
  · -- the origin
    intro w
    rw [oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      oddCore_of_zero P w]

end Work.FTS_StreamBdry.SB25
