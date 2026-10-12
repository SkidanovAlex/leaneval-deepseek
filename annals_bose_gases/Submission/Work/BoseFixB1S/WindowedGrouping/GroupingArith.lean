import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.WindowedGrouping.GroupingArith` — the arithmetic core of FS's grouping

FS's proof of `thm:smallbox` (`final_v2.tex` 3975–4048) groups the `n` particles of a box state
into `m` groups of `n'` particles and one group of `n''` particles, `n = m n' + n''`,
`n' ∈ [C_n μ|B|, (C_n+1)μ|B|)`, `n'' < n'`.  With `ρ := n/|B|`, `ρ' := n'/|B|`, `s := n''/|B|`
the two group bounds they sum are

    m·e_B(n') ≥ m·(1/18)·μ·ρ'·∬w₁                (from `(1/9)(μ−ρ')²`, sharpened this way)
    e_B(n'') ≥ ¼(s−μ)²·∬w₁ − ½μ²·∬w₁ − errors

and their conclusion `c·F(ρ) − ½μ²·∬w₁ − errors'` then follows from the **purely real** comparison

    ¼(s−μ)² + (1/18)μ·mρ'  ≥  c·F(ρ),      F(ρ) = μ(ρ−μ)²/(ρ+μ) = psiWeight 1 μ ρ,

proved here with the explicit constant `c = 1/40` on FS's admissible set (`ρ' ≥ 2μ` — the group
window — and `0 ≤ s ≤ ρ'`).  (Numerically the infimum of the ratio is `≈ 0.056 ≈ 1/18`, approached
as `m, ρ' → ∞` and `s → 0`; the proof only uses `mρ' ≥ ρ/2` for `m ≥ 1`, and the `m = 0` case is
elementary.)

This is a piece of FS's proof that is *absent* from the corpus, and it is independent of which
per-box bound the grouping consumes.  It is the complement of the *refuted* attempt to group the
F-form itself: by `FINDING_LowStateCountCapB1_gate.md` §5 the F-form's left-hand side is strictly
superadditive in the count, so the grouping must run on FS's `A₀`-form (as FS do), and then the
arithmetic above is exactly the last step.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS's grouping arithmetic.**  For `μ > 0`, `ρ' ≥ 2μ`, `0 ≤ s ≤ ρ'`, `m : ℕ`, and
`ρ := mρ' + s`:

    ¼(s−μ)² + (1/18)·μ·(mρ')  ≥  (1/40)·μ·(ρ−μ)²/(ρ+μ) .

These are exactly FS's hypotheses on the group sizes (`ρ' ≥ C_n μ` with `C_n ≥ 2`, `s < n'/|B| ≤ ρ'`),
and `μ·(ρ−μ)²/(ρ+μ) = psiWeight 1 μ ρ` is FS's `F(ρ)` up to the `psiWeight` normalisation.  The
`m = 0` case is the state already inside the window (`ρ = s`). -/
theorem groupingArith {μ ρ' s : ℝ} (m : ℕ) (hμ : 0 < μ) (hρ' : 2 * μ ≤ ρ')
    (hs0 : 0 ≤ s) (hsρ : s ≤ ρ') :
    (1 / 4) * (s - μ) ^ 2 + (1 / 18) * μ * ((m : ℝ) * ρ')
      ≥ (1 / 40) * (μ * ((((m : ℝ) * ρ' + s) - μ) ^ 2 / (((m : ℝ) * ρ' + s) + μ))) := by
  set ρ : ℝ := (m : ℝ) * ρ' + s with hρdef
  have hμ0 : 0 ≤ μ := hμ.le
  have hρ'0 : 0 ≤ ρ' := le_trans (by linarith : (0 : ℝ) ≤ 2 * μ) hρ'
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) hρ'0) hs0
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: `ρ = s`, and the square term alone suffices
    subst hm
    have hρs : ρ = s := by rw [hρdef]; simp
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [show ρ = s from hρs]
    have hpos' : 0 < s + μ := by linarith
    have h1 : μ * ((s - μ) ^ 2 / (s + μ)) ≤ 10 * (s - μ) ^ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hpos']
      nlinarith [sq_nonneg (s - μ), hs0, hμ]
    have h2 : (1 / 40 : ℝ) * (10 * (s - μ) ^ 2) = (1 / 4) * (s - μ) ^ 2 := by ring
    linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 40), h2.le, h2.ge]
  · -- `m ≥ 1`: `mρ' ≥ ρ/2`
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hρ'ρ : ρ' ≤ ρ := by rw [hρdef]; nlinarith [hm1, hρ'0, hs0]
    have h2μρ : 2 * μ ≤ ρ := le_trans hρ' hρ'ρ
    have hpos : 0 < ρ + μ := by linarith
    have hb1 : (ρ - μ) ^ 2 / (ρ + μ) ≤ ρ := by
      rw [div_le_iff₀ hpos]
      nlinarith [h2μρ, hμ0]
    have hkey : (1 / 2 : ℝ) * ρ ≤ (m : ℝ) * ρ' := by
      have h1 : ρ ≤ ((m : ℝ) + 1) * ρ' := by
        rw [hρdef]; nlinarith [hsρ]
      have h2 : ((m : ℝ) / ((m : ℝ) + 1)) * (((m : ℝ) + 1) * ρ') = (m : ℝ) * ρ' := by
        field_simp
      have h3 : ((m : ℝ) / ((m : ℝ) + 1)) * ρ ≤ (m : ℝ) * ρ' := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : (1 / 2 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < (m : ℝ) + 1)]
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right h4 hρ0) h3
    have hA : (1 / 18 : ℝ) * μ * ((m : ℝ) * ρ') ≥ (1 / 36) * μ * ρ := by
      nlinarith [hkey, hμ0, hρ0]
    have hB : (1 / 40 : ℝ) * (μ * ((ρ - μ) ^ 2 / (ρ + μ))) ≤ (1 / 40) * μ * ρ := by
      nlinarith [mul_le_mul_of_nonneg_left hb1 hμ0, hμ0, hρ0]
    have hC : (1 / 40 : ℝ) * μ * ρ ≤ (1 / 36) * μ * ρ := by nlinarith [hμ0, hρ0]
    have hsq : (0 : ℝ) ≤ (1 / 4) * (s - μ) ^ 2 := by positivity
    rw [hρdef] at hA hB hC ⊢
    linarith [hsq, hA, hB, hC]

end Work.BoseFixB1S
