import Mathlib
import Submission.Work.CNum.SerUpDefs

/-!
# `Work.CNum.SerStepArith` — the arithmetic step of the `serUp` state invariant

`Work.CNum.snpe σ pe = mulU σ pe + 2` is the mantissa that the `serUp` recursion
(`Work.CNum.Fx.serAuxB`) carries for the accumulated error of the complex mantissa `c^(k+1)`, where
`c` is the centre of an enclosing ball and `σ` bounds the geometric factor `srad x y e = ‖c‖ + ρ`.

`mulU a b = ⌈a·b/SC⌉` is the outward-rounded product at scale `SC = 2^30`
(`Work.CNum.Fx.mulU`), so `m2r (snpe σ pe) = ⌈σ·pe/SC⌉/SC + 2/SC` is (up to the added `2/SC`, a
safety margin for one multiplication by `c`) an upper bound for the real product
`m2r σ · m2r pe`.  The state invariant `Work.CNum.SerInv` therefore asks for

`0 ≤ pe`, `m2r pe ≤ 3`  ⟹  `0 ≤ snpe σ pe` and `m2r (snpe σ pe) ≤ 3`

whenever `σ` bounds a disc radius (`0 ≤ σ`, `m2r σ < 1`): the *error mantissa stays in the same
band `[0,3]`* after one step of the recursion.  This is pure integer arithmetic at scale `SC`, and
it is exactly what the induction of `SerInvStep` needs about the error component.

The proof is sharp, with no slack: `m2r σ < 1` with `σ ∈ ℤ`, `σ ≥ 0` gives `σ ≤ SC - 1`, and
`m2r pe ≤ 3` gives `pe ≤ 3·SC`, so

`⌈σ·pe/SC⌉ · SC ≤ σ·pe + SC - 1 ≤ (3·SC² - 3·SC) + SC - 1`,

i.e. `⌈σ·pe/SC⌉ + 2 ≤ 3·SC - 1 < 3·SC`, whence `m2r (snpe σ pe) < 3`.  The crucial rounding input
is `mulU_mul_SC_le` below: the ceiling division overshoots by strictly less than one unit of `SC`.
-/

namespace Work.CNum

open Work.ANum

/-- The rounding-up multiplication `mulU a b = ⌈a·b/SC⌉` overshoots the true product `a·b` by
strictly less than one unit of `SC`:
`mulU a b * SC ≤ a*b + (SC - 1)`.  (The other direction, `a*b ≤ mulU a b * SC`, is
`Work.CNum.m2r_mulU_ge`.) -/
lemma mulU_mul_SC_le (a b : ℤ) : mulU a b * SC ≤ a * b + (SC - 1) := by
  have h : -(a * b) < (Int.ediv (-(a * b)) SC + 1) * SC :=
    Int.lt_ediv_add_one_mul_self (-(a * b)) (b := SC) SC_pos
  simp only [mulU]
  linarith

theorem SerStepArith {σ pe : ℤ} (hpe : 0 ≤ pe) (hpe3 : Work.ANum.m2r pe ≤ 3) (hσlt : Work.ANum.m2r σ < 1) (hσ0 : 0 ≤ σ) : 0 ≤ Work.CNum.snpe σ pe ∧ Work.ANum.m2r (Work.CNum.snpe σ pe) ≤ 3 := by
  -- Mantissa bounds for the two inputs: `σ ≤ SC - 1`, `pe ≤ 3·SC`.
  have hσS : σ ≤ SC - 1 := by
    have h : (σ : ℝ) < (SC : ℝ) := by
      have h2 := hσlt
      rw [m2r, div_lt_one SC_posR] at h2
      exact h2
    have h3 : σ < SC := by exact_mod_cast h
    omega
  have hpeS : pe ≤ 3 * SC := by
    have h2 := hpe3
    rw [m2r, div_le_iff₀ SC_posR] at h2
    exact_mod_cast h2
  -- `σ·pe ≤ 3SC² - 3SC`, the extreme case `σ = SC - 1`, `pe = 3SC`.
  have hX : σ * pe ≤ 3 * SC * SC - 3 * SC := by
    have h1 : σ * pe ≤ (SC - 1) * pe := mul_le_mul_of_nonneg_right hσS hpe
    have h2 : (SC - 1) * pe ≤ (SC - 1) * (3 * SC) := mul_le_mul_of_nonneg_left hpeS (by omega)
    nlinarith [h1, h2]
  -- The ceiling rounding: `(⌈σ·pe/SC⌉ + 2)·SC ≤ 3SC²`.
  have hkey : (mulU σ pe + 2) * SC ≤ (3 * SC) * SC := by
    have hB := mulU_mul_SC_le σ pe
    nlinarith [hB, hX]
  have hkey' : mulU σ pe + 2 ≤ 3 * SC :=
    (Int.mul_le_mul_right SC_pos).mp hkey
  have h3SC : m2r (3 * SC) = 3 := by
    rw [m2r]
    push_cast
    rw [mul_div_cancel_right₀ _ (ne_of_gt SC_posR)]
  constructor
  · -- Nonnegativity: `⌈σ·pe/SC⌉ ≥ 0` since `σ·pe ≥ 0`.
    have hmul0 : 0 ≤ mulU σ pe := by
      have h0 : 0 ≤ σ * pe := mul_nonneg hσ0 hpe
      have hed : Int.ediv (-(σ * pe)) SC ≤ 0 := by
        have hlt : Int.ediv (-(σ * pe)) SC < 1 := by
          have hiff : Int.ediv (-(σ * pe)) SC < 1 ↔ -(σ * pe) < 1 * SC :=
            Int.ediv_lt_iff_lt_mul SC_pos
          rw [hiff]
          linarith
        omega
      simp only [mulU]
      omega
    simp only [snpe]
    omega
  · -- The upper bound: `m2r (⌈σ·pe/SC⌉ + 2) ≤ 3`.
    have h := m2r_le hkey'
    rw [h3SC] at h
    exact h

end Work.CNum
