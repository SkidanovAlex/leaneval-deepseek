import Mathlib
import Submission.Work.LT.sin_sq_even_natAbs
import Submission.Work.LT.sin_sq_natAbs_ge_half

namespace Work.LT

/-! **The `ℓ²`-distance from `1` to a standard additive character of `ℤ/p`.**

`‖ω^t − 1‖² = 4 sin²(π·|t|/p)`, where `ω = ZMod.stdAddChar` and `|t|` is the absolutely least
residue `(ZMod.valMinAbs t).natAbs`; and this is at least `2` as soon as `4|t| ≥ p` (the range
`|t| ≤ p/2` of `valMinAbs` puts `π|t|/p ∈ [π/4, π/2]`, where `sin² ≥ 1/2`).

ROUTE. `ZMod.stdAddChar_apply` writes `ZMod.stdAddChar t = ↑(ZMod.toCircle t)`, and
`ZMod.toCircle` is `Circle.exp (2π·t.val/p)`; `Circle.coe_exp` turns this into
`Complex.exp (2π i x/p)`. Then `Complex.normSq` of the difference of two unit complex numbers is
`2 − 2 * re`, and `re (exp (iθ)) = cos θ` gives `2 − 2 cos(2π x/p) = 4 sin²(π x/p)`. Replacing
`t.val` by the representative `ZMod.valMinAbs t` (congruent mod `p`, with `ZMod.valMinAbs_spec`)
does not change `sin²` (periodicity `sin²(π(k+p)/p) = sin²(πk/p)` and evenness `sin²(−x) = sin² x`).
For the second part use `ZMod.natAbs_valMinAbs_le : (ZMod.valMinAbs t).natAbs ≤ p/2` and the
monotonicity of `sin` on `[π/4, π/2]` (`Real.sin_le_one`, `Real.sin_lt_sin` / `Real.sin_injOn`). -/

/-- For a real number `x`, the squared distance from `1` to the point `exp (↑x * I)` of the unit
circle is `4 sin²(x / 2)`: the two points are `cos x + sin x * I` and `1`, so by
`Complex.normSq_sub` the distance squared is `1 + 1 - 2 cos x`, and
`Real.sin_sq_eq_half_sub` converts this into `4 sin²(x/2)`. -/
theorem normSq_exp_I_sub_one (x : ℝ) :
    Complex.normSq (Complex.exp (↑x * Complex.I) - 1) = 4 * Real.sin (x / 2) ^ 2 := by
  rw [Complex.normSq_sub]
  have h1 : Complex.normSq (Complex.exp (↑x * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  have h2 : (Complex.exp (↑x * Complex.I) * (starRingEnd ℂ) 1).re = Real.cos x := by
    simp [Complex.exp_re]
  rw [h1, h2, Complex.normSq_one]
  have h3 := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h3
  rw [h3]
  ring

/-- The standard additive character of `ℤ/p` at `t` in exponential form, using the absolutely
least residue as the representative of `t` (this is what `ZMod.coe_valMinAbs` and
`ZMod.stdAddChar_coe` give directly, no congruence reduction is needed). -/
theorem stdAddChar_eq_exp (p : ℕ) [NeZero p] (t : ZMod p) :
    ZMod.stdAddChar t =
      Complex.exp (↑(2 * Real.pi * ((ZMod.valMinAbs t : ℤ) : ℝ) / p) * Complex.I) := by
  rw [← ZMod.coe_valMinAbs t, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The `ℓ²`-distance identity. -/
theorem stdAddChar_sin_normSq (p : ℕ) [NeZero p] (t : ZMod p) :
    Complex.normSq (ZMod.stdAddChar t - 1)
      = 4 * Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2 := by
  rw [stdAddChar_eq_exp, normSq_exp_I_sub_one]
  have harg : (2 * Real.pi * ((ZMod.valMinAbs t : ℤ) : ℝ) / p) / 2
      = Real.pi * ((ZMod.valMinAbs t : ℤ) : ℝ) / p := by ring
  rw [harg, sin_sq_even_natAbs]

/-- The lower bound: once `4 |t| ≥ p`, the character is at least `√2` away from `1`. -/
theorem stdAddChar_sin_ge_two (p : ℕ) [NeZero p] (t : ZMod p)
    (h : p ≤ 4 * (ZMod.valMinAbs t).natAbs) :
    2 ≤ 4 * Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2 := by
  have h' := sin_sq_natAbs_ge_half p t h
  linarith

theorem stdAddChar_sin :
    ∀ (p : ℕ) [NeZero p] (t : ZMod p),
      Complex.normSq (ZMod.stdAddChar t - 1)
        = 4 * Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2
      ∧ (p ≤ 4 * (ZMod.valMinAbs t).natAbs →
          2 ≤ 4 * Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2) := by
  intro p _ t
  exact ⟨stdAddChar_sin_normSq p t, fun h => stdAddChar_sin_ge_two p t h⟩

end Work.LT
