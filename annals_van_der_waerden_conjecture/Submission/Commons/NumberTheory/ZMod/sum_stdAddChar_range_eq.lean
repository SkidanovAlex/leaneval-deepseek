import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Commons.NumberTheory.ZMod

open Finset

section
variable (p : ℕ)
-- The statement below is written with the natural-number scalar `k * d`, which is the
-- coercion `((k : ZMod p) * d)`.  This local instance lets Lean elaborate that coercion
-- when the type of the argument of `stdAddChar` is not yet known.
local instance instHMulNatZMod : HMul ℕ (ZMod p) (ZMod p) := ⟨fun k d => (k : ZMod p) * d⟩

/-- Geometric-series identity for the standard additive character of `ZMod p`:
the sum of `stdAddChar (k * d)` over `k < L` equals
`(1 - stdAddChar (L * d)) / (1 - stdAddChar d)` whenever `d ≠ 0`. -/
theorem sum_stdAddChar_range_eq (p : ℕ) [Fact p.Prime] (d : ZMod p) (hd : d ≠ 0) (L : ℕ) :
    ∑ k ∈ Finset.range L, ZMod.stdAddChar (k * d)
      = (1 - ZMod.stdAddChar ((L : ZMod p) * d)) / (1 - ZMod.stdAddChar d) := by
  have hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hd1 : ZMod.stdAddChar d ≠ 1 := by
    intro h
    rw [← (ZMod.stdAddChar (N := p)).map_zero_eq_one] at h
    exact hd (ZMod.injective_stdAddChar h)
  have hterm : ∀ k : ℕ, ZMod.stdAddChar (k * d) = ZMod.stdAddChar d ^ k := by
    intro k
    show ZMod.stdAddChar ((k : ZMod p) * d) = ZMod.stdAddChar d ^ k
    rw [← nsmul_eq_mul, ZMod.stdAddChar.map_nsmul_eq_pow]
  have hpow : ZMod.stdAddChar d ^ L = ZMod.stdAddChar ((L : ZMod p) * d) := by
    rw [← ZMod.stdAddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), geom_sum_eq hd1 L, hpow]
  rw [div_eq_mul_inv, div_eq_mul_inv,
      show (1 : ℂ) - ZMod.stdAddChar ((L : ZMod p) * d) =
        -(ZMod.stdAddChar ((L : ZMod p) * d) - 1) by ring,
      show (1 : ℂ) - ZMod.stdAddChar d = -(ZMod.stdAddChar d - 1) by ring,
      inv_neg, neg_mul_neg]

end

end Commons.NumberTheory.ZMod