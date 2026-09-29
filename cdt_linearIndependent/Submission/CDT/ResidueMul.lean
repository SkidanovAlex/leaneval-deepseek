import Mathlib
import Submission.CDT.Residue

/-!
# The residue calculus, multiplicatively refined

`Submission.CDT.Residue` develops the first-order local structure of `K(X)` at a point `α`: the
relation `ResidueAt α r c` ("`r` has at most a simple pole at `α`, of residue `c`") and, above all,
the residue of a logarithmic derivative, `ResidueAt α ((dRat f)/f) (ordAt α f)`.

The function-field Lindemann–Weierstrass theorem *of weight one*
(`Submission.CDT.LogMultiplicativeField`, `Submission.CDT.LogRelation`) uses only the residue of a
sum: `Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h` gives `Σᵢ cᵢ·ordAt α fᵢ = 0` for every `α`, because `dRat h`
never has a simple pole.

The *weight-two* theory (products of logarithms) needs one more local fact: the residue of a
**product** of a function that is finite at `α` with a function having a simple pole there.  That is
the content of this file:

* `zero_le_ordAt_sub_valueAt` — `ordAt α (g - valueAt α g) ≥ 0` when `ordAt α g = 0`;
* **`ResidueAt.mul`** — if `ordAt α r = 0` and `ResidueAt α s d`, then
  `ResidueAt α (r * s) (valueAt α r * d)`: the residue is multiplied by the *value* of `r` at `α`;
* **`residueAt_mul_dRat_div_self`** — the special case `s = (dRat f)/f`: the residue of
  `r·(dRat f)/f` at `α` is `valueAt α r · ordAt α f`;
* **`residueAt_dRat_div_self_mul_dRat_div_self`** — the product of two logarithmic derivatives.

The proof of `ResidueAt.mul` is the elementary one: writing `r = valueAt α r + (r - valueAt α r)`
and `s = d/(X-α) + (s - d/(X-α))`, the two "correction" terms have nonnegative order, and the
product `valueAt α r · d/(X-α)` is exactly the elementary pole `polePart α (valueAt α r · d)`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- If `g` is finite at `α` (`ordAt α g = 0`), then subtracting its value there does not lower the
order of vanishing: `ordAt α (g - valueAt α g) ≥ 0`.  (When `g` *is* the constant `valueAt α g`
the difference vanishes and this is `ordAt_zero`.) -/
lemma zero_le_ordAt_sub_valueAt {α : K} {g : RatFunc K} (hg : ordAt α g = 0) :
    0 ≤ ordAt α (g - algebraMap K (RatFunc K) (valueAt α g)) := by
  rcases eq_or_ne g (algebraMap K (RatFunc K) (valueAt α g)) with h | h
  · rw [sub_eq_zero.mpr h, ordAt_zero]
  · exact le_trans (by norm_num) (one_le_ordAt_sub_valueAt hg h)

/-- **Multiplicativity of residues.**  If `r` is finite at `α` (`ordAt α r = 0`) and `s` has at
most a simple pole there with residue `d`, then the product has at most a simple pole with residue
`valueAt α r · d`. -/
theorem ResidueAt.mul {α : K} {r s : RatFunc K} {d : K} (hr : ordAt α r = 0)
    (hs : ResidueAt α s d) : ResidueAt α (r * s) (valueAt α r * d) := by
  rcases eq_or_ne r 0 with hzero | hrne
  · -- the product vanishes: both sides are `0`
    have hv : valueAt α (0 : RatFunc K) = 0 := by
      simp [valueAt, RatFunc.num_zero, RatFunc.denom_zero]
    rw [hzero, hv, zero_mul, zero_mul]
    have hp : polePart α (0 : K) = 0 := by rw [polePart_eq, map_zero, zero_div]
    refine ⟨by rw [ordAt_zero]; norm_num, ?_⟩
    rw [hp, sub_zero, ordAt_zero]
  have hsplit : r * s - polePart α (valueAt α r * d)
      = (r - algebraMap K (RatFunc K) (valueAt α r)) * polePart α d
        + r * (s - polePart α d) := by
    rw [polePart_mul]; ring
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne s 0 with h | h
    · rw [h, mul_zero, ordAt_zero]; norm_num
    · rw [ordAt_mul α hrne h, hr, zero_add]; exact hs.1
  · rw [hsplit]
    -- the two summands have nonnegative order
    have hA : 0 ≤ ordAt α ((r - algebraMap K (RatFunc K) (valueAt α r)) * polePart α d) := by
      rcases eq_or_ne d 0 with hd | hd
      · have hp : polePart α d = 0 := by rw [hd, polePart_eq, map_zero, zero_div]
        rw [hp, mul_zero, ordAt_zero]
      · have hpp : polePart α d ≠ 0 := polePart_ne_zero α hd
        rcases eq_or_ne (r - algebraMap K (RatFunc K) (valueAt α r)) 0 with h0 | h0
        · rw [h0, zero_mul, ordAt_zero]
        · rw [ordAt_mul α h0 hpp, ordAt_polePart α hd]
          have := one_le_ordAt_sub_valueAt hr (sub_ne_zero.mp h0)
          linarith
    have hB : 0 ≤ ordAt α (r * (s - polePart α d)) := by
      rcases eq_or_ne (s - polePart α d) 0 with h0 | h0
      · rw [h0, mul_zero, ordAt_zero]
      · rw [ordAt_mul α hrne h0, hr, zero_add]; exact hs.2
    rcases eq_or_ne ((r - algebraMap K (RatFunc K) (valueAt α r)) * polePart α d
        + r * (s - polePart α d)) 0 with h0 | h0
    · rw [h0, ordAt_zero]
    · exact (le_min hA hB).trans (min_ordAt_le_ordAt_add α h0)

/-- **The residue of `r · (f'/f)`**: if `r` is finite at `α`, the residue of the product of `r`
with the logarithmic derivative of `f` is `valueAt α r · ordAt α f`. -/
theorem residueAt_mul_dRat_div_self {α : K} {r : RatFunc K} (hr : ordAt α r = 0)
    (f : RatFunc K) (hf : f ≠ 0) :
    ResidueAt α (r * (dRat f / f)) (valueAt α r * ((ordAt α f : ℤ) : K)) :=
  ResidueAt.mul hr (residueAt_dRat_div_self f hf α)

/-- **The residue of a product of two logarithmic derivatives.**  Suppose the logarithmic
derivative of `g` is finite and nonzero at `α` (`ordAt α (dRat g / g) = 0`, which forces `g` itself
to be finite and nonzero there).  Then the residue of the product `(f'/f)·(g'/g)` at `α` is
`(g'/g)(α) · ordAt α f`: it vanishes when `f` too is finite at `α`, and is the expected simple-pole
residue when `f` has a zero or a pole. -/
theorem residueAt_dRat_div_self_mul_dRat_div_self {α : K} {f g : RatFunc K} (hf : f ≠ 0)
    (hgg : ordAt α (dRat g / g) = 0) :
    ResidueAt α ((dRat f / f) * (dRat g / g))
      (valueAt α (dRat g / g) * ((ordAt α f : ℤ) : K)) := by
  rcases eq_or_ne (ordAt α f) 0 with hf0 | hf0
  · -- `f` is also finite at `α`: the product is holomorphic and the residue vanishes
    rw [hf0, Int.cast_zero, mul_zero]
    refine ResidueAt.of_ordAt_nonneg ?_
    rcases eq_or_ne (dRat f / f) 0 with h0 | h0
    · rw [h0, zero_mul, ordAt_zero]
    · rcases eq_or_ne (dRat g / g) 0 with h1 | h1
      · rw [h1, mul_zero, ordAt_zero]
      · rw [ordAt_mul α h0 h1, hgg, add_zero]
        exact zero_le_ordAt_dRat_div_self_of_ordAt_eq_zero hf hf0
  · -- `f` has a zero or a pole at `α`
    have h := ResidueAt.mul (s := dRat f / f) hgg (residueAt_dRat_div_self f hf α)
    unfold ResidueAt at h ⊢
    rw [mul_comm (dRat g / g) (dRat f / f)] at h
    exact h

/-- **A weight-two Lindemann–Weierstrass obstruction.**  If `α` is a zero or a pole of `f` while
the logarithmic derivative of `g` is finite and *nonzero* at `α` (`ordAt α (dRat g / g) = 0` and
`valueAt α (dRat g / g) ≠ 0`), then the product `(f'/f)·(g'/g)` of logarithmic derivatives — whose
residue at `α` is the nonzero number `(g'/g)(α)·ordAt α f` — is **not** the derivative of any
rational function, since `dRat h` never has a simple pole (`ordAt_dRat_ne_neg_one`). -/
theorem dRat_ne_mul_dRat_div_self_div_self {α : K} {f g h : RatFunc K} (hf : f ≠ 0)
    (hgg : ordAt α (dRat g / g) = 0) (hval : valueAt α (dRat g / g) ≠ 0)
    (hf0 : ordAt α f ≠ 0) :
    dRat h ≠ (dRat f / f) * (dRat g / g) := by
  intro hh
  have hres := residueAt_dRat_div_self_mul_dRat_div_self hf hgg
  rw [← hh] at hres
  have hr : valueAt α (dRat g / g) * ((ordAt α f : ℤ) : K) ≠ 0 :=
    mul_ne_zero hval (by
      intro h0
      exact hf0 (Int.cast_eq_zero.mp (by simpa using h0 : ((ordAt α f : ℤ) : K) = 0)))
  exact ordAt_dRat_ne_neg_one α h (hres.ordAt_eq_neg_one hr)

end Submission.CDT
