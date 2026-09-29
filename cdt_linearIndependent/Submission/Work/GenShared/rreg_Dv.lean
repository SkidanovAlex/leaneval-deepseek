import Mathlib
import Submission.Work.GenShared.periods_defs

/-!
# `Rreg` is preserved by the connection `Dv`

`Rreg f z` (`= f.denom.eval z ≠ 0`, see `Work.GenShared.periods_defs`) says that the rational
function `f` is finite at `z`.  This file proves the elementary closure properties of `Rreg`
under the field operations on `RatFunc ℂ`:

* `rreg_zero`, `rreg_add`, `rreg_mul`, `rreg_neg`, `rreg_sub`, `rreg_sum`;
* `rreg_dRat` — the derivative `dRat` of a rational function that is finite at `z` is again
  finite at `z` (indeed `denom (dRat f) ∣ denom f ^ 2`);
* `rreg_div_poly` — a quotient `P/Q` of polynomials with `Q z ≠ 0` is finite at `z`.

They are the coefficients out of which the connection
`Dv p2 p1 p0 rn rd (a,b,c) = (a' - (p₀/p₂)b + Σ cᵢ rᵢ, a + b' - (p₁/p₂)b, (cᵢ'))`
is built, so they immediately give `rreg_Dv`: on the open set where `p₂` and all the denominators
`rdᵢ` are nonzero, `Dv` maps coefficient tuples regular at `z` to coefficient tuples regular at `z`.
-/

namespace Work.GenShared

open Complex Metric Work.GenShared

open scoped Classical

/-- The zero rational function is finite everywhere. -/
lemma rreg_zero {z : ℂ} : Rreg (0 : RatFunc ℂ) z := by
  simp [Rreg]

/-- `Rreg` is closed under sums: the canonical denominator of `x + y` divides `denom x * denom y`. -/
lemma rreg_add {x y : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) (hy : Rreg y z) :
    Rreg (x + y) z := by
  unfold Rreg at *
  intro h
  obtain ⟨c, hc⟩ := RatFunc.denom_add_dvd x y
  have : (x.denom * y.denom).eval z = 0 := by rw [hc, Polynomial.eval_mul, h, zero_mul]
  rw [Polynomial.eval_mul] at this
  exact mul_ne_zero hx hy this

/-- `Rreg` is closed under products: the canonical denominator of `x * y` divides
`denom x * denom y`. -/
lemma rreg_mul {x y : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) (hy : Rreg y z) :
    Rreg (x * y) z := by
  unfold Rreg at *
  intro h
  obtain ⟨c, hc⟩ := RatFunc.denom_mul_dvd x y
  have : (x.denom * y.denom).eval z = 0 := by rw [hc, Polynomial.eval_mul, h, zero_mul]
  rw [Polynomial.eval_mul] at this
  exact mul_ne_zero hx hy this

/-- The constant `-1` is finite everywhere (`denom (-1) = 1`). -/
lemma rreg_neg_one (z : ℂ) : Rreg (-1 : RatFunc ℂ) z := by
  unfold Rreg
  rw [show (-1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) (-1 : Polynomial ℂ) by
    rw [map_neg, map_one]]
  rw [RatFunc.denom_algebraMap]
  norm_num

/-- `Rreg` is closed under negation, via `-x = (-1) * x`. -/
lemma rreg_neg {x : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) : Rreg (-x) z := by
  have h := rreg_mul (x := (-1 : RatFunc ℂ)) (y := x) (rreg_neg_one z) hx
  simpa using h

/-- `Rreg` is closed under differences. -/
lemma rreg_sub {x y : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) (hy : Rreg y z) :
    Rreg (x - y) z := by
  have h := rreg_add hx (rreg_neg hy)
  simpa [sub_eq_add_neg] using h

/-- `Rreg` is closed under finite sums. -/
lemma rreg_sum {ι : Type*} [Fintype ι] (g : ι → RatFunc ℂ) {z : ℂ}
    (hg : ∀ i, Rreg (g i) z) : Rreg (∑ i, g i) z := by
  have h := Finset.sum_induction (s := Finset.univ) g (fun x => Rreg x z)
    (fun a b ha hb => rreg_add ha hb) (rreg_zero (z := z)) (fun i _ => hg i)
  simpa using h

/-- A quotient `P/Q` of polynomials with `Q z ≠ 0` is finite at `z`
(since `denom (P/Q) ∣ Q`). -/
lemma rreg_div_poly {p q : Polynomial ℂ} {z : ℂ} (hq : q.eval z ≠ 0) :
    Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) q) z := by
  unfold Rreg
  intro h
  obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd p q
  exact hq (by rw [hc, Polynomial.eval_mul, h, zero_mul])

/-- The derivative `dRat f` of a rational function finite at `z` is finite at `z`; indeed
`denom (dRat f) ∣ denom f ^ 2`. -/
lemma rreg_dRat {f : RatFunc ℂ} {z : ℂ} (hf : Rreg f z) : Rreg (Submission.CDT.dRat f) z := by
  unfold Rreg at *
  have hne : (f.denom ^ 2 : Polynomial ℂ) ≠ 0 := pow_ne_zero _ (RatFunc.denom_ne_zero f)
  have hrepr : Submission.CDT.dRat f
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.derivative f.num * f.denom - f.num * Polynomial.derivative f.denom)
        / (algebraMap (Polynomial ℂ) (RatFunc ℂ) f.denom) ^ 2 := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [Submission.CDT.dRat_div]
  have heq : Submission.CDT.dRat f
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.derivative f.num * f.denom - f.num * Polynomial.derivative f.denom)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.denom ^ 2) := by
    rw [hrepr, map_pow]
  have key : (Submission.CDT.dRat f).denom ∣ f.denom ^ 2 :=
    (RatFunc.denom_dvd (x := Submission.CDT.dRat f) hne).mpr ⟨_, heq⟩
  intro h
  obtain ⟨c, hc⟩ := key
  have h2 : (f.denom ^ 2).eval z = 0 := by rw [hc, Polynomial.eval_mul, h, zero_mul]
  rw [Polynomial.eval_pow] at h2
  exact pow_ne_zero 2 hf h2

theorem rreg_Dv {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    {x0 : ℂ} {δ : ℝ} (hp2ne : ∀ z ∈ ball x0 δ, p2.eval z ≠ 0)
    (hrdne : ∀ i, ∀ z ∈ ball x0 δ, (rd i).eval z ≠ 0)
    {z : ℂ} (hz : z ∈ ball x0 δ) {n : W k}
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) (hc : ∀ i, Rreg (n.2.2 i) z) :
    Rreg (Dv p2 p1 p0 rn rd n).1 z ∧ Rreg (Dv p2 p1 p0 rn rd n).2.1 z ∧
      ∀ i, Rreg ((Dv p2 p1 p0 rn rd n).2.2 i) z := by
  refine ⟨?_, ?_, ?_⟩
  · -- `a' - (p₀/p₂)·b + Σᵢ cᵢ·rᵢ`
    simp only [Dv]
    exact rreg_add
      (rreg_sub (rreg_dRat ha) (rreg_mul (rreg_div_poly (hp2ne z hz)) hb))
      (rreg_sum
        (g := fun i => n.2.2 i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)))
        (fun i => rreg_mul (hc i) (rreg_div_poly (hrdne i z hz))))
  · -- `a + b' - (p₁/p₂)·b`
    simp only [Dv]
    exact rreg_sub (rreg_add ha (rreg_dRat hb)) (rreg_mul (rreg_div_poly (hp2ne z hz)) hb)
  · -- `(cᵢ')ᵢ`
    intro i
    simp only [Dv]
    exact rreg_dRat (hc i)

end Work.GenShared
