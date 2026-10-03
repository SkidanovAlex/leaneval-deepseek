import Mathlib
import Submission.Work.A3.CSPoly

/-!
# The shift identity for complete exponential sums (Area A3)

This module proves the elementary but essential identity behind the major-arc analysis of the
complete exponential sum `completeSum` of Area A3:

if `p` is a prime, `k ≤ ν`, `h = p^k * u` and `q = p ^ (ν - k)`, then

`∑_{r < p^ν} e(-2πi a (g(r+h) - g(r)) / p^ν) = p^k * completeSum (polydiff g h) (a*u) q`.

Equivalently: the string `a*(g(r+h) - g(r))/p^ν = a*u*(polydiff g h)(r)/q` is, as a function of
`r`, periodic with period `q = p^(ν-k)`, and `∑_{r<p^ν} = p^k ∑_{s<q}`.

The three ingredients are

* `shiftEq_polydiff_eval_mul` — the defining property of the divided difference
  `polydiff g h`: `h * (polydiff g h).eval t = g.eval (t + h) - g.eval t` (no hypothesis on `h`);
* `shiftEq_dvd_eval_sub_eval` — integer polynomial evaluation respects congruences
  (`q ∣ x - y → q ∣ Q.eval x - Q.eval y`), so `(polydiff g h)(p^(ν-k) j + s) ≡ (polydiff g h)(s)`
  mod `p^(ν-k)`;
* `shiftEq_sum_range_mul` — the reindexing of `∑_{r<n*q}` as the double sum over
  `range n × range q`.

The result `sum_shift_eq` is the discrete ("major arc at the rational a/p^k") step of the
power-saving estimate `Work.A3.completeSum_power_saving`.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset

noncomputable section

/-- **The defining property of the divided difference `polydiff`**: for every integer polynomial
`g` and integers `h`, `t`,

`h * (polydiff g h).eval t = g.eval (t + h) - g.eval t`.

(No hypothesis on `h` is needed: for `h = 0` the identity reads `0 = 0`, and `polydiff g 0` is the
formal derivative of `g`.) -/
lemma shiftEq_polydiff_eval_mul (g : ℤ[X]) (h t : ℤ) :
    (polydiff g h).eval t * h = g.eval (t + h) - g.eval t := by
  have hmono : ∀ i : ℕ, (∑ j ∈ Finset.range i, ((i.choose j : ℤ) * h ^ (i - j - 1)) * t ^ j) * h
      = (t + h) ^ i - t ^ i := by
    intro i
    rw [Finset.sum_mul]
    have hb := add_pow t h i
    rw [Finset.sum_range_succ] at hb
    simp only [tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one] at hb
    rw [hb, add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < i := Finset.mem_range.mp hj
    have hpow : h ^ (i - j) = h ^ (i - j - 1) * h := by
      rw [← pow_succ, show i - j - 1 + 1 = i - j by omega]
    rw [hpow]
    ring
  rw [polydiff]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Finset.sum_mul]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, ← mul_sub, hmono i]

/-- Integer polynomial evaluation respects congruence modulo `q`. -/
lemma shiftEq_dvd_eval_sub_eval {Q : ℤ[X]} {q x y : ℤ} (h : q ∣ x - y) :
    q ∣ Q.eval x - Q.eval y :=
  dvd_trans h (Polynomial.sub_dvd_eval_sub x y Q)

/-- **Reindexing**: a sum over `range (n * q)` is the double sum over `range n × range q` along the
bijection `(j, s) ↦ q * j + s`. -/
lemma shiftEq_sum_range_mul (n q : ℕ) (F : ℕ → ℂ) (hq : 0 < q) :
    (∑ r ∈ Finset.range (n * q), F r)
      = ∑ x ∈ Finset.range n ×ˢ Finset.range q, F (q * x.1 + x.2) := by
  refine Finset.sum_bij (fun x (_ : x ∈ Finset.range (n * q)) => (x / q, x % q)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact (Finset.mem_range.mp hx)),
      Nat.mod_lt x hq⟩
  · intro x1 h1 x2 h2 heq
    have h1' : x1 / q = x2 / q := by simpa using congrArg Prod.fst heq
    have h2' : x1 % q = x2 % q := by simpa using congrArg Prod.snd heq
    calc x1 = q * (x1 / q) + x1 % q := (Nat.div_add_mod x1 q).symm
      _ = q * (x2 / q) + x2 % q := by rw [h1', h2']
      _ = x2 := Nat.div_add_mod x2 q
  · intro b hb
    simp only [Finset.mem_product, Finset.mem_range] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨q * b.1 + b.2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have hstep : q * b.1 + b.2 < q * (b.1 + 1) := by nlinarith
      calc q * b.1 + b.2 < q * (b.1 + 1) := hstep
        _ = q * b.1 + q := by ring
        _ ≤ q * n := by nlinarith
        _ = n * q := by ring
    · ext
      · simp only
        rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hb2]
        simp
      · simp only
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hb2
  · intro x _
    rw [Nat.div_add_mod]

/-- **The pointwise shift identity**: for `h = p^k * u` and `q = p^(ν-k)`, the summand of the
shifted sum takes the value of the `q`-complete sum of the divided difference at `s`, for every
`r = q * j + s`.  (In particular it is `q`-periodic in `r`.) -/
lemma shiftEq_completeSum_term (g : ℤ[X]) (a u : ℤ) (p ν k : ℕ) (hp : p.Prime) (hk : k ≤ ν)
    (j s : ℕ) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
        Complex.ofReal (((a * (g.eval ((((p ^ (ν - k) * j + s : ℕ)) : ℤ) + ((p : ℤ) ^ k * (u : ℤ)))
          - g.eval (((p ^ (ν - k) * j + s : ℕ)) : ℤ)) : ℤ) : ℝ) / (((p ^ ν : ℕ)) : ℝ)))
      = Complex.exp (-(2 * Real.pi * Complex.I *
          (Complex.ofReal ((((a * (u : ℤ)) : ℤ) : ℝ)) *
            Complex.ofReal ((((polydiff g ((p : ℤ) ^ k * (u : ℤ))).eval ((s : ℕ) : ℤ) : ℤ) : ℝ)) /
            Complex.ofReal (((p ^ (ν - k) : ℕ) : ℝ))))) := by
  set h : ℤ := (p : ℤ) ^ k * (u : ℤ) with hh
  set q : ℕ := p ^ (ν - k) with hqdef
  have hN : p ^ ν = p ^ k * q := by rw [hqdef, ← pow_add, Nat.add_sub_cancel' hk]
  have hR : (((q * j + s : ℕ)) : ℤ) = (j : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
  have hdvd : (q : ℤ) ∣ (polydiff g h).eval (((q * j + s : ℕ)) : ℤ)
      - (polydiff g h).eval ((s : ℕ) : ℤ) :=
    dvd_trans (show (q : ℤ) ∣ (((q * j + s : ℕ) : ℤ) - ((s : ℕ) : ℤ)) by
        rw [hR]; exact ⟨(j : ℤ), by ring⟩)
      (Polynomial.sub_dvd_eval_sub _ _ (polydiff g h))
  obtain ⟨c, hc⟩ := hdvd
  have hpd := shiftEq_polydiff_eval_mul g h (((q * j + s : ℕ)) : ℤ)
  have hpde : (polydiff g h).eval (((q * j + s : ℕ)) : ℤ)
      = (polydiff g h).eval ((s : ℕ) : ℤ) + (q : ℤ) * c := by linarith [hc]
  have h1 : g.eval ((((q * j + s : ℕ)) : ℤ) + h) - g.eval (((q * j + s : ℕ)) : ℤ)
      = ((polydiff g h).eval ((s : ℕ) : ℤ) + (q : ℤ) * c) * h := by
    rw [← hpd, hpde]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpk0 : (((p ^ k : ℕ)) : ℝ) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ (ne_of_gt hp0)
  have hq0R : ((q : ℕ) : ℝ) ≠ 0 := by
    rw [hqdef, Nat.cast_pow]; exact pow_ne_zero _ (ne_of_gt hp0)
  have hhR : ((h : ℤ) : ℝ) = (((p ^ k : ℕ)) : ℝ) * (u : ℝ) := by rw [hh]; push_cast; ring
  have hNR : (((p ^ ν : ℕ)) : ℝ) = (((p ^ k : ℕ)) : ℝ) * ((q : ℕ) : ℝ) := by
    rw [hN]; push_cast; ring
  have hreal : (((a * (g.eval ((((q * j + s : ℕ)) : ℤ) + h)
        - g.eval (((q * j + s : ℕ)) : ℤ)) : ℤ)) : ℝ) / (((p ^ ν : ℕ)) : ℝ)
      = ((((a * (u : ℤ)) : ℤ)) : ℝ) * ((((polydiff g h).eval ((s : ℕ) : ℤ) : ℤ)) : ℝ) / ((q : ℕ) : ℝ)
        + (((a * (u : ℤ) * c : ℤ)) : ℝ) := by
    rw [h1]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast]
    rw [hhR, hNR]
    have hmul0 : (((p ^ k : ℕ)) : ℝ) * ((q : ℕ) : ℝ) ≠ 0 := mul_ne_zero hpk0 hq0R
    field_simp
  rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
  conv_rhs => rw [← neg_mul]
  rw [hreal, Complex.ofReal_add, mul_add, Complex.exp_add]
  have hm : Complex.exp (-(2 * Real.pi * Complex.I) *
      Complex.ofReal (((a * (u : ℤ) * c : ℤ)) : ℝ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-(a * (u : ℤ) * c), by push_cast; ring⟩
  rw [hm, mul_one]

/-- **The shift identity** for the complete exponential sum, in the form in which it is used:
multiplying the shift `h` by the prime power `p^k` costs a factor `p^k` and shifts the modulus from
`p^ν` to `p^(ν-k)`, the polynomial `g` being replaced by its divided difference `polydiff g h`. -/
theorem sum_shift_eq_general (g : ℤ[X]) (a u : ℤ) (p ν k : ℕ) (hp : p.Prime) (hk : k ≤ ν) :
    (∑ r ∈ Finset.range (p ^ ν), Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + ((p : ℤ) ^ k * (u : ℤ))) - g.eval (r : ℤ)) : ℤ) : ℝ) /
          (((p ^ ν : ℕ) : ℝ)))))
      = ((p : ℂ) ^ k) * completeSum (polydiff g ((p : ℤ) ^ k * (u : ℤ)))
          (a * (u : ℤ)) (p ^ (ν - k)) := by
  let F : ℕ → ℂ := fun r => Complex.exp (-(2 * Real.pi * Complex.I) *
      Complex.ofReal (((a * (g.eval ((r : ℤ) + ((p : ℤ) ^ k * (u : ℤ))) - g.eval (r : ℤ)) : ℤ) : ℝ) /
        (((p ^ ν : ℕ) : ℝ))))
  have hL : (∑ r ∈ Finset.range (p ^ ν), Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + ((p : ℤ) ^ k * (u : ℤ))) - g.eval (r : ℤ)) : ℤ) : ℝ) /
          (((p ^ ν : ℕ) : ℝ))))) = ∑ r ∈ Finset.range (p ^ ν), F r := by
    apply Finset.sum_congr rfl
    intro r _
    rw [← Complex.ofReal_div]
  rw [hL]
  have hq0 : 0 < p ^ (ν - k) := pow_pos hp.pos _
  have hN2 : p ^ ν = p ^ k * p ^ (ν - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [show Finset.range (p ^ ν) = Finset.range (p ^ k * p ^ (ν - k)) from by rw [hN2],
    shiftEq_sum_range_mul (p ^ k) (p ^ (ν - k)) F hq0, Finset.sum_product]
  have hstep : (∑ j ∈ Finset.range (p ^ k), ∑ s ∈ Finset.range (p ^ (ν - k)),
        F (p ^ (ν - k) * j + s))
      = ∑ j ∈ Finset.range (p ^ k), ∑ s ∈ Finset.range (p ^ (ν - k)),
          Complex.exp (-(2 * Real.pi * Complex.I *
            (Complex.ofReal ((((a * (u : ℤ)) : ℤ) : ℝ)) *
              Complex.ofReal ((((polydiff g ((p : ℤ) ^ k * (u : ℤ))).eval ((s : ℕ) : ℤ) : ℤ) : ℝ)) /
              Complex.ofReal (((p ^ (ν - k) : ℕ) : ℝ))))) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro s _
    exact shiftEq_completeSum_term g a u p ν k hp hk j s
  rw [hstep, completeSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]

theorem sum_shift_eq (g : Polynomial ℤ) (a : ℤ) {p ν u k : ℕ} (hp : p.Prime) (hk : k < ν)
    (hu : ¬ ((p : ℤ) ∣ (u : ℤ))) :
    (∑ r ∈ Finset.range (p ^ ν), Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + ((p : ℤ) ^ k * (u : ℤ))) - g.eval (r : ℤ)) : ℤ) : ℝ) /
          (((p ^ ν : ℕ) : ℝ)))))
      = ((p : ℂ) ^ k) * Work.A3.completeSum (Work.A3.polydiff g ((p : ℤ) ^ k * (u : ℤ)))
          (a * (u : ℤ)) (p ^ (ν - k)) := by
  simpa using sum_shift_eq_general g a (u : ℤ) p ν k hp (le_of_lt hk)

end

end Work.A3
