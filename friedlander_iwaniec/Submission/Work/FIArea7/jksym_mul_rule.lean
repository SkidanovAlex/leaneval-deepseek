import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.JacTools
import Submission.Work.FIArea7.star_identity
import Submission.Work.FIArea7.chain2
import Submission.Work.FIArea7.core

/-!
# `Work.FIArea7.jksym_mul_rule` — *FI* Lemma 20.1, the Jacobi–Kubota multiplier rule

The multiplier rule (20.3)/(20.4) of Friedlander–Iwaniec,
`[wz] = ε(w,z)·[w]·[z]·(z/w)`, proved in coordinates.

The development is split over the following modules of this workspace, all of which are part of
this work:

* `Submission.Work.FIArea7.JacTools` — the tools: the negativity indicator `negI`, the Hilbert
  symbol at `∞` (17.7) and its properties (20.8)–(20.11); `χ₄`, `χ₈` as powers of `-1`;
  quadratic reciprocity (17.6) for the Jacobi symbol with *integer* numerator
  (`jacobiSym_recip_int`); the supplement (20.7) via `jacobiSym_two_pow_mul` (peeling a power
  of `2` out of the numerator); the odd part of a nonzero integer.
* `Submission.Work.FIArea7.star_identity` — **(★)**, the 2-adic core: after all the *odd* Jacobi
  symbols have been paired off by quadratic reciprocity, (20.4) reduces to a `±1`-valued
  identity depending only on `(u,v₁,r₁,s,ρ,m)` mod `8` and their signs.
* `Submission.Work.FIArea7.chain2` — `stepP2`, the pairing of the odd symbols, i.e. (★) together
  with the five reciprocity/peeling steps that produce its left-hand side.
* `Submission.Work.FIArea7.core` — `jksym_core`, the integer form of (20.4):
  `(b/|a|) = ε·(-1)^{ν'}·(v/|u|)·(s/|r|)·(a/q)`.

The final step below is the `ℂ`-bookkeeping: the powers of `i` combine because
`(a-1)/2 = (u-1)/2 + (r-1)/2 + 2ν'`.
-/

set_option autoImplicit false

namespace Work.FIArea7

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The cast to `ℂ` of an integer power of `-1` is a square root of `1`. -/
lemma negOnePow_cast_sq (k : ℤ) : (((Int.negOnePow k : ℤˣ)) : ℂ) ^ 2 = 1 := by
  have h : ((Int.negOnePow k : ℤˣ)) = 1 ∨ ((Int.negOnePow k : ℤˣ)) = -1 := by
    rcases Int.even_or_odd k with hk | hk
    · left; exact Int.negOnePow_even k hk
    · right; exact Int.negOnePow_odd k hk
  rcases h with h | h <;> rw [h] <;> norm_num

lemma neg_one_zpow (k : ℤ) : (-1 : ℂ) ^ k = ((Int.negOnePow k : ℤˣ) : ℂ) := by
  have h2 : ((-1 : ℂ)) ^ k = (-1 : ℂ) ^ k.natAbs := by
    rcases k with k | k
    · simp
    · rw [zpow_negSucc, Int.natAbs_negSucc]
      rcases Nat.even_or_odd (k + 1) with h | h
      · rw [h.neg_one_pow]; norm_num
      · rw [h.neg_one_pow]; norm_num
  rw [h2, Int.coe_negOnePow]

/-- **The `i`-power bookkeeping**: `i^{n+2k} = i^n·(-1)^k`. -/
lemma I_pow_split (n k : ℤ) :
    (Complex.I : ℂ) ^ (n + 2 * k)
      = (Complex.I : ℂ) ^ n * ((Int.negOnePow k : ℤˣ) : ℂ) := by
  have h1 : (Complex.I : ℂ) ^ (n + 2 * k)
      = (Complex.I : ℂ) ^ n * (Complex.I : ℂ) ^ (2 * k) := zpow_add₀ Complex.I_ne_zero n (2 * k)
  have h2 : (Complex.I : ℂ) ^ (2 * k) = ((Complex.I : ℂ) ^ 2) ^ k :=
    zpow_mul (Complex.I : ℂ) 2 k
  rw [h1, h2, Complex.I_sq, neg_one_zpow]

/-- ***FI* Lemma 20.1, the Jacobi–Kubota multiplier rule (20.3)/(20.4)**:

for `w` primary primitive and `z ≡ 1 (mod 2)` primitive (`Odd z.re ∧ Even z.im`, `(r,s) = 1`),

  `[wz] = ε(w,z)·[w]·[z]·(z/w)`,

where `[z] = i^{(r-1)/2}(s/|r|)` is the Jacobi–Kubota symbol (20.1) (`Work.FIArea7.JKSym`, as a
complex number), `(z/w) = ξ_w(z) = (Re(w z) | |w|²)` is the Dirichlet symbol of §19
(`Work.FIArea7.DirichletSym`; `Re(wz) = ur − vs` for `w = u+iv`, `z = r+is`), and `ε = ε(w,z)`
is the quadrant sign of (20.5)/(20.6), `Work.FIArea7.MultEps`:

  `ε = (u,v)_∞(r,−v)_∞` if `ur > vs`,   `ε = (u,v)_∞(−r,v)_∞` if `ur < vs`,

with `(x,y)_∞` the Hilbert symbol at ∞ (17.7) `= −1` iff `x < 0 ∧ y < 0`
(`Work.FIArea7.HilbertInf`).  The two cases are exhaustive since `ur − vs = Re(wz)` is odd.

In coordinates this is exactly (20.4),
`i^{(a-1)/2}(b/|a|) = ε·i^{(u-1)/2}(v/|u|)·i^{(r-1)/2}(s/|r|)·((ur−vs)/(u²+v²))`
with `wz = a + ib`, `a = ur − vs`, `b = us + vr` — i.e. the identity of the statement after
unfolding `JKSym`, `JKCoeff`, `DirichletSym`.  All moduli occurring are odd, so Mathlib's
`jacobiSym` is the genuine Jacobi symbol and the source's convention (8.15) is respected.

(The source's proof: quadratic reciprocity (17.6), its supplement (20.7) for `(2/·)`, and the
Hilbert-symbol identities (20.8)–(20.11).  In the vanishing case `(u,v) ≠ 1` or `(r,s) ≠ 1` both
sides are `0`, so the two coprimality hypotheses are not actually load-bearing — but they are the
source's own primitivity hypotheses, they hold in every application of §§21–23, and they make the
statement easier to prove.)

Hypotheses are satisfiable, e.g. `w = 3 + 2i`, `z = 1 + 2i`.  Verified exhaustively in Python
(primary primitive `w` and primitive `z ≡ 1 (mod 2)` with coordinates in `[-12,12]`, 7938 cases;
and with `[-16,16]` without the coprimality hypotheses): no counterexample. -/
theorem jksym_mul_rule {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hz : Odd z.re ∧ Even z.im)
    (hpw : IsCoprime w.re w.im) (hpz : IsCoprime z.re z.im) :
    Work.FIArea7.JKSym (w * z)
      = (Work.FIArea7.MultEps w z : ℂ) * Work.FIArea7.JKSym w * Work.FIArea7.JKSym z
        * (Work.FIArea7.DirichletSym w z : ℂ) := by
  obtain ⟨hu, hv, hv4⟩ := hw
  obtain ⟨hr, hs⟩ := hz
  have hq : Work.FIPlan.gnorm w = (w.re ^ 2 + w.im ^ 2).natAbs := by
    have h2 : ((w.re ^ 2 + w.im ^ 2).natAbs : ℤ) = w.re ^ 2 + w.im ^ 2 :=
      Int.natAbs_of_nonneg (by positivity)
    have h := norm_eq w
    rw [← h2] at h
    exact_mod_cast h
  by_cases hv0 : w.im = 0
  · -- degenerate case: w = 1
    have h1 : w.re.natAbs = 1 := by
      have h := Int.isCoprime_iff_gcd_eq_one.mp hpw
      rw [hv0, Int.gcd_eq_natAbs] at h
      simpa using h
    have h2 : w.re = 1 ∨ w.re = -1 := by
      rcases Int.natAbs_eq w.re with h3 | h3
      · left; rw [h3]; exact_mod_cast h1
      · right; rw [h3]
        have h4 : (w.re.natAbs : ℤ) = 1 := by exact_mod_cast h1
        rw [h4]
    have h3 : w.re = 1 := by
      rcases h2 with h2 | h2
      · exact h2
      · exfalso
        rw [hv0, h2] at hv4
        have hd : (4 : ℤ) ∣ (-1 - 1) - 0 := Int.modEq_iff_dvd.mp hv4
        omega
    have hw1 : w = 1 := Zsqrtd.ext h3 (by rw [hv0]; rfl)
    subst hw1
    simp only [JKSym, JKCoeff, DirichletSym, MultEps, HilbertInf, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.reduceNeg, mul_zero, lt_self_iff_false, not_false_eq_true, if_false, mul_one,
      Zsqrtd.re_mul, Zsqrtd.im_mul, one_mul, zero_mul, sub_zero, Int.reduceSub,
      show Work.FIPlan.gnorm 1 = 1 from by
        rw [Work.FIPlan.gnorm, Zsqrtd.norm_one]; rfl]
    rw [jacobiSym.one_right]
    norm_num
  · -- main case
    have hc := jksym_core hu hv hr hs hpw hpz hv0
    rw [JKSym, JKSym, JKSym, JKCoeff, JKCoeff, JKCoeff, DirichletSym, re_mul, im_mul, hq]
    obtain ⟨U, hU⟩ : ∃ U : ℤ, w.re = 2 * U + 1 := hu
    obtain ⟨R, hR⟩ : ∃ R : ℤ, z.re = 2 * R + 1 := hr
    obtain ⟨Vm, hVm⟩ := hv
    have hVm2 : w.im = 2 * Vm := by rw [hVm]; ring
    obtain ⟨Sm, hSm⟩ := hs
    have hSm2 : z.im = 2 * Sm := by rw [hSm]; ring
    have hexp : (w.re * z.re - w.im * z.im - 1) / 2
        = (w.re - 1) / 2 + (z.re - 1) / 2
          + 2 * (((w.re - 1) * (z.re - 1) - w.im * z.im) / 4) := by
      rw [hU, hR, hVm2, hSm2,
        show (2 * U + 1 - 1) / 2 = U by omega,
        show (2 * R + 1 - 1) / 2 = R by omega,
        show ((2 * U + 1) * (2 * R + 1) - 2 * Vm * (2 * Sm) - 1) / 2
            = U + R + 2 * (U * R - Vm * Sm) by
          rw [show (2 * U + 1) * (2 * R + 1) - 2 * Vm * (2 * Sm) - 1
              = 2 * (U + R + 2 * (U * R - Vm * Sm)) by ring,
            Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)],
        show ((2 * U + 1 - 1) * (2 * R + 1 - 1) - 2 * Vm * (2 * Sm)) / 4
            = U * R - Vm * Sm by
          rw [show (2 * U + 1 - 1) * (2 * R + 1 - 1) - 2 * Vm * (2 * Sm)
              = 4 * (U * R - Vm * Sm) by ring,
            Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]]
    have hI : (Complex.I : ℂ) ^ ((w.re * z.re - w.im * z.im - 1) / 2)
        = (Complex.I : ℂ) ^ ((w.re - 1) / 2) * (Complex.I : ℂ) ^ ((z.re - 1) / 2)
          * ((Int.negOnePow (((w.re - 1) * (z.re - 1) - w.im * z.im) / 4) : ℤˣ) : ℂ) := by
      rw [hexp, I_pow_split ((w.re - 1) / 2 + (z.re - 1) / 2)
        (((w.re - 1) * (z.re - 1) - w.im * z.im) / 4), zpow_add₀ Complex.I_ne_zero]
    have hJ : (jacobiSym (w.re * z.im + w.im * z.re) (w.re * z.re - w.im * z.im).natAbs : ℂ)
        = ((MultEps w z : ℤ) : ℂ)
          * ((Int.negOnePow (((w.re - 1) * (z.re - 1) - w.im * z.im) / 4) : ℤˣ) : ℂ)
          * (jacobiSym w.im w.re.natAbs : ℂ) * (jacobiSym z.im z.re.natAbs : ℂ)
          * (jacobiSym (w.re * z.re - w.im * z.im) (w.re ^ 2 + w.im ^ 2).natAbs : ℂ) := by
      rw [hc]; push_cast; ring
    rw [hI, hJ]
    ring_nf
    rw [negOnePow_cast_sq ((1 - w.re + w.re * z.re - z.re - w.im * z.im) / 4)]
    ring

end

end Work.FIArea7
