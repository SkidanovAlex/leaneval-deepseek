import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.coprime_pairR_oddPart_m
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup

/-!
# The termwise flip identity of the far part (FI §12)

This module proves `farU_conjV_termwise`: the *pointwise* rearrangement of a single summand of
the flipped exponential sum.  Reading the summand of `pairSumCo (cR c R) S (m q')` for the pair
`(ρ₁,s₁)`, `(ρ₂,s₂)` of reduced moduli, the identity rewrites

`(c/q'D)^{it} · farU_{ρ₁s₁} · conj(farV_{ρ₂s₂}) · (ρ₁|(mq')')(ρ₂|(mq')')`

into the form in which the variance/large-sieve step of the paper sees it:

`(s₁|ρ₁)(s₂|ρ₂) · α_{cρ₁s₁} conj(α_{cρ₂s₂}) · (ρ₁|q')(ρ₂|q') · e(u x) · y^{it}`

with the separation arguments `x = xOrig c i` (`= s₁/cρ₁ - s₂/cρ₂`) and `y = ySep c D i`
(`= cρ₁ρ₂/q'D`).  Three independent ingredients are combined:

* the Jacobi reciprocity of the *odd parts*, `(ρ|m')(ρ|(mq)') = (ρ|q')`, which holds because
  the hypotheses force `(ρ, m) = 1`;
* the multiplicativity of the complex power over nonnegative real bases,
  `(c/q'D)^{it} ρ₁^{it} ρ₂^{it} = (c ρ₁ ρ₂/q'D)^{it}`;
* the additivity of the exponential, `e(u s₁/cρ₁) e(-u s₂/cρ₂) = e(u x)`.

The coprimality `(ρᵢ, m) = 1` needed for the Jacobi step is supplied by
`coprime_pairR_oddPart_m` (the reduced moduli `ρᵢ` are the reduced parts `pairR` of `c ρᵢ`).
-/

namespace Work.FIArea4.Vflip.Vfd

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary complex-analytic rewritings -/

/-- Complex conjugation commutes with the exponential. -/
private lemma star_exp' (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [show star (Complex.exp z) = (starRingEnd ℂ) (Complex.exp z) from rfl]
  exact (Complex.exp_conj z).symm

/-- Conjugation of a complex power with nonnegative real base: `conj (r^w) = r^{conj w}`. -/
private lemma star_cpow_ofReal' {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    star ((r:ℂ)^w) = (r:ℂ)^(star w) := by
  have hx : ((r:ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (r:ℂ) w hx
  rw [Complex.star_def]
  simp only [Complex.conj_ofReal] at h
  exact h.symm

/-- The complex power is multiplicative over a quotient of nonnegative real bases. -/
private lemma div_cpow_natCast (a b : ℕ) (w : ℂ) :
    (((a:ℕ):ℂ) / ((b:ℕ):ℂ))^w = ((a:ℕ):ℂ)^w / ((b:ℕ):ℂ)^w := by
  rw [show ((a:ℕ):ℂ) = ((a:ℝ):ℂ) from (Complex.ofReal_natCast a).symm,
      show ((b:ℕ):ℂ) = ((b:ℝ):ℂ) from (Complex.ofReal_natCast b).symm]
  exact Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) w

/-- The complex power is multiplicative over a product of nonnegative real bases. -/
private lemma mul_cpow_natCast (a b : ℕ) (w : ℂ) :
    (((a:ℕ):ℂ))^w * (((b:ℕ):ℂ))^w = (((a*b:ℕ)):ℂ)^w := by
  rw [show ((a:ℕ):ℂ) = ((a:ℝ):ℂ) from (Complex.ofReal_natCast a).symm,
      show ((b:ℕ):ℂ) = ((b:ℝ):ℂ) from (Complex.ofReal_natCast b).symm,
      show (((a*b:ℕ)):ℂ) = (((a*b:ℕ):ℝ):ℂ) from (Complex.ofReal_natCast (a*b)).symm,
      ← Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) w]
  congr 1; push_cast; ring

/-- The conjugate of the companion array `farV`: every factor with a conjugate is expanded, the
Jacobi weights being real, and the conjugate of the power `ρ^{-it}` is `ρ^{it}`. -/
private lemma star_farV (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (ρ2 s2 : ℕ) :
    star (farV m c α u t ρ2 s2)
    = star (α (c*ρ2) s2) * ((jacobiSym (s2:ℤ) ρ2 : ℤ):ℂ) * Work.FIArea4.jw m ρ2
      * Complex.exp (-(2*Real.pi*Complex.I*(u*((s2:ℝ)/((c*ρ2:ℕ):ℝ)))))
      * ((((ρ2:ℕ):ℝ):ℂ)^(Complex.I*(t:ℂ))) := by
  rw [farV]
  simp only [Complex.star_def, map_mul]
  simp only [starRingEnd_apply]
  rw [star_intCast, Work.FIArea4.star_jw, star_exp', star_cpow_ofReal' (Nat.cast_nonneg ρ2)]
  rw [show star (2*Real.pi*Complex.I*(u*((s2:ℝ)/((c*ρ2:ℕ):ℝ))))
        = -(2*Real.pi*Complex.I*(u*((s2:ℝ)/((c*ρ2:ℕ):ℝ)))) from by
        simp only [Complex.star_def, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
          map_div₀]
        ring,
      show star (-(Complex.I*(t:ℂ))) = Complex.I*(t:ℂ) from by
        simp only [Complex.star_def, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring]

/-! ## The termwise identity -/

theorem farU_conjV_termwise {c D m q' : ℕ} {α : ℕ → ℕ → ℂ} {u t : ℝ} {ρ1 s1 ρ2 s2 : ℕ}
    (hc : 1 ≤ c) (hm : 1 ≤ m) (hD : 1 ≤ D) (hq' : 1 ≤ q')
    (hρ1 : 0 < ρ1) (hρ2 : 0 < ρ2)
    (hcop1 : Nat.Coprime (c*ρ1) (2*s1)) (hcop2 : Nat.Coprime (c*ρ2) (2*s2))
    (hmc : m ∣ c) (hgcd : Nat.Coprime ρ1 ρ2)
    (hdiv : m*q' ∣ Work.FIArea4.Vflip.pairAbs (c*ρ1) (c*ρ2) s1 s2) :
    (((c:ℕ):ℂ) / (((q'*D:ℕ)):ℂ))^(Complex.I*(t:ℂ)) *
        Work.FIArea4.Vflip.Vfd.farU m c α u t ρ1 s1 * star (Work.FIArea4.Vflip.Vfd.farV m c α u t ρ2 s2) *
        ((jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart (m*q')) *
          jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart (m*q')) : ℤ) : ℂ)
      = ((jacobiSym (s1:ℤ) ρ1 * jacobiSym (s2:ℤ) ρ2 : ℤ) : ℂ) *
        (α (c*ρ1) s1 * star (α (c*ρ2) s2)) *
        ((jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q') *
          jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q') : ℤ) : ℂ) *
        Complex.exp (2*Real.pi*Complex.I*(u * Work.FIArea4.Vflip.Vfd.xOrig c ((q',(ρ1,s1)),(ρ2,s2)))) *
        (((Work.FIArea4.Vflip.Vfd.ySep c D ((q',(ρ1,s1)),(ρ2,s2)) : ℝ)) : ℂ)^(Complex.I*(t:ℂ)) := by
  have hcpos : 0 < c := by omega
  have hmne : m ≠ 0 := by omega
  have hq'ne : q' ≠ 0 := by omega
  -- `ρᵢ` are the reduced moduli `pairR` of the pair `(cρ₁, cρ₂)`
  have hC : Work.FIArea4.Vflip.pairC (c*ρ1) (c*ρ2) = c := by
    rw [Work.FIArea4.Vflip.pairC, Nat.gcd_mul_left, hgcd.gcd_eq_one, mul_one]
  have hR1 : Work.FIArea4.Vflip.pairR (c*ρ1) (c*ρ2) = ρ1 := by
    rw [Work.FIArea4.Vflip.pairR, hC, Nat.mul_div_cancel_left ρ1 hcpos]
  have hR2 : Work.FIArea4.Vflip.pairR (c*ρ2) (c*ρ1) = ρ2 := by
    rw [Work.FIArea4.Vflip.pairR, show Work.FIArea4.Vflip.pairC (c*ρ2) (c*ρ1) = c by
          rw [Work.FIArea4.Vflip.pairC, Nat.gcd_comm, Nat.gcd_mul_left, hgcd.gcd_eq_one, mul_one],
      Nat.mul_div_cancel_left ρ2 hcpos]
  -- coprimality of the reduced moduli with the odd part of `m`
  have hpair := coprime_pairR_oddPart_m (r1 := c*ρ1) (r2 := c*ρ2)
      (Nat.mul_pos hcpos hρ1) (Nat.mul_pos hcpos hρ2) hcop1 hcop2 (by rwa [hC]) hdiv
  rw [hR1, hR2] at hpair
  -- the Jacobi reciprocity of the odd parts
  have hJ1int : jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart (m*q'))
      = jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q') := by
    have hmul : Work.FIPlan.oddPart (m*q') = Work.FIPlan.oddPart m * Work.FIPlan.oddPart q' :=
      Nat.ordCompl_mul m q' 2
    have hm0 : Work.FIPlan.oddPart m ≠ 0 := (Work.FIArea4.oddPart_pos hmne).ne'
    have hq0 : Work.FIPlan.oddPart q' ≠ 0 := (Work.FIArea4.oddPart_pos hq'ne).ne'
    have hsq : jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m)^2 = 1 := by
      apply jacobiSym.sq_one
      rw [Int.gcd_natCast_natCast]; exact hpair.1.gcd_eq_one
    calc jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart (m*q'))
        = jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m)
            * (jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q')) := by
          rw [hmul, jacobiSym.mul_right' (ρ1:ℤ) hm0 hq0]
      _ = jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart m)^2 * jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q') := by ring
      _ = jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q') := by rw [hsq]; ring
  have hJ2int : jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart (m*q'))
      = jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q') := by
    have hmul : Work.FIPlan.oddPart (m*q') = Work.FIPlan.oddPart m * Work.FIPlan.oddPart q' :=
      Nat.ordCompl_mul m q' 2
    have hm0 : Work.FIPlan.oddPart m ≠ 0 := (Work.FIArea4.oddPart_pos hmne).ne'
    have hq0 : Work.FIPlan.oddPart q' ≠ 0 := (Work.FIArea4.oddPart_pos hq'ne).ne'
    have hsq : jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m)^2 = 1 := by
      apply jacobiSym.sq_one
      rw [Int.gcd_natCast_natCast]; exact hpair.2.gcd_eq_one
    calc jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart (m*q'))
        = jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m)
            * (jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m) * jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q')) := by
          rw [hmul, jacobiSym.mul_right' (ρ2:ℤ) hm0 hq0]
      _ = jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart m)^2 * jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q') := by ring
      _ = jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q') := by rw [hsq]; ring
  have hJ1 : Work.FIArea4.jw m ρ1 * ((jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart (m*q')) : ℤ):ℂ)
      = ((jacobiSym (ρ1:ℤ) (Work.FIPlan.oddPart q') : ℤ):ℂ) := by
    rw [Work.FIArea4.jw, ← Int.cast_mul, hJ1int]
  have hJ2 : Work.FIArea4.jw m ρ2 * ((jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart (m*q')) : ℤ):ℂ)
      = ((jacobiSym (ρ2:ℤ) (Work.FIPlan.oddPart q') : ℤ):ℂ) := by
    rw [Work.FIArea4.jw, ← Int.cast_mul, hJ2int]
  -- the multiplicativity of the complex power
  have hPow : (((c:ℕ):ℂ) / ((q'*D:ℕ):ℂ))^(Complex.I*(t:ℂ))
      * ((((ρ1:ℕ):ℝ):ℂ))^(Complex.I*(t:ℂ)) * ((((ρ2:ℕ):ℝ):ℂ))^(Complex.I*(t:ℂ))
      = ((Work.FIArea4.Vflip.Vfd.ySep c D ((q',(ρ1,s1)),(ρ2,s2)) : ℝ) : ℂ)^(Complex.I*(t:ℂ)) := by
    have hy : (Work.FIArea4.Vflip.Vfd.ySep c D ((q',(ρ1,s1)),(ρ2,s2)) : ℂ)
        = ((c*ρ1*ρ2:ℕ):ℂ)/((q'*D:ℕ):ℂ) := by
      unfold Work.FIArea4.Vflip.Vfd.ySep; push_cast; ring
    rw [hy, div_cpow_natCast (c*ρ1*ρ2) (q'*D) (Complex.I*(t:ℂ))]
    rw [← mul_cpow_natCast (c*ρ1) ρ2 (Complex.I*(t:ℂ)),
        ← mul_cpow_natCast c ρ1 (Complex.I*(t:ℂ))]
    rw [div_cpow_natCast c (q'*D) (Complex.I*(t:ℂ))]
    rw [show (((ρ1:ℕ):ℝ):ℂ) = ((ρ1:ℕ):ℂ) from Complex.ofReal_natCast ρ1,
        show (((ρ2:ℕ):ℝ):ℂ) = ((ρ2:ℕ):ℂ) from Complex.ofReal_natCast ρ2]
    ring
  -- the additivity of the exponential
  have hExp : (Complex.exp (2*Real.pi*Complex.I*(u * ((s1:ℝ)/((c*ρ1:ℕ):ℝ)))))
      * (Complex.exp (-(2*Real.pi*Complex.I*(u * ((s2:ℝ)/((c*ρ2:ℕ):ℝ))))))
      = Complex.exp (2*Real.pi*Complex.I*(u * Work.FIArea4.Vflip.Vfd.xOrig c ((q',(ρ1,s1)),(ρ2,s2)))) := by
    rw [← Complex.exp_add]
    congr 1
    unfold Work.FIArea4.Vflip.Vfd.xOrig Work.FIArea4.Vflip.xPair
    push_cast
    ring
  rw [Work.FIArea4.Vflip.Vfd.farU, star_farV m c α u t ρ2 s2]
  simp only [Int.cast_mul]
  rw [← hJ1, ← hJ2, ← hPow, ← hExp]
  ring

end

end Work.FIArea4.Vflip.Vfd
