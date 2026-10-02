/-
# TripodCert — the data of the uniqueness certificate

Area `Submission/Work/TripodCert/`.  The proof of TRI (the landing point of the `22/63`-ray is
fixed by `Tsq c`) reduces to the uniqueness of the zero of `h = (Tsq c)^[3] - id` on the closed
disc `UDisc = closedBall z₀ R`:

* the landing point `y` of the `22/63`-ray and the landing point `Tsq c y` of the `25/63`-ray
  both lie in `UDisc` (`Chain.lean` + the emitted containment checks), and both are fixed by
  `(Tsq c)^[3]`;
* if `Re (deriv h) > 0` on `UDisc`, then `h` is injective there, so the two fixed points agree.

This module supplies the *numerical* side of the second bullet: the rational constants of the
certificate, the explicit exact computation of `Re P₀` (where `P₀ = deriv ((Tsq c₀)^[3]) z₀` is
the product of the three derivatives along the orbit of `z₀` at the centre `c₀` of the parameter
box), and the elementary numerical facts (radii, drift, containment) the estimate chain needs.
The proof of the estimate chain itself is in `DerivBound.lean`.
-/
import Mathlib
import Submission.Work.TripodCert.Data
import Submission.Work.TripodCert.Num2
import Submission.Work.TripodCert.Check2
import Submission.Work.TripodCert.Sound
import Submission.Work.TripodCert.inUBall_sound
import Submission.Work.TripodCert.norm_Tsq_sub_le
import Submission.Work.SeedCertRay.norm_sub_center_le
import Submission.Work.SeedDyn.deriv_Tsq_ne_zero
import Submission.Work.TripodCert.deriv_tsq_three

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Explicit rational complex arithmetic -/

/-- Multiplication of the explicit complex numbers represented by rational pairs. -/
def mul2 (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Addition of the explicit complex numbers represented by rational pairs. -/
def add2 (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 + b.1, a.2 + b.2)

/-- Subtraction. -/
def sub2 (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 - b.1, a.2 - b.2)

/-- Complex conjugation of the pair: negation of the imaginary part. -/
def conj2 (a : ℚ × ℚ) : ℚ × ℚ := (a.1, -a.2)

/-- The negative of the pair. -/
def neg2 (a : ℚ × ℚ) : ℚ × ℚ := (-a.1, -a.2)

/-- The complex number represented by a rational pair. -/
def toC (a : ℚ × ℚ) : ℂ := (((a.1 : ℚ) : ℝ) : ℂ) + (((a.2 : ℚ) : ℝ) : ℂ) * Complex.I

/-- `Tsq` in pair coordinates. -/
def Tsq2 (c z : ℚ × ℚ) : ℚ × ℚ :=
  add2 (mul2 (add2 (mul2 z z) (conj2 c)) (add2 (mul2 z z) (conj2 c))) c

/-- `deriv (Tsq c) z = 4 z (z² + c̄)` in pair coordinates. -/
def dTsq2 (c z : ℚ × ℚ) : ℚ × ℚ :=
  mul2 (mul2 (2, 0) (2, 0)) (mul2 z (add2 (mul2 z z) (conj2 c)))

/-- The centre of the parameter box, as a rational pair. -/
def c0p : ℚ × ℚ := (Q PXM, Q PYM)

/-- The centre of the uniqueness disc, as a rational pair. -/
def z0p : ℚ × ℚ := (Q Uzx, Q Uzy)

/-- The product of the three derivatives along the orbit of `z₀`, in pair coordinates. -/
def P0p : ℚ × ℚ :=
  mul2 (mul2 (dTsq2 c0p (Tsq2 c0p (Tsq2 c0p z0p))) (dTsq2 c0p (Tsq2 c0p z0p))) (dTsq2 c0p z0p)

/-- A norm bound is equivalent to a bound on the sum of the squares of the coordinates. -/
theorem norm_le_iff_sq_le {a : ℚ × ℚ} {r : ℚ} (hr : 0 ≤ r) :
    ‖toC a‖ ≤ (r : ℝ) ↔ a.1 ^ 2 + a.2 ^ 2 ≤ r ^ 2 := by
  have h2 : ‖toC a‖ ^ 2 = ((a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2) := by
    rw [Complex.sq_norm]
    simp only [toC, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, sub_zero]
    ring
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  constructor
  · intro h
    have h3 : ‖toC a‖ ^ 2 ≤ (r : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (toC a), h]
    rw [h2] at h3
    exact_mod_cast h3
  · intro h
    have h3 : ((a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2) ≤ (r : ℝ) ^ 2 := by exact_mod_cast h
    have h4 : ‖toC a‖ ^ 2 ≤ (r : ℝ) ^ 2 := by rw [h2]; exact h3
    nlinarith [norm_nonneg (toC a), h4, hrR]

/-! ## The bridges to `ℂ` -/

theorem toC_mul2 (a b : ℚ × ℚ) : toC (mul2 a b) = toC a * toC b := by
  apply Complex.ext <;>
    simp only [toC, mul2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, sub_zero] <;> push_cast <;> ring

theorem toC_add2 (a b : ℚ × ℚ) : toC (add2 a b) = toC a + toC b := by
  apply Complex.ext <;>
    simp only [toC, add2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, sub_zero] <;> push_cast <;> ring

theorem toC_sub2 (a b : ℚ × ℚ) : toC (sub2 a b) = toC a - toC b := by
  apply Complex.ext <;>
    simp only [toC, sub2, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, sub_zero] <;> push_cast <;> ring

theorem toC_neg2 (a : ℚ × ℚ) : toC (neg2 a) = -toC a := by
  apply Complex.ext <;>
    simp only [toC, neg2, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, sub_zero] <;> push_cast <;> ring

theorem star_toC (a : ℚ × ℚ) : star (toC a) = toC (conj2 a) := by
  have h : star (toC a) = conj (toC a) := rfl
  rw [h]
  apply Complex.ext <;> simp only [toC, conj2, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_add, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, sub_zero] <;> push_cast <;> ring

/-- The conjugation bridge, in the direction used by the rewrites. -/
theorem toC_conj2 (a : ℚ × ℚ) : toC (conj2 a) = star (toC a) := (star_toC a).symm

theorem toC_Tsq2 (c z : ℚ × ℚ) :
    toC (Tsq2 c z) = Work.Landing.Tsq (toC c) (toC z) := by
  simp only [Tsq2, toC_add2, toC_mul2, Work.Landing.Tsq, star_toC]
  ring

theorem toC_two_two : toC ((2, 0) : ℚ × ℚ) * toC ((2, 0) : ℚ × ℚ) = (4 : ℂ) := by
  norm_num [toC]

theorem toC_dTsq2 (c z : ℚ × ℚ) :
    toC (dTsq2 c z) = deriv (Work.Landing.Tsq (toC c)) (toC z) := by
  rw [Work.SeedDyn.deriv_Tsq_eq]
  simp only [dTsq2, toC_mul2, toC_add2, star_toC]
  rw [toC_two_two]
  ring

theorem toC_c0p : toC c0p = c0T := rfl

theorem toC_z0p : toC z0p = uZ0 := rfl

/-- The product `P₀` computed in pair coordinates, as a complex number. -/
theorem toC_P0p : toC P0p
    = deriv ((Work.Landing.Tsq (toC c0p))^[3]) (toC z0p) := by
  rw [Work.TripodCert.deriv_tsq_three]
  simp only [P0p, toC_mul2, toC_dTsq2, toC_Tsq2, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

/-! ## The rational constants of the certificate -/

/-- The radius of the uniqueness disc, in mantissas, as a rational. -/
def uRUq : ℚ := Q URmU

/-- The radius of the uniqueness disc, as a real number. -/
def uRUr : ℝ := (uRUq : ℝ)

/-- A bound for `‖z‖` on the uniqueness disc. -/
def UMq : ℚ := 13 / 10

/-- A bound for `‖z₀² + c̄₀‖`. -/
def US0q : ℚ := 2 / 5

/-- A bound for `‖c‖` on the parameter box. -/
def UCmq : ℚ := 6 / 5

/-- A bound for `‖Tsq c₀ z₀ - z₀‖`. -/
def Ud0q : ℚ := 1 / 20000

/-- The radius of the disc on which the three orbit points are located. -/
def UREq : ℚ := 1 / 20

/-- The radius bound of the parameter box. -/
def UDcq : ℚ := Q RADM

/-- The factor `‖z‖ + ‖z₀‖`. -/
def UN0q : ℚ := 2 * UMq

/-- The factor `‖z‖² + ‖z₀‖² + 2‖c‖` of the `Tsq`-difference estimate. -/
def UN1q : ℚ := 2 * UMq * UMq + 2 * UCmq

/-- The `Tsq`-difference bound on the uniqueness disc. -/
def Ur1q : ℚ := uRUq * UN0q * UN1q

/-- The drift bound `‖Tsq c z₀ - z₀‖`. -/
def Ur0q : ℚ := Ud0q + (2 * UMq * UMq + 2 * UCmq + 1) * UDcq

/-- A bound for `‖deriv (Tsq c) w‖` on the disc of radius `UREq`. -/
def ULq : ℚ := 4 * UMq * (US0q + UDcq + 2 * UMq * UREq)

/-- A Lipschitz bound for `deriv (Tsq c)` on the disc of radius `UREq`. -/
def UKq : ℚ := 4 * (3 * UMq * UMq + UCmq)

/-- The variation of `deriv (Tsq c)` under a change of the parameter. -/
def Uβq : ℚ := 4 * UMq * UDcq

/-- **The total variation bound `δ` of the derivative product.** -/
def Uδq : ℚ := UKq * ULq * ULq * (ULq * Ur1q + Ur1q + uRUq) + 3 * Uβq * ULq * ULq

/-! ## The numerical certificate -/

/-- **The exact evaluation of `Re P₀`.**  The product of the three derivatives along the orbit of
`z₀` at the centre `c₀` of the parameter box has real part at least `3/2 + δ`, where `δ` is the
variation bound of `Uδq`. -/
theorem certP0 : (3 / 2 + Uδq : ℚ) ≤ P0p.1 := by
  norm_num [P0p, dTsq2, Tsq2, mul2, add2, conj2, c0p, z0p, Q, MS, PXM, PYM, Uzx, Uzy, Uδq,
    UKq, ULq, Uβq, Ur1q, Ur0q, UN0q, UN1q, UMq, US0q, UCmq, Ud0q, UREq, UDcq, uRUq, URmU, RADM]

/-- The certificate in the form used by the estimate chain: the real part of the derivative
product at `(c₀, z₀)` dominates `3/2 + δ`. -/
theorem certP0_re : 3 / 2 + (Uδq : ℝ) ≤ (deriv ((Work.Landing.Tsq c0T)^[3]) uZ0).re := by
  have h := certP0
  have h1 : ((3 / 2 + Uδq : ℚ) : ℝ) ≤ ((P0p.1 : ℚ) : ℝ) := by exact_mod_cast h
  have h2 : ((P0p.1 : ℚ) : ℝ) = (toC P0p).re := by
    simp [toC, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h2, toC_P0p, toC_c0p, toC_z0p] at h1
  rw [show ((3 / 2 + Uδq : ℚ) : ℝ) = 3 / 2 + ((Uδq : ℚ) : ℝ) by push_cast; ring] at h1
  exact h1

/-- The norm bound of `z₀`, strong enough for both the disc `D` and the disc `E`. -/
theorem hUM0 : ‖uZ0‖ ≤ ((UMq - UREq : ℚ) : ℝ) := by
  have hr : (0 : ℚ) ≤ UMq - UREq := by norm_num [UMq, UREq]
  rw [← toC_z0p]
  refine (norm_le_iff_sq_le hr).mpr ?_
  norm_num [toC, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, sub_zero, z0p, Q, MS, UMq, UREq, Uzx, Uzy]

/-- The norm bound of `z₀` on the uniqueness disc. -/
theorem hUMz : ‖uZ0‖ + (uRUq : ℝ) ≤ (UMq : ℝ) := by
  have h1 := hUM0
  have h2 : (uRUq : ℝ) ≤ (UREq : ℝ) := by norm_num [uRUq, UREq, URmU, Q, MS]
  push_cast at h1
  linarith

/-- The norm bound of `z₀` and of the disc of radius `UREq` around it. -/
theorem hUMe : ‖uZ0‖ + (UREq : ℝ) ≤ (UMq : ℝ) := by
  have h1 := hUM0
  push_cast at h1
  linarith

/-- The numerical bound `‖z₀² + c̄₀‖ ≤ 2/5`. -/
theorem hUS0 : ‖uZ0 ^ 2 + star c0T‖ ≤ (US0q : ℝ) := by
  have hr : (0 : ℚ) ≤ US0q := by norm_num [US0q]
  rw [← toC_z0p, ← toC_c0p, pow_two, ← toC_mul2, ← toC_conj2, ← toC_add2]
  refine (norm_le_iff_sq_le hr).mpr ?_
  norm_num [toC, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, sub_zero, mul2, add2, conj2, z0p, c0p, Q, MS, US0q, Uzx, Uzy, PXM, PYM]

/-- The numerical drift bound `‖Tsq c₀ z₀ - z₀‖ ≤ 1/20000`. -/
theorem hUd0 : ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ ≤ (Ud0q : ℝ) := by
  have hr : (0 : ℚ) ≤ Ud0q := by norm_num [Ud0q]
  rw [← toC_z0p, ← toC_c0p, ← toC_Tsq2, ← toC_sub2]
  refine (norm_le_iff_sq_le hr).mpr ?_
  norm_num [toC, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, sub_zero, Tsq2, sub2, mul2, add2, conj2, z0p, c0p, Q, MS, Ud0q, Uzx, Uzy,
    PXM, PYM]

/-- The numerical bound `‖c₀‖ + rad X ≤ 6/5`. -/
theorem hUc0 : ‖c0T‖ + (UDcq : ℝ) ≤ (UCmq : ℝ) := by
  have hr : (0 : ℚ) ≤ UCmq - UDcq := by norm_num [UCmq, UDcq, Q, MS, RADM]
  have h1 : ‖c0T‖ ≤ ((UCmq - UDcq : ℚ) : ℝ) := by
    rw [← toC_c0p]
    refine (norm_le_iff_sq_le hr).mpr ?_
    norm_num [toC, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, add_zero, sub_zero, c0p, Q, MS, UCmq, UDcq, RADM, PXM, PYM]
  push_cast at h1
  linarith

/-- The parameter box is contained in the disc of radius `UDcq` about its centre. -/
theorem hDc {c : ℂ} (hc : Xb.mem c) : ‖c - c0T‖ ≤ (UDcq : ℝ) := by
  have h := Work.SeedCertRay.norm_sub_center_le Xb hc
  have h1 : Xb.center = c0T := by
    apply Complex.ext
    · rw [Xb_center_re]
      simp [c0T, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    · rw [Xb_center_im]
      simp [c0T, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
  have h2 : ((Xb.rad : ℚ) : ℝ) = (UDcq : ℝ) := by rw [Xb_rad]; rfl
  simpa [h1, h2] using h

/-- The parameter box bound `‖c‖ ≤ 6/5`. -/
theorem hUCm {c : ℂ} (hc : Xb.mem c) : ‖c‖ ≤ (UCmq : ℝ) := by
  have h1 := hDc hc
  have h2 := hUc0
  have h3 : ‖c‖ ≤ ‖c0T‖ + ‖c - c0T‖ := by
    calc ‖c‖ = ‖c0T + (c - c0T)‖ := by ring_nf
      _ ≤ ‖c0T‖ + ‖c - c0T‖ := norm_add_le _ _
  linarith

/-- The containment `Tsq (D) ⊆ E`. -/
theorem hUr1 : Ur1q + Ur0q ≤ UREq := by
  norm_num [Ur1q, Ur0q, UN0q, UN1q, uRUq, UMq, UCmq, Ud0q, UDcq, UREq, Q, MS, RADM, URmU]

/-- The containment `Tsq (E) ⊆ E`. -/
theorem hUr1E : (Ur1q + Ur0q) * UN0q * UN1q + Ur0q ≤ UREq := by
  norm_num [Ur1q, Ur0q, UN0q, UN1q, uRUq, UMq, UCmq, Ud0q, UDcq, UREq, Q, MS, RADM, URmU]

end Work.TripodCert
