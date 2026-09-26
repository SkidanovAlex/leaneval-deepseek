import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

set_option maxHeartbeats 800000

/-!
## Summability of the `E₈` theta series

The theta series summand is `thetaTerm τ x = exp (π i τ ‖x‖ ^ 2)`, whose modulus is
`exp (-π (im τ) ‖x‖ ^ 2)`.  Since `τ.im > 0` this decays as a Gaussian, and because every
vector of `E₈` has coordinates that are half-integers (i.e. `2 • x ∈ ℤ⁸`), the sum over
`E₈` is dominated by the Gaussian sum over `ℤ⁸`, which factors as a product of
one-dimensional Gaussian sums over `ℤ`.

This file proves those Gaussian summability statements (over `ℤ`, and over the finite
product `Fin n → ℤ`) and then concludes the summability of the `E₈` theta series.
-/

/-- The one-dimensional Gaussian sum `∑_{n : ℕ} exp (-c n ^ 2)` converges for `c > 0`. -/
private lemma summable_nat_exp_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  have key : ∀ n : ℕ, Real.exp (-c * (n : ℝ) ^ 2) ≤ Real.exp ((n : ℝ) * (-c)) := by
    intro n
    apply Real.exp_le_exp.mpr
    have hle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        nlinarith
    nlinarith [hle, hc]
  exact Summable.of_nonneg_of_le (f := fun n : ℕ => Real.exp ((n : ℝ) * (-c)))
    (fun n => Real.exp_nonneg _) key
    ((Real.summable_exp_nat_mul_iff (a := -c)).mpr (by linarith))

/-- The one-dimensional Gaussian sum `∑_{k : ℤ} exp (-c k ^ 2)` converges for `c > 0`. -/
private lemma summable_int_exp_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_nat_exp_sq hc
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using summable_nat_exp_sq hc

/-- The multi-dimensional Gaussian sum `∑_{z : Fin n → ℤ} ∏ i, exp (-c (z i) ^ 2)` converges
for `c > 0`.  It factors as the `n`-fold product of the one-dimensional sums over `ℤ`. -/
private lemma summable_pi_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun z : Fin n → ℤ => ∏ i, Real.exp (-c * (z i : ℝ) ^ 2)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    refine (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))).mp ?_
    have hmul : Summable (fun p : ℤ × (Fin n → ℤ) =>
        Real.exp (-c * (p.1 : ℝ) ^ 2) * ∏ i, Real.exp (-c * (p.2 i : ℝ) ^ 2)) :=
      Summable.mul_of_nonneg (summable_int_exp_sq hc) ih
        (fun k => Real.exp_nonneg _)
        (fun z => Finset.prod_nonneg (fun i _ => Real.exp_nonneg _))
    refine hmul.congr (fun p => ?_)
    simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]

/-- For a vector `x` of the `E₈` lattice, the integer coordinate `2 * x i`.  This is a
convenient way to view `E₈` as a subset of `ℤ⁸`. -/
private noncomputable def e8ToInt (x : E8) : Fin 8 → ℤ := fun i => Classical.choose (x.2.1 i)

private lemma e8ToInt_spec (x : E8) (i : Fin 8) :
    2 * (x : EuclideanSpace ℝ (Fin 8)).ofLp i = ((e8ToInt x i : ℤ) : ℝ) :=
  Classical.choose_spec (x.2.1 i)

private lemma e8ToInt_injective : Function.Injective e8ToInt := by
  intro x y h
  apply Subtype.ext
  refine WithLp.ofLp_injective 2 ?_
  funext i
  have hx := e8ToInt_spec x i
  have hy := e8ToInt_spec y i
  have hxy : e8ToInt x i = e8ToInt y i := by rw [h]
  rw [hxy] at hx
  linarith [hx, hy]

/-- Coordinate formula: a vector of `E₈` has half-integer coordinates. -/
private lemma e8_coord (x : E8) (i : Fin 8) :
    (x : EuclideanSpace ℝ (Fin 8)).ofLp i = ((e8ToInt x i : ℤ) : ℝ) / 2 := by
  have h := e8ToInt_spec x i
  linarith

/-- The squared norm of a vector of `E₈`, in terms of its `4`-scaled integer coordinates. -/
private lemma e8_norm_sq (x : E8) :
    ‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2
      = (1 / 4) * ∑ i, ((e8ToInt x i : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  simp only [show ∀ i, (x : EuclideanSpace ℝ (Fin 8)).ofLp i
      = ((e8ToInt x i : ℤ) : ℝ) / 2 from fun i => by
        have h := e8ToInt_spec x i; linarith]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The modulus of the theta summand at a vector of `E₈`, expressed through the integer
coordinates. -/
private lemma norm_thetaTerm_e8 (τ : ℍ) (x : E8) :
    ‖thetaTerm τ (x : EuclideanSpace ℝ (Fin 8))‖
      = Real.exp (-(π * τ.im / 4) * ∑ i, ((e8ToInt x i : ℤ) : ℝ) ^ 2) := by
  rw [show ‖thetaTerm τ (x : EuclideanSpace ℝ (Fin 8))‖
      = Real.exp (-π * τ.im * ‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2) by
    rw [thetaTerm, Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num]
  rw [e8_norm_sq]
  congr 1
  ring

/-- The `E₈` theta series converges absolutely on the upper half plane. -/
theorem thetaSeries_E8_summable (τ : ℍ) :
    Summable (fun x : E8 => thetaTerm τ (x : EuclideanSpace ℝ (Fin 8))) := by
  have hc : 0 < π * τ.im / 4 := by
    have := τ.im_pos; positivity
  have hF : Summable (fun z : Fin 8 → ℤ =>
      Real.exp (-(π * τ.im / 4) * ∑ i, (z i : ℝ) ^ 2)) := by
    refine (summable_pi_gauss 8 hc).congr (fun z => ?_)
    rw [Finset.mul_sum, Real.exp_sum]
  have hcomp : Summable (fun x : E8 =>
      Real.exp (-(π * τ.im / 4) * ∑ i, ((e8ToInt x i : ℤ) : ℝ) ^ 2)) :=
    hF.comp_injective e8ToInt_injective
  refine Summable.of_norm ?_
  exact hcomp.congr (fun x => (norm_thetaTerm_e8 τ x).symm)

end Work.Modular
