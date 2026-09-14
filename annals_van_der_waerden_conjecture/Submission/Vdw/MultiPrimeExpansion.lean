import Mathlib
import Submission.Vdw.MultiPrimeWeight
import Submission.Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le_zmod

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The multi-prime (§4) frequency analysis

The multi-prime Fourier expansion of the index conditions (paper §4,
Corollary `Dequi2`) needs two analytic inputs at *composite* modulus
`C = ∏_{p ∈ s} p`; this module supplies them.

* `prod_stdAddChar_eq_combination` — **the CRT-combination identity**: for
  `C = ∏_{p ∈ s} p` and frequencies `b_p ∈ ZMod p`,
  `∏_p stdAddChar ((x : ZMod p) · b_p) = stdAddChar ((x : ZMod C) · B)`
  with `B = Σ_p b_p·(C/p)`.  This is the key pointwise input: the *product* of
  the per-prime characters is a *single* standard character of the product
  modulus at the plainly-defined integer combination `B` (no character/CRT
  bookkeeping beyond `Σ_p b_p/p = B/C` is needed, and the identity is checked
  at the level of the exponential arguments `2πi·x·Σ_p b_p/p = 2πi·x·B/C`).
  Auxiliary: `natCast_mul_div_eq_div`, the casting identity
  `(b·(C/p) : ℂ)/C = b/p` for `p ∣ C`.
* `norm_sum_joint_box_char_le` — **the joint box character sum**: the product
  over the primes of the per-prime characters at the frequencies `b p i`,
  summed over the coefficient box `(BddInt H)^n`, is bounded by the product
  over the coordinates of the composite weight `freqWeightZ C H` at the
  CRT combinations `Σ_p b_p·(C/p)`.  This is the box-frequency input of the
  multi-prime error term (it combines the pointwise identity with the
  composite box atom `MultiPrimeWeight.norm_sum_bddVec_stdAddChar_le_weight_zmod`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- Casting identity used in the CRT-combination computation: for `0 < p`,
`p ∣ C`, `0 < C` and `b : ℕ`, `(b·(C/p) : ℂ)/C = b/p`. -/
theorem natCast_mul_div_eq_div (C p b : ℕ) (hdvd : p ∣ C) (hp : 0 < p) (hC : 0 < C) :
    (((b * (C / p) : ℕ)) : ℂ) / ((C : ℕ) : ℂ) = ((b : ℕ) : ℂ) / ((p : ℕ) : ℂ) := by
  have hR : (((b * (C / p) : ℕ)) : ℝ) / ((C : ℕ) : ℝ)
      = ((b : ℕ) : ℝ) / ((p : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_div hdvd]
    field_simp
    positivity
  have hC' : ((C : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.pos_iff_ne_zero.mp hC
  have hp' : ((p : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.pos_iff_ne_zero.mp hp
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hR
  push_cast at hcast
  rw [div_eq_div_iff hC' hp'] at hcast ⊢
  rw [Nat.cast_mul] at ⊢
  exact hcast

/-- Pointwise: the product of the per-prime additive characters at a single
coordinate equals the standard character of the product modulus at the CRT
combination `B = Σ_p b_p·(C/p)` of the frequencies (`C = ∏_{p ∈ s} p`). -/
theorem prod_stdAddChar_eq_combination (s : Finset ℕ) (hpos : ∀ m ∈ s, 0 < m)
    [inst : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
    (C : ℕ) [NeZero C] (hC : C = ∏ q ∈ s, q)
    (x : ℤ) (b : ∀ p : {p // p ∈ s}, ZMod (p : ℕ)) :
    ∏ p : {p // p ∈ s}, ZMod.stdAddChar ((x : ZMod (p : ℕ)) * (b p))
      = ZMod.stdAddChar ((x : ZMod C) *
          (((∑ p : {p // p ∈ s}, (b p).val * (C / (p : ℕ)) : ℕ)) : ZMod C)) := by
  classical
  set B : ℕ := ∑ p : {p // p ∈ s}, (b p).val * (C / (p : ℕ)) with hB
  have hdvd : ∀ p : {p // p ∈ s}, (p : ℕ) ∣ C := by
    intro p
    rw [hC]
    exact Finset.dvd_prod_of_mem (fun q => q) p.2
  have key : ∀ p : {p // p ∈ s},
      ZMod.stdAddChar ((x : ZMod (p : ℕ)) * (b p))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * ((b p).val : ℂ) / (p : ℂ)) := by
    intro p
    have hx : ((x : ZMod (p : ℕ)) * (b p)) = (((x * ((b p).val : ℤ) : ℤ)) : ZMod (p : ℕ)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (b p)]
      push_cast
      ring
    rw [hx, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hrhs : ZMod.stdAddChar ((x : ZMod C) * ((B : ℕ) : ZMod C))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * ((B : ℂ) / (C : ℂ))) := by
    rw [show ((x : ZMod C) * ((B : ℕ) : ZMod C)) = (((x * (B : ℤ)) : ℤ) : ZMod C) from by
      push_cast
      ring,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun p _ => key p), hrhs, ← Complex.exp_sum]
  congr 1
  have hsum2 : (∑ p : {p // p ∈ s}, ((b p).val : ℂ) / (p : ℂ)) = (B : ℂ) / (C : ℂ) := by
    have hCpos : 0 < C := by rw [hC]; exact Finset.prod_pos (fun q hq => hpos q hq)
    rw [hB, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact (natCast_mul_div_eq_div C (p : ℕ) (b p).val (hdvd p) (hpos p.1 p.2) hCpos).symm
  rw [← hsum2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-- **The joint box character sum**: the product over the primes of the
per-prime characters at the frequencies `b p i`, summed over the coefficient
box, is bounded by the product over the coordinates of the composite weight at
the CRT combination `Σ_p b_p·(C/p)`.  This is the box-frequency input of the
multi-prime (§4, Corollary `Dequi2`) Fourier expansion. -/
theorem norm_sum_joint_box_char_le (s : Finset ℕ) (hpos : ∀ m ∈ s, 0 < m)
    [inst : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
    (C : ℕ) [NeZero C] (hC : C = ∏ q ∈ s, q)
    (n H : ℕ) (b : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    ‖∑ f : BddVec n H, ∏ p : {p // p ∈ s}, ∏ i : Fin n,
        ZMod.stdAddChar (((f i : ℤ) : ZMod (p : ℕ)) * (b p i))‖
      ≤ ∏ i : Fin n, freqWeightZ C H
          (((∑ p : {p // p ∈ s}, (b p i).val * (C / (p : ℕ)) : ℕ)) : ZMod C) := by
  classical
  have hpoint : ∀ f : BddVec n H,
      ∏ p : {p // p ∈ s}, ∏ i : Fin n,
          ZMod.stdAddChar (((f i : ℤ) : ZMod (p : ℕ)) * (b p i))
        = ZMod.stdAddChar (∑ i : Fin n, ((f i : ℤ) : ZMod C) *
            (((∑ p : {p // p ∈ s}, (b p i).val * (C / (p : ℕ)) : ℕ)) : ZMod C)) := by
    intro f
    rw [Finset.prod_comm]
    have h1 : ∀ i : Fin n, (∏ p : {p // p ∈ s},
          ZMod.stdAddChar (((f i : ℤ) : ZMod (p : ℕ)) * (b p i)))
        = ZMod.stdAddChar (((f i : ℤ) : ZMod C) *
            (((∑ p : {p // p ∈ s}, (b p i).val * (C / (p : ℕ)) : ℕ)) : ZMod C)) :=
      fun i => prod_stdAddChar_eq_combination s hpos C hC (f i : ℤ) (fun p => b p i)
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    rw [← Commons.NumberTheory.ZMod.AddChar.map_sum_eq_prod ZMod.stdAddChar Finset.univ
      (fun i : Fin n => ((f i : ℤ) : ZMod C) *
        (((∑ p : {p // p ∈ s}, (b p i).val * (C / (p : ℕ)) : ℕ)) : ZMod C))]
  rw [Finset.sum_congr rfl (fun f _ => hpoint f)]
  exact norm_sum_bddVec_stdAddChar_le_weight_zmod C n H
    (fun i : Fin n => (((∑ p : {p // p ∈ s}, (b p i).val * (C / (p : ℕ)) : ℕ)) : ZMod C))

end

end Submission.Vdw
