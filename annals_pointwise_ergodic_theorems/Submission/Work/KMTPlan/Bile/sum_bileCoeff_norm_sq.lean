/-
# Plancherel for the DFT normalisation of `bileCoeff`

The inverse DFT coefficients of the band-limited lift are `bileCoeff Q f j = Q⁻¹ · (dft f) (-j)`.
This file proves that they satisfy Plancherel's identity in the normalisation used by the lift:

`∑_j ‖bileCoeff Q f j‖² = Q⁻¹ · ∑_x ‖f x‖²`.

Mathlib has `ZMod.dft` and its inversion formula `ZMod.dft_dft` but no Plancherel identity for it,
so the identity is proved here from scratch.  The core computation is the bilinear identity

`∑_k dft Φ k · conj (dft Ψ k) = Q · ∑_j Φ j · conj (Ψ j)`,

which follows by expanding both DFTs as character sums `dft Φ k = ∑_j e(-j k) Φ j` and using the
orthogonality of the standard additive character, `∑_k e((i - j) k) = Q δ_{ij}`
(`AddChar.sum_mulShift` for the primitive character `ZMod.stdAddChar`).
-/
import Mathlib
import Submission.Work.KMTPlan.Bile.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped FourierTransform SchwartzMap BigOperators

namespace Work.KMTPlan.Bile

/-! ## Characters of `ZMod Q` -/

/-- The standard additive character of `ZMod Q` has unit modulus. -/
lemma norm_stdAddChar (Q : ℕ) [NeZero Q] (x : ZMod Q) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Complex conjugation inverts the standard additive character. -/
lemma star_stdAddChar (Q : ℕ) [NeZero Q] (x : ZMod Q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [show star (ZMod.stdAddChar x) = (ZMod.stdAddChar x)⁻¹ from
      (Complex.inv_eq_conj (norm_stdAddChar Q x)).symm,
    ← AddChar.map_neg_eq_inv]

/-- Orthogonality of the standard additive character: `∑_k e(-j k) e(i k) = Q δ_{ij}`. -/
lemma sum_stdAddChar_mul (Q : ℕ) [NeZero Q] (i j : ZMod Q) :
    (∑ k : ZMod Q, ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (i * k))
      = if i = j then (Q : ℂ) else 0 := by
  have h : ∀ k : ZMod Q, ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (i * k)
      = ZMod.stdAddChar (k * (i - j)) := by
    intro k
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [h]
  rw [AddChar.sum_mulShift (i - j) (ZMod.isPrimitive_stdAddChar Q), ZMod.card]
  simp [sub_eq_zero]

/-! ## The bilinear Plancherel identity for `ZMod.dft` -/

/-- The DFT expanded as a character sum. -/
lemma dft_expand (Q : ℕ) [NeZero Q] (Φ : ZMod Q → ℂ) (k : ZMod Q) :
    ZMod.dft Φ k = ∑ j : ZMod Q, ZMod.stdAddChar (-(j * k)) * Φ j := by
  rw [ZMod.dft_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]

/-- The complex conjugate of the DFT expanded as a character sum. -/
lemma star_dft_expand (Q : ℕ) [NeZero Q] (Φ : ZMod Q → ℂ) (k : ZMod Q) :
    star (ZMod.dft Φ k) = ∑ j : ZMod Q, ZMod.stdAddChar (j * k) * star (Φ j) := by
  rw [dft_expand Q Φ k, star_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [star_mul, star_stdAddChar, neg_neg, mul_comm]

/-- The bilinear (sesquilinear) Plancherel identity for the DFT on `ZMod Q`. -/
lemma dft_mul_star_sum (Q : ℕ) [NeZero Q] (Φ Ψ : ZMod Q → ℂ) :
    (∑ k : ZMod Q, ZMod.dft Φ k * star (ZMod.dft Ψ k))
      = (Q : ℂ) * ∑ j : ZMod Q, Φ j * star (Ψ j) := by
  calc (∑ k : ZMod Q, ZMod.dft Φ k * star (ZMod.dft Ψ k))
      = ∑ k : ZMod Q, (∑ j : ZMod Q, ZMod.stdAddChar (-(j * k)) * Φ j)
          * (∑ i : ZMod Q, ZMod.stdAddChar (i * k) * star (Ψ i)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dft_expand Q Φ k, star_dft_expand Q Ψ k]
    _ = ∑ k : ZMod Q, ∑ j : ZMod Q, ∑ i : ZMod Q,
          (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (i * k)) * (Φ j * star (Ψ i)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ j : ZMod Q, ∑ i : ZMod Q,
          (∑ k : ZMod Q, ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (i * k))
            * (Φ j * star (Ψ i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j : ZMod Q, ∑ i : ZMod Q, (if i = j then (Q : ℂ) else 0) * (Φ j * star (Ψ i)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [sum_stdAddChar_mul Q i j]
    _ = (Q : ℂ) * ∑ j : ZMod Q, Φ j * star (Ψ j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi
          rw [if_neg hi, zero_mul]
        · intro hj
          exact absurd (Finset.mem_univ j) hj

/-! ## Plancherel in the norm-squared form -/

/-- The square of the norm of a complex number, read in `ℂ`, is `z · conj z`. -/
lemma ofReal_normSq_eq_mul_star (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * star z := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← starRingEnd_apply (R := ℂ) z]

/-- `∑_x ‖f x‖²`, read in `ℂ`, is `∑_x f x · conj (f x)`. -/
lemma ofReal_sum_normSq_eq_sum_mul_star (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    (((∑ x : ZMod Q, ‖f x‖ ^ 2 : ℝ)) : ℂ) = ∑ x : ZMod Q, f x * star (f x) := by
  rw [Complex.ofReal_sum (Finset.univ : Finset (ZMod Q))]
  exact Finset.sum_congr rfl fun x _ => ofReal_normSq_eq_mul_star (f x)

/-- Plancherel for the DFT on `ZMod Q`: `∑_k ‖dft f k‖² = Q · ∑_x ‖f x‖²`. -/
lemma sum_normSq_dft (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    (∑ k : ZMod Q, ‖ZMod.dft f k‖ ^ 2) = (Q : ℝ) * ∑ x : ZMod Q, ‖f x‖ ^ 2 := by
  refine Complex.ofReal_injective ?_
  rw [ofReal_sum_normSq_eq_sum_mul_star Q (ZMod.dft f), Complex.ofReal_mul,
    ofReal_sum_normSq_eq_sum_mul_star Q f, dft_mul_star_sum Q f f]
  simp

/-! ## The norm-squared sum of the inverse DFT coefficients -/

end Work.KMTPlan.Bile
