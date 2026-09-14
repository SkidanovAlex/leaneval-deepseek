import Mathlib
import Submission.Vdw.FourierWeight
import Submission.Commons.NumberTheory.ZMod.sum_minrep_weight_le
import Submission.Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le_zmod
import Submission.Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le_zmod

open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The frequency weight for a composite modulus (multi-prime §4)

The §4 Fourier chapter bounds the error term of the *single-prime* counting
problem by a sum of weights `freqWeight p H b = min (2H+1) (p/(2·minrep b))` over
the nonzero frequencies `b : ZMod p`.  For the multi-prime assembly (paper
Corollary `Dequi2`) the same weight is needed with the *composite* modulus
`C = ∏ p_i` in place of the prime `p`: the joint Fourier expansion over
`∏_i (Z/p_i)^n` produces, in each coordinate, the frequency
`c_i/C ∈ (1/C)ℤ` of the box character sum, and the character sum over an
interval of length `2H+1` is bounded by `min (2H+1) (C/(2·minrep c_i))`.

This module defines that weight and proves the resulting weight sum is
`≤ (5(M + (2H+1))(1+log M))^m` — the composite analogue of
`FourierWeight.sum_freqWeight_prod_le`, from the commons lemma
`Commons.NumberTheory.ZMod.sum_minrep_weight_le` (generalizing the prime-modulus
one-dimensional estimate) plus the factorization of the product over
coordinates.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The frequency weight for the modulus `M`**: the trivial bound `2H+1` at
the zero frequency, and `min (2H+1) (M/(2·minrep b))` otherwise, where
`minrep b = min b.val (M - b.val)` is the distance of `b` to `0` in `ZMod M`. -/
def freqWeightZ (M : ℕ) [NeZero M] (H : ℕ) (b : ZMod M) : ℝ :=
  if b = 0 then ((2 * H + 1 : ℕ) : ℝ)
  else min (((2 * H + 1 : ℕ)) : ℝ) ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ)))

/-- The composite weight agrees with the prime-modulus weight of
`FourierWeight` when the modulus is a prime. -/
theorem freqWeightZ_eq_freqWeight (p : ℕ) [Fact p.Prime] (H : ℕ) (b : ZMod p) :
    freqWeightZ p H b = freqWeight p H b := by
  rw [freqWeightZ, freqWeight]

lemma freqWeightZ_nonneg (M : ℕ) [NeZero M] (H : ℕ) (b : ZMod M) :
    0 ≤ freqWeightZ M H b := by
  rw [freqWeightZ]
  split_ifs
  · exact_mod_cast Nat.zero_le _
  · exact le_min (by positivity) (by positivity)

/-- **The one-dimensional composite weight sum** (from the commons lemma). -/
theorem sum_freqWeightZ_le (M : ℕ) [NeZero M] (H : ℕ) :
    ∑ b : ZMod M, freqWeightZ M H b
      ≤ 5 * ((M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ)) * (1 + Real.log M) := by
  simpa only [freqWeightZ] using
    Commons.NumberTheory.ZMod.sum_minrep_weight_le M H

/-- **The `m`-fold composite weight sum**: the weights factor over the
coordinates. -/
theorem sum_freqWeightZ_prod_le (M : ℕ) [NeZero M] (m H : ℕ) :
    ∑ c : Fin m → ZMod M, ∏ i, freqWeightZ M H (c i)
      ≤ (5 * ((M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ)) * (1 + Real.log M)) ^ m := by
  classical
  have hfac : ∏ i : Fin m, ∑ b : ZMod M, freqWeightZ M H b
      = ∑ c : Fin m → ZMod M, ∏ i, freqWeightZ M H (c i) := by
    rw [Finset.prod_univ_sum (t := fun _ : Fin m => (Finset.univ : Finset (ZMod M)))]
    rw [Fintype.piFinset_univ]
  rw [← hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => freqWeightZ_nonneg M H b))
    (sum_freqWeightZ_le M H) m

/-- **Composite Fourier box atom (general bound form)**: if every
one-dimensional range sum of the frequency `a i` is bounded by `K i`, then the
character sum over the symmetric coefficient box `(BddInt H)^m` is bounded by
the product of the `K i`.  Composite-modulus version of
`BoxFourier.norm_sum_bddVec_stdAddChar_le_of_bound`. -/
theorem norm_sum_bddVec_stdAddChar_le_of_bound_zmod (M : ℕ) [NeZero M] (m H : ℕ)
    (a : Fin m → ZMod M) (K : Fin m → ℝ)
    (h : ∀ i, ‖∑ k ∈ Finset.range (2 * H + 1),
        ZMod.stdAddChar ((k : ZMod M) * a i)‖ ≤ K i) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod M) * a i)‖
      ≤ ∏ i, K i := by
  classical
  set L : ℕ := 2 * H + 1 with hL
  have hreindex : ∑ z : BddVec m H,
        ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod M) * a i)
      = ∑ v : Fin m → Fin L, ZMod.stdAddChar
          (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod M) * a i) := by
    rw [← Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin m => (bddIntEquivFin H).symm))
        (fun v : Fin m → Fin L => ZMod.stdAddChar
          (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod M) * a i))
        (fun z : BddVec m H => ZMod.stdAddChar
          (∑ i, ((z i : ℤ) : ZMod M) * a i))]
    intro v
    exact congrArg _ (Finset.sum_congr rfl (fun i _ => rfl))
  have hsplit : ∀ (v : Fin m → Fin L),
      ZMod.stdAddChar (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod M) * a i)
        = ZMod.stdAddChar (-(∑ i, (H : ZMod M) * a i)) *
          ZMod.stdAddChar (∑ i, (((v i : ℕ) : ZMod M) * a i)) := by
    intro v
    have harg : (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod M) * a i)
        = (∑ i, (((v i : ℕ) : ZMod M) * a i))
          - (∑ i, (H : ZMod M) * a i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [harg, AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.map_neg_eq_inv, mul_comm]
  rw [hreindex]
  have hfactor : ∑ v : Fin m → Fin L, ZMod.stdAddChar
        (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod M) * a i)
      = ZMod.stdAddChar (-(∑ i, (H : ZMod M) * a i)) *
        ∑ v : Fin m → Fin L, ZMod.stdAddChar
          (∑ i, (((v i : ℕ) : ZMod M) * a i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [hsplit v]
  rw [hfactor, norm_mul, norm_stdAddChar_eq_one, one_mul]
  refine Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le_zmod M m L a K ?_
  intro i
  simpa [L] using h i

/-- **Composite Fourier box atom**: the character sum over the symmetric
coefficient box `(BddInt H)^m` at the frequencies `a i` is at most the product
of the composite weights `freqWeightZ M H`.  This is the box-atom input of the
multi-prime (§4, Corollary `Dequi2`) assembly, generalizing
`BoxFourier.norm_sum_bddVec_stdAddChar_le_weight` from a prime modulus to an
arbitrary modulus. -/
theorem norm_sum_bddVec_stdAddChar_le_weight_zmod (M : ℕ) [NeZero M] (m H : ℕ)
    (a : Fin m → ZMod M) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod M) * a i)‖
      ≤ ∏ i, freqWeightZ M H (a i) := by
  classical
  refine norm_sum_bddVec_stdAddChar_le_of_bound_zmod M m H a
    (fun i => freqWeightZ M H (a i)) (fun i => ?_)
  by_cases hai : a i = 0
  · rw [hai]
    have h1 : ∀ k ∈ Finset.range (2 * H + 1),
        ZMod.stdAddChar ((k : ZMod M) * (0 : ZMod M)) = 1 := by
      intro k _
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      freqWeightZ, if_pos rfl]
    exact le_of_eq (Complex.norm_natCast (2 * H + 1))
  · rw [freqWeightZ, if_neg hai]
    exact Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le_zmod M (a i) hai (2 * H + 1)

end

end Submission.Vdw
