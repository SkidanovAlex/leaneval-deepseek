/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The box-sum power commutes with complex conjugation

The `2^t`-th power of the box norm `Work.Peluse.boxSumPow t Q S f` is the fully expanded cube
average

`(1/|S|) ∑_x E_{h,h'} ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`,

a polynomial with conjugation signs in the values of `f`.  Replacing `f` by its complex conjugate
`star ∘ f` therefore conjugates every term of the average (the `|ω|`-fold conjugation of a
conjugated value is the conjugation of the `|ω|`-fold conjugated value), and the normalising
constant `(1/|S|) ∏_i (1/|Q i|)^2` is a real number, hence fixed by `star`.

This file proves that `boxSumPow` is compatible with `star`, both for an arbitrary
`ω`-dependent family of functions (`prodCubeSum_star`, the natural general form) and for the
single-function box average (`boxSumPow_star`).

## Main results

* `Work.Peluse.Pairing.star_iterate_star_swap` : `star (star^[k] z) = star^[k] (star z)`;
* `Work.Peluse.Pairing.prodCubeSum_star` :
  `prodCubeSum t Q S (fun ω x => star (g ω x)) = star (prodCubeSum t Q S g)`;
* `Work.Peluse.Pairing.boxSumPow_star` :
  `boxSumPow t Q S (fun x => star (f x)) = star (boxSumPow t Q S f)`.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Math. Pi **8** (2020), e16,
Definition 2.1.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pairing

open Work.Peluse

noncomputable section

/-- `star` commutes with iterating `star`: both sides are `star` applied `k + 1` times. -/
lemma star_iterate_star_swap (k : ℕ) (z : ℂ) : star (star^[k] z) = star^[k] (star z) := by
  rw [← Function.iterate_succ_apply' star k z, Function.iterate_succ_apply star k z]

/-- The normalising constant of `prodCubeSum`, `(1/|S|) ∏_i (1/|Q i|)^2`, is a real number, so it
is fixed by `star`. -/
lemma star_prodCubeSum_const {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) :
    star (((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
        * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹))
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
        * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) := by
  simp only [star_mul, star_inv₀, star_natCast, star_prod]
  ring

/-- `star` commutes with the general cube average: conjugating every one of the `2^t` functions
conjugates the average. -/
theorem prodCubeSum_star {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (g : (Fin t → Bool) → ℤ → ℂ) :
    Work.Peluse.prodCubeSum t Q S (fun ω x => star (g ω x))
      = star (Work.Peluse.prodCubeSum t Q S g) := by
  simp only [Work.Peluse.prodCubeSum, star_mul, star_inv₀, star_natCast, star_prod, star_sum,
    tsum_star, star_iterate_star_swap]
  ring

/-- The `2^t`-th power of the box norm commutes with complex conjugation. -/
theorem boxSumPow_star {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow t Q S (fun x => star (f x)) = star (Work.Peluse.boxSumPow t Q S f) := by
  simp only [Work.Peluse.boxSumPow]
  exact prodCubeSum_star (t := t) Q S (fun _ => f)

end

end Work.Peluse.Pairing
