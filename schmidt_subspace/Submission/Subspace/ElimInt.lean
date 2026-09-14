import Mathlib
import Submission.Subspace.ElimHeight
import Submission.Subspace.RothHeight

/-!
# The elimination iteration over `ℤ`

`Submission.Subspace.elimF` (the iterated division by the lowest power of each variable of a
list) is defined over a field.  For the non-vanishing argument we need an *integral* version:
the Siegel polynomial has integer coefficients in the coordinate variables, and this
integrality must be preserved by the elimination, since the conclusion of the projective Roth
lemma is applied to an integral polynomial.

This file provides `elimFZ` (the integral elimination) together with the bridge

  `elimF ys (F.map (Int.castRingHom ℚ)) = (elimFZ ys F).map (Int.castRingHom ℚ)`

and the height bound `hZ (elimFZ ys F) ≤ hZ F`.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The lowest power of `X y` occurring in an integral polynomial (`0` for `F = 0`). -/
noncomputable def lowestDegZ (y : σ) (F : MvPolynomial σ ℤ) : ℕ :=
  sInf {n : ℕ | ∃ u ∈ F.support, u y = n}

/-- The polynomial obtained from an integral `F` by dividing out the *lowest* power of `X y`
occurring in `F`. -/
noncomputable def lowestCoeffZ (y : σ) (F : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ u ∈ F.support.filter (fun u => u y = lowestDegZ y F),
    MvPolynomial.monomial (u - Finsupp.single y (lowestDegZ y F)) (MvPolynomial.coeff u F)

/-- The integral elimination iteration. -/
noncomputable def elimFZ : List σ → MvPolynomial σ ℤ → MvPolynomial σ ℤ
  | [], F => F
  | y :: ys, F => elimFZ ys (lowestCoeffZ y F)

lemma intCast_injective' : Function.Injective (Int.castRingHom ℚ) := fun a b h => Int.cast_injective h

@[simp]
lemma support_map_intCast (F : MvPolynomial σ ℤ) :
    (F.map (Int.castRingHom ℚ)).support = F.support :=
  MvPolynomial.support_map_of_injective F intCast_injective'

lemma lowestDeg_map_intCast (y : σ) (F : MvPolynomial σ ℤ) :
    lowestDeg y (F.map (Int.castRingHom ℚ)) = lowestDegZ y F := by
  rw [lowestDeg, lowestDegZ, support_map_intCast]

lemma lowestCoeffZ_map_intCast (y : σ) (F : MvPolynomial σ ℤ) :
    lowestCoeff y (F.map (Int.castRingHom ℚ)) =
      (lowestCoeffZ y F).map (Int.castRingHom ℚ) := by
  rw [lowestCoeff, lowestCoeffZ, lowestDeg_map_intCast, support_map_intCast]
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.coeff_map]

lemma elimFZ_map_intCast (ys : List σ) (F : MvPolynomial σ ℤ) :
    elimF ys (F.map (Int.castRingHom ℚ)) = (elimFZ ys F).map (Int.castRingHom ℚ) := by
  induction ys generalizing F with
  | nil => rfl
  | cons y ys ih =>
      simp only [elimFZ]
      rw [elimF, lowestCoeffZ_map_intCast]
      exact ih (lowestCoeffZ y F)

/-- The integral elimination does not increase the height. -/
lemma hZ_elimFZ_le (ys : List σ) (F : MvPolynomial σ ℤ) :
    hZ (elimFZ ys F) ≤ hZ F := by
  have h := logHeight_gP_elimF_le ys (F.map (Int.castRingHom ℚ))
  rw [hZ, hZ, ← elimFZ_map_intCast ys F]
  exact h

end Submission.Subspace
