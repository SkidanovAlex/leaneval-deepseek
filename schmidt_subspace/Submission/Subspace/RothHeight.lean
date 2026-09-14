import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_sum_le
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_pderivIter_le
import Submission.Commons.Algebra.MvPolynomial.pderivIter_map

/-!
# Heights of integer polynomials (normalisation for the Roth lemma)

For an integer polynomial `P` we use the *affine* logarithmic height
`hZ P = log (Height.mulHeight (gP (P.map (Int.castRingHom ℚ))))`; for integral polynomials this is
`log (max |coeff|)`, and it is the normalisation in which the sharp sum bound
(`polyHeight_int_sum_le`), the sharp product bound, and exact multiplicativity for polynomials in
disjoint variables (`polyHeight_int_tensor_eq`) hold.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial
open Commons.NumberTheory.Height.MvPolynomial (gP)

variable {σ : Type*}

/-- The affine logarithmic height of an integer polynomial (via its image in `ℚ[x]`). -/
noncomputable def hZ (P : MvPolynomial σ ℤ) : ℝ :=
  Height.logHeight (gP (P.map (Int.castRingHom ℚ)))

lemma gP_ne_zero' {σ : Type*} (Q : MvPolynomial σ ℚ) : gP Q ≠ 0 := by
  intro h
  have := congrFun h none
  simp [gP] at this

/-- The height of `gP` is invariant under `Q ↦ -Q` (the `none` slot, holding `1`, changes to `1`). -/
lemma mulHeight_gP_neg (Q : MvPolynomial σ ℚ) :
    Height.mulHeight (gP (-Q)) = Height.mulHeight (gP Q) := by
  have hne : gP (-Q) ≠ 0 := gP_ne_zero' _
  have hne' : gP Q ≠ 0 := gP_ne_zero' _
  have hcoeff : ∀ m : σ →₀ ℕ, MvPolynomial.coeff m (-Q) = -(MvPolynomial.coeff m Q) := by
    intro m; simp
  have key : ∀ v : AbsoluteValue ℚ ℝ, (⨆ o, v (gP (-Q) o)) = (⨆ o, v (gP Q o)) := by
    intro v
    refine iSup_congr fun o => ?_
    cases o with
    | none => simp [gP]
    | some m =>
      show v (MvPolynomial.coeff m (-Q)) = v (MvPolynomial.coeff m Q)
      rw [hcoeff m, AbsoluteValue.map_neg]
  rw [Height.mulHeight_eq hne, Height.mulHeight_eq hne']
  refine congrArg₂ (·*·) ?_ ?_
  · exact congrArg Multiset.prod (Multiset.map_congr rfl fun v _ => key v)
  · exact finprod_congr fun v => key v.val

/-- The affine height of an integer polynomial is invariant under units. -/
lemma hZ_smul_unit (P : MvPolynomial σ ℤ) (u : ℤˣ) : hZ (u • P) = hZ P := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · have h1 : (-1 : ℤˣ) • P = -P := by simp
    rw [h1]
    change Real.log (Height.mulHeight (gP (((-P : MvPolynomial σ ℤ)).map (Int.castRingHom ℚ)))) =
      Real.log (Height.mulHeight (gP (P.map (Int.castRingHom ℚ))))
    rw [map_neg, mulHeight_gP_neg]

lemma hZ_neg (P : MvPolynomial σ ℤ) : hZ (-P) = hZ P := by
  have : (-P : MvPolynomial σ ℤ) = (-1 : ℤˣ) • P := by simp
  rw [this, hZ_smul_unit]


section Det

open scoped Matrix

/-- **Height of a determinant of integer polynomials.** -/
theorem hZ_det_le {σ : Type*} [Fintype σ] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ ℤ)) (H L : ℝ) (hH0 : 0 ≤ H) (hL0 : 0 ≤ L)
    (hprod : ∀ π : Equiv.Perm (Fin k), hZ (Finset.univ.prod fun i => A (π i) i) ≤ H * k + L) :
    hZ A.det ≤ H * k + L + Real.log (Nat.factorial k) := by
  rw [Matrix.det_apply, hZ]
  unfold gP
  have hbound : ∀ π : Equiv.Perm (Fin k),
      hZ ((↑(Equiv.Perm.sign π) : ℤˣ) • (Finset.univ.prod fun i => A (π i) i)) ≤ H * k + L := by
    intro π
    rw [hZ_smul_unit]
    exact hprod π
  have key := Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_sum_le
    (σ := σ) (Finset.univ : Finset (Equiv.Perm (Fin k)))
    (fun π => (↑(Equiv.Perm.sign π) : ℤˣ) • (Finset.univ.prod fun i => A (π i) i)) (H * k + L)
    (by positivity) (fun π _ => hbound π)
  simpa [Finset.card_univ, Fintype.card_perm, Finset.card_fin] using key

end Det

end Submission.Subspace
