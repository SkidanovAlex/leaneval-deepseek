import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- If `P : ℤ[X]` has constant coefficient `±1`, then at every complex root `z` of `P` the value
of the integer polynomial `C (-(P.coeff 0)) * P.divX` equals `z⁻¹`.

Indeed, from `X * P.divX + C (P.coeff 0) = P` evaluated at the root `z` we get
`z * (P.divX).aeval z = -(P.coeff 0)`, and since `(P.coeff 0)² = 1` this gives
`z * (C (-(P.coeff 0)) * P.divX).aeval z = 1`, i.e. `(C (-(P.coeff 0)) * P.divX).aeval z = z⁻¹`. -/
private lemma aeval_recip_eq_inv (P : Polynomial ℤ) (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1)
    {z : ℂ} (hz : z ∈ P.aroots ℂ) :
    (Polynomial.aeval z) (C (-(P.coeff 0)) * P.divX) = z⁻¹ := by
  have hroot : (Polynomial.aeval z) P = 0 := (Polynomial.mem_aroots.mp hz).2
  have hdiv : z * (Polynomial.aeval z) P.divX + (P.coeff 0 : ℂ) = 0 := by
    have := congrArg (Polynomial.aeval z) (Polynomial.X_mul_divX_add P)
    simpa [Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_mul, hroot] using this
  have hsq : (P.coeff 0 : ℂ) ^ 2 = 1 := by
    rcases h0 with h | h <;> simp [h]
  have hzh : z * (Polynomial.aeval z) P.divX = -(P.coeff 0 : ℂ) :=
    eq_neg_of_add_eq_zero_left hdiv
  have key : z * (Polynomial.aeval z) (C (-(P.coeff 0)) * P.divX) = 1 := by
    rw [map_mul, Polynomial.aeval_C]
    have hc : (algebraMap ℤ ℂ) (-(P.coeff 0)) = -(P.coeff 0 : ℂ) := by
      rw [algebraMap_int_eq]; simp
    rw [hc]
    rw [show z * (-(P.coeff 0 : ℂ) * (Polynomial.aeval z) P.divX)
        = (-(P.coeff 0 : ℂ)) * (z * (Polynomial.aeval z) P.divX) by ring]
    rw [hzh]
    linear_combination hsq
  exact eq_inv_of_mul_eq_one_right key

/-- **Inverse power sums of the roots of a unit-constant monic integer polynomial are integers.**

If `P ∈ ℤ[X]` is monic with constant term `±1`, then all complex roots of `P` are nonzero, and
for every `m` the sum `∑_z (z⁻¹)^m` over the complex roots of `P` (counted with multiplicity)
is an integer.

The point is that the auxiliary integer polynomial `Q_m = (C (-(P.coeff 0)) * P.divX)^m` agrees
with `z ↦ (z⁻¹)^m` on the roots of `P` (using `X * P.divX + C (P.coeff 0) = P` together with
`(P.coeff 0)² = 1`), and the general principle
`Polynomial.leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap` states that
the sum of the values of an integer polynomial on the roots of a monic integer polynomial lies in
the image of `ℤ` in the coefficient field. -/
theorem inv_pow_sum_roots_int (P : Polynomial ℤ) (hP : P.Monic)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (m : ℕ) :
    ∃ c : ℤ, ((P.map (Int.castRingHom ℂ)).roots.map (fun z => (z⁻¹) ^ m)).sum = (c : ℂ) := by
  -- `aroots` over `ℂ` is the multiset of complex roots of the mapped polynomial.
  have haroots : P.aroots ℂ = (P.map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.aroots_def, algebraMap_int_eq]
  -- The auxiliary integer polynomial agrees with `z ↦ (z⁻¹)^m` on the roots of `P`.
  have hq : ∀ z ∈ P.aroots ℂ,
      (Polynomial.aeval z) ((C (-(P.coeff 0)) * P.divX) ^ m) = (z⁻¹) ^ m := by
    intro z hz
    rw [map_pow]
    congr 1
    exact aeval_recip_eq_inv P h0 hz
  -- Integrality of the sum of the values of the auxiliary polynomial on the roots.
  have hmem : ((P.aroots ℂ).map
      (fun z => (Polynomial.aeval z) ((C (-(P.coeff 0)) * P.divX) ^ m))).sum
      ∈ Set.range (algebraMap ℤ ℂ) := by
    have h := Polynomial.leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap
      (R := ℤ) (A := ℂ) P ((C (-(P.coeff 0)) * P.divX) ^ m) (IsAlgClosed.splits _)
    simpa [hP.leadingCoeff] using h
  -- Replace the auxiliary polynomial by the function `z ↦ (z⁻¹)^m`.
  have hmap : (P.aroots ℂ).map
        (fun z => (Polynomial.aeval z) ((C (-(P.coeff 0)) * P.divX) ^ m))
      = ((P.map (Int.castRingHom ℂ)).roots).map (fun z => (z⁻¹) ^ m) := by
    rw [haroots]
    apply Multiset.map_congr rfl
    intro z hz
    exact hq z (by rwa [← haroots] at hz)
  rw [hmap] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  rw [← hc, algebraMap_int_eq]
  rfl

end Work.BW
