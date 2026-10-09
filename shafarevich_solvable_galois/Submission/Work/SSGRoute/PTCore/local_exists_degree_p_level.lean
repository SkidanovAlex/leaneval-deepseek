import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# A finite Galois extension of a local field with degree divisible by `p`

For the `Q`-adic completion `F = Q.adicCompletion K` of a number field `K` and a prime `p`, we
construct a finite Galois intermediate field `L ⊆ AlgebraicClosure F` with `p ∣ [L : F]`.

The construction is elementary.  Let `π` be a uniformizer of `F`, so that `v π = exp (-1)`.
The splitting field `L` of `X ^ p - π` over `F` is finite and Galois over `F` (it is the splitting
field of a separable polynomial), and it contains a `p`-th root `α` of `π`.  Taking norms from `L`
to `F` gives

`N(α) ^ p = N(α ^ p) = N(π) = π ^ [L : F]`,

and applying the valuation `v` and the logarithm of the value group turns this into
`p • log (v (N α)) = [L : F] • (-1)`, whence `p ∣ [L : F]`.
-/

namespace Work.SSGRoute.PTCore

open Polynomial

/-- Arithmetic: if `p • k = e • (-1)` in `ℤ`, then `p ∣ e`. -/
private lemma dvd_of_nsmul_eq_neg {p e : ℕ} {k : ℤ} (h : p • k = e • (-1 : ℤ)) : p ∣ e := by
  have h' : (p : ℤ) * k = -(e : ℤ) := by simpa [nsmul_eq_mul] using h
  refine Int.ofNat_dvd.mp ⟨-k, ?_⟩
  rw [mul_neg, h', neg_neg]

/-- **A finite Galois extension of degree divisible by `p`, from a uniformizer.**
Let `F` be a field of characteristic zero equipped with a valuation `w` with values in
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, and let `π` be a uniformizer, i.e. `w π = exp (-1)`.
Then there is a finite Galois extension `L` of `F` (an intermediate field of the algebraic
closure) with `p ∣ [L : F]`. -/
theorem exists_galois_degree_p_dvd_of_uniformizer (p : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [CharZero F] (w : Valuation F (WithZero (Multiplicative ℤ))) (π : F)
    (hπ : w π = WithZero.exp (-1)) :
    ∃ L : IntermediateField F (AlgebraicClosure F),
      FiniteDimensional F ↥L ∧ IsGalois F ↥L ∧ p ∣ Module.finrank F ↥L := by
  haveI hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hπne : π ≠ 0 := (Valuation.ne_zero_iff w).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  -- the splitting field of `X ^ p - π`
  let L : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F ((X ^ p - C π).rootSet (AlgebraicClosure F))
  haveI hsplit : Polynomial.IsSplittingField F ↥L (X ^ p - C π) :=
    IntermediateField.adjoin_rootSet_isSplittingField (p := X ^ p - C π) (IsAlgClosed.splits _)
  haveI hfin : FiniteDimensional F ↥L :=
    Polynomial.IsSplittingField.finiteDimensional ↥L (X ^ p - C π)
  haveI hgal : IsGalois F ↥L :=
    IsGalois.of_separable_splitting_field (p := X ^ p - C π)
      (separable_X_pow_sub_C π hpF hπne)
  haveI : Module.Free F ↥L := Module.Free.of_divisionRing F ↥L
  -- a `p`-th root of `π` inside `L`
  let α : ↥L := rootOfSplitsXPowSubC (NeZero.pos p) π ↥L
  have hα : α ^ p = algebraMap F ↥L π :=
    rootOfSplitsXPowSubC_pow (n := p) (a := π) (L := ↥L)
  -- norm computation: `N(α) ^ p = π ^ [L : F]`
  have hnorm : ((Algebra.norm F) α) ^ p = π ^ Module.finrank F ↥L := by
    rw [← map_pow, hα, Algebra.norm_algebraMap]
  have hw : (w ((Algebra.norm F) α)) ^ p = (w π) ^ Module.finrank F ↥L := by
    simpa using congrArg w hnorm
  rw [hπ] at hw
  have hlog : p • WithZero.log (w ((Algebra.norm F) α)) =
      Module.finrank F ↥L • (-1 : ℤ) := by
    have h := congrArg WithZero.log hw
    simpa only [WithZero.log_pow, WithZero.log_exp] using h
  exact ⟨L, hfin, hgal, dvd_of_nsmul_eq_neg hlog⟩

theorem local_exists_degree_p_level (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ L : IntermediateField (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)),
      FiniteDimensional (Q.adicCompletion K) ↥L ∧ IsGalois (Q.adicCompletion K) ↥L ∧
        p ∣ Module.finrank (Q.adicCompletion K) ↥L := by
  haveI : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (Q.adicCompletion K)))
  obtain ⟨π, hπ⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K Q
  have hπ' : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  exact exists_galois_degree_p_dvd_of_uniformizer p
    (Valued.v : Valuation (Q.adicCompletion K) (WithZero (Multiplicative ℤ)))
    (π : Q.adicCompletion K) hπ'

end Work.SSGRoute.PTCore
