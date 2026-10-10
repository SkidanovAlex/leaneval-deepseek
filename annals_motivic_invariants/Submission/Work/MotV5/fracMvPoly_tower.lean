import Mathlib

set_option linter.unusedVariables false -- v435-speed

/-!
# The rational-function-field tower of `Frac(MvPolynomial (Fin m) F)`

Helper lemmas for node **CAN** (`Work.MotV5.fracMvPoly_cancel`): the field
`S(m,F) := FractionRing (MvPolynomial (Fin m) F)` is the `m`-fold iterated rational function field
over `F`, so

* `S(0,F) = Frac F` is `F` itself (`surjective_algebraMap_mvPoly_zero`);
* `S(m+1,F) ≅ RatFunc (S(m,F))` over `S(m,F)` (`fracMvPoly_succ_ratFunc`).

The second is the only non-elementary step: it is the base change
`FractionRing (Polynomial A) ≅ RatFunc (FractionRing A)` for a domain `A`
(`ratFunc_fractionRing`), which is proved by exhibiting both sides as fraction rings of `A[X]`;
the `RatFunc`-flavoured version of the same fact is `Work.CrauderKatz.ratFunc_equiv_fractionRing_polynomial`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotV5

noncomputable section

open Polynomial

/-! ## §1 The fraction field of a field is the field -/

/-- Every element of the fraction field of a field is a constant. -/
theorem surjective_algebraMap_fractionRing_self {M : Type*} [Field M] :
    Function.Surjective (algebraMap M (FractionRing M)) := by
  intro z
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors M) z
  have hs0 : (s : M) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
  have hmap0 : (algebraMap M (FractionRing M) (s : M)) ≠ 0 :=
    fun h => hs0 (IsFractionRing.injective M (FractionRing M) (by simpa using h))
  refine ⟨m / (s : M), ?_⟩
  rw [map_div₀, div_eq_iff hmap0]
  exact hs.symm

/-- `Frac M[X_0]`, i.e. the fraction field of the constant polynomial ring, is `M` itself. -/
theorem surjective_algebraMap_mvPoly_zero {M : Type*} [Field M] :
    Function.Surjective (algebraMap M (FractionRing (MvPolynomial (Fin 0) M))) := by
  intro z
  have e : FractionRing (MvPolynomial (Fin 0) M) ≃ₐ[M] FractionRing M :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.isEmptyAlgEquiv M (Fin 0))
  obtain ⟨c, hc⟩ := surjective_algebraMap_fractionRing_self (e z)
  refine ⟨c, ?_⟩
  exact e.injective (by rw [e.commutes, hc])

/-! ## §2 Base change for the fraction field of a polynomial ring -/

/-- **Base change.**  For a domain `A` over `𝕜`, the fraction field of `A[X]` is the fraction field
of `(Frac A)[X]`.

Route: `A[X] → (Frac A)[X] → Frac((Frac A)[X])` exhibits `Frac((Frac A)[X])` as a localization of
`A[X]` at the pullback of the non-zero-divisors of `(Frac A)[X]`, which is exactly the set of
non-zero-divisors of `A[X]`; hence both `Frac A[X]` and `Frac((Frac A)[X])` are fraction rings of
`A[X]` and `IsLocalization.algEquiv` compares them. -/
theorem ratFunc_fractionRing {𝕜 A : Type*} [Field 𝕜] [CommRing A] [IsDomain A] [Algebra 𝕜 A] :
    Nonempty (FractionRing (Polynomial A) ≃ₐ[𝕜] RatFunc (FractionRing A)) := by
  letI : Algebra (Polynomial A) (Polynomial (FractionRing A)) :=
    Polynomial.algebra A (FractionRing A)
  haveI hloc : IsLocalization ((nonZeroDivisors A).map Polynomial.C)
      (Polynomial (FractionRing A)) :=
    Polynomial.isLocalization (nonZeroDivisors A) (FractionRing A)
  have hcomap : Submonoid.comap (algebraMap (Polynomial A) (Polynomial (FractionRing A)))
      (nonZeroDivisors (Polynomial (FractionRing A))) = nonZeroDivisors (Polynomial A) := by
    ext f
    simp only [Submonoid.mem_comap]
    rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
    exact Polynomial.map_ne_zero_iff (IsFractionRing.injective A (FractionRing A))
  have hT : IsLocalization (Submonoid.comap (algebraMap (Polynomial A) (Polynomial (FractionRing A)))
      (nonZeroDivisors (Polynomial (FractionRing A)))) (RatFunc (FractionRing A)) :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      ((nonZeroDivisors A).map Polynomial.C) (nonZeroDivisors (Polynomial (FractionRing A)))
      (RatFunc (FractionRing A)) (fun x hx => hx.mem_nonZeroDivisors)
  haveI : IsLocalization (nonZeroDivisors (Polynomial A)) (RatFunc (FractionRing A)) :=
    hcomap ▸ hT
  exact ⟨(IsLocalization.algEquiv (nonZeroDivisors (Polynomial A))
    (FractionRing (Polynomial A)) (RatFunc (FractionRing A))).restrictScalars 𝕜⟩

/-! ## §3 The tower step -/

/-- **The tower step.**  `Frac F[x_0,…,x_n] ≅ RatFunc (Frac F[x_0,…,x_{n-1}])` as
`F`-algebras.

Route: `MvPolynomial.finSuccEquiv` identifies the polynomial ring with `(MvPolynomial (Fin n))[X]`,
and `ratFunc_fractionRing` performs the base change.  The result is an `F`-algebra equivalence, so
that the transport of constants in `fracMvPoly_cancel` is compatible with `algebraMap F`. -/
theorem fracMvPoly_succ_ratFunc {F : Type*} [Field F] (n : ℕ) :
    Nonempty (FractionRing (MvPolynomial (Fin (n + 1)) F) ≃ₐ[F]
      RatFunc (FractionRing (MvPolynomial (Fin n) F))) := by
  obtain ⟨e1⟩ : Nonempty (FractionRing (MvPolynomial (Fin (n + 1)) F) ≃ₐ[F]
      FractionRing (Polynomial (MvPolynomial (Fin n) F))) :=
    ⟨IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.finSuccEquiv F n)⟩
  obtain ⟨e2⟩ : Nonempty (FractionRing (Polynomial (MvPolynomial (Fin n) F)) ≃ₐ[F]
      RatFunc (FractionRing (MvPolynomial (Fin n) F))) :=
    ratFunc_fractionRing (𝕜 := F) (A := MvPolynomial (Fin n) F)
  exact ⟨e1.trans e2⟩

/-! ## §4 Algebraicity helpers -/

/-- Algebraicity over `R` descends along an injective `S`-algebra map `S → A` (where `S` is an
`R`-algebra): if `algebraMap S A c` is algebraic over `R` then so is `c`. -/
theorem isAlgebraic_of_isAlgebraic_algebraMap {R S A : Type*} [CommRing R] [CommRing S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (hinj : Function.Injective (algebraMap S A)) {c : S}
    (hc : IsAlgebraic R (algebraMap S A c)) : IsAlgebraic R c := by
  obtain ⟨p, hp, hp0⟩ := hc
  refine ⟨p, hp, ?_⟩
  have h := Polynomial.aeval_algebraMap_apply A c p
  rw [hp0] at h
  exact hinj (by rw [h.symm, map_zero])

/-- Algebraicity over `R` transports along an `S`-algebra map `S → A` (with `S` an `R`-algebra). -/
theorem isAlgebraic_algebraMap_of_isAlgebraic {R S A : Type*} [CommRing R] [CommRing S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {c : S}
    (hc : IsAlgebraic R c) : IsAlgebraic R (algebraMap S A c) :=
  hc.algHom (IsScalarTower.toAlgHom R S A)

end

end Work.MotV5
