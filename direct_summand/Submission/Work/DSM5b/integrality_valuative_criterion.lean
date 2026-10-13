import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.isIntegralElem_range_subtype
import Submission.Work.DSM5b.exists_isPrime_quotient_not_isIntegral

/-!
# The valuative criterion for integrality of an element

For an `R`-algebra `S` and `x : S`, the element `x` is integral over `R` if and only if for every
valuation ring `A` with fraction field `K`, every ring map `φ : R →+* A` and every ring map
`ψ : S →+* K` compatible with the `R`-algebra structures, the value `ψ x` lies in the image of `A`.

* The forward direction is `IsIntegral.map_of_comp_eq` (integrality is transported along a
  compatible pair of ring maps), together with the fact that a valuation ring is integrally closed
  in its fraction field (`IsIntegrallyClosedIn A K`, inferred from `IsDomain A`, `ValuationRing A`
  and `IsFractionRing A K`).

* The converse is proved contrapositively.  Given `x` that is not integral over `R`:
  1. (`Work.DSM5b.exists_isPrime_quotient_not_isIntegral`) there is a prime ideal `P ⊆ S` such that
     the image of `x` in the domain `S ⧸ P` is still not integral over `R`;
  2. (`Work.DSM5b.exists_counterexample_of_not_isIntegralElem_domain`) in the case of a *domain*, a
     non-integral element is excluded by a valuation subring of the fraction field: this uses
     `Work.DSM5b.isIntegralElem_range_subtype` to compare integrality over `f` with integrality over
     the image `f.range`, and then `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`
     applied to the integral closure of `f.range` in the fraction field.
-/

set_option linter.style.haveILetI false

namespace Work.DSM5b

universe u

/-! ## Separating a non-integral element by a valuation subring (field case) -/

/-- If `y` is not integral over `f : R →+* F` with `F` a field, then some valuation subring of `F`
contains the image of `f` but not `y`.  This is the valuative form of the statement that the
integral closure of `f.range` in `F` is the intersection of the valuation subrings of `F`
containing `f.range` (`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`). -/
theorem exists_valuationSubring_notMem_of_not_isIntegralElem {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) {y : F} (hy : ¬ f.IsIntegralElem y) :
    ∃ V : ValuationSubring F, f.range ≤ V.toSubring ∧ y ∉ V := by
  have hmem : y ∉ (integralClosure f.range F).toSubring := by
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact fun h => hy ((isIntegralElem_range_subtype f y).mpr h)
  have hle : f.range ≤ (integralClosure f.range F).toSubring := by
    intro z hz
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := f.range) (A := F) (x := ⟨z, hz⟩)
  obtain ⟨V, hV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hmem
  exact ⟨V, hle.trans hV, hyV⟩

/-! ## The domain case of the converse -/

/-- **The converse of the valuative criterion, in the case of a domain.**  If `x : D` is not
integral over `f : R →+* D` with `D` a domain, then, writing `F = FractionRing D`, there is a
valuation subring `V ≤ F` containing the image of `f` and with `x ∉ V`; this is exactly the
counterexample to the valuative criterion. -/
theorem exists_counterexample_of_not_isIntegralElem_domain {R D : Type*} [CommRing R] [CommRing D]
    [IsDomain D] (f : R →+* D) (x : D) (hx : ¬ f.IsIntegralElem x) :
    ∃ (V : ValuationSubring (FractionRing D)) (φ : R →+* V) (ψ : D →+* FractionRing D),
      (algebraMap V (FractionRing D)).comp φ = ψ.comp f ∧
        ¬ ∃ a : V, ψ x = algebraMap V (FractionRing D) a := by
  let F := FractionRing D
  let j : D →+* F := algebraMap D F
  have hinj : Function.Injective j := IsFractionRing.injective D F
  have hβ : ¬ (j.comp f).IsIntegralElem (j x) := by
    rintro ⟨p, hp, hpx⟩
    refine hx ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂ p f j x, map_zero]
    exact hpx
  obtain ⟨V, hV, hyV⟩ := exists_valuationSubring_notMem_of_not_isIntegralElem (j.comp f) hβ
  have hcod : ∀ r, (j.comp f) r ∈ V.toSubring := fun r => hV (RingHom.mem_range_self (j.comp f) r)
  refine ⟨V, (j.comp f).codRestrict V.toSubring hcod, j, ?_, ?_⟩
  · ext r
    exact RingHom.codRestrict_apply (j.comp f) V.toSubring hcod r
  · rintro ⟨a, ha⟩
    exact hyV (ha ▸ a.2)

/-- **Valuative criterion for integrality of an element.**  For an `R`-algebra `S` and `x : S`, the
element `x` is integral over `R` if and only if for every valuation ring `A` with fraction field `K`,
every ring map `φ : R →+* A` and every ring map `ψ : S →+* K` compatible with the `R`-algebra
structures, the value `ψ x` lies in (the image of) `A`.

(The forward direction: `ψ x` is integral over `φ R ⊆ A`, and `A` is integrally closed in `K`.
The converse: Zorn/maximal-ideal reduction of `S` to a domain, then
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`.) -/
theorem integrality_valuative_criterion (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : S) :
    IsIntegral R x ↔
      ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (K : Type u) [Field K]
        [Algebra A K] [IsFractionRing A K] (φ : R →+* A) (ψ : S →+* K),
        ψ.comp (algebraMap R S) = (algebraMap A K).comp φ →
          ∃ a : A, ψ x = algebraMap A K a := by
  constructor
  · intro hx A _ _ _ K _ _ _ φ ψ hφψ
    have h1 : IsIntegral A (ψ x) := IsIntegral.map_of_comp_eq φ ψ hφψ.symm hx
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := A) (A := K) h1
    exact ⟨a, ha.symm⟩
  · intro H
    by_contra hx
    obtain ⟨P, hP, hPx⟩ := exists_isPrime_quotient_not_isIntegral x hx
    haveI : P.IsPrime := hP
    let f : R →+* (S ⧸ P) := (Ideal.Quotient.mk P).comp (algebraMap R S)
    have hf : ¬ f.IsIntegralElem (Ideal.Quotient.mk P x) := hPx
    obtain ⟨V, φ, ψ, hcompat, hbad⟩ :=
      exists_counterexample_of_not_isIntegralElem_domain f (Ideal.Quotient.mk P x) hf
    have hcompat' : (ψ.comp (Ideal.Quotient.mk P)).comp (algebraMap R S) =
        (algebraMap V (FractionRing (S ⧸ P))).comp φ := by
      rw [RingHom.comp_assoc]
      exact hcompat.symm
    exact hbad (H V (FractionRing (S ⧸ P)) φ (ψ.comp (Ideal.Quotient.mk P)) hcompat')

end Work.DSM5b
