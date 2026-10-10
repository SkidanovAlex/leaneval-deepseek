import Mathlib
import Submission.Work.FFResidual.All
import Submission.Work.FFResidual.Geometry.isDiscreteValuationRing_of_isIntegrallyClosed_of_krullDimLE_one
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_of_algEquiv
import Submission.Work.MotR.FunctionField.hasFunctionFieldPlace_fractionRing_mvPolynomial_of_nonempty
import Submission.Work.MotR.FunctionField.nonempty_of_isTranscendenceBasis_of_exists_transcendental
import Submission.Work.MotR.FunctionField.exists_ne_bot_isPrime_integralClosure

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotR.FunctionField

set_option linter.style.haveILetI false

open IntermediateField

/-- **A function field of positive dimension over a perfect field has a place over the
constants.**

Let `K` be a field extension of a perfect field `𝔽` which is essentially of finite type over `𝔽`
(equivalently: `K` is a finitely generated field extension of `𝔽`), and suppose that `K` has a
transcendental element over `𝔽`.  Then `K` carries a discrete valuation ring `R` with `𝔽 ⊆ R`,
fraction field `K` and a uniformizer: that is, `K` has a place over `𝔽`.

The construction: choose a separating transcendence basis `s ⊆ K` (Mathlib: every essentially of
finite type extension of a perfect field is separably generated).  The subfield `L = 𝔽(s)` is a
rational function field over `𝔽`, hence has a place over `𝔽`; `K/L` is finite and separable, so
the integral closure `S` of the valuation ring of that place in `K` is a Dedekind domain with
fraction field `K`, and any nonzero prime of `S` (which exists: `S` is integral over a
one-dimensional local domain) localizes to a discrete valuation ring with fraction field `K`. -/
theorem hasFunctionFieldPlace_of_perfect_essFiniteType {𝔽 K : Type} [Field 𝔽] [Field K]
    [Algebra 𝔽 K] [PerfectField 𝔽] [Algebra.EssFiniteType 𝔽 K] (h : ∃ t : K, Transcendental 𝔽 t) :
    Work.FFResidual.HasFunctionFieldPlace 𝔽 K := by
  classical
  -- A separating transcendence basis of `K` over `𝔽`, and the subfield `L = 𝔽(s)` it generates.
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField 𝔽 K
  have hsne : s.Nonempty := nonempty_of_isTranscendenceBasis_of_exists_transcendental h hs
  haveI : Nonempty s := Finset.nonempty_coe_sort.mpr hsne
  let L : IntermediateField 𝔽 K := IntermediateField.adjoin 𝔽 (s : Set K)
  -- `K/L` is a finite separable extension.
  haveI hsepL : Algebra.IsSeparable ↥L K := hsep
  haveI hAlgL : Algebra.IsAlgebraic ↥L K := hsepL.isAlgebraic
  haveI hFinL : FiniteDimensional ↥L K := by
    have hFG : (⊤ : IntermediateField ↥L K).FG := by
      refine IntermediateField.FG.of_restrictScalars (K := 𝔽) (L := ↥L) (E := K) ?_
      rw [IntermediateField.restrictScalars_top]
      exact IntermediateField.fg_top 𝔽 K
    haveI : Algebra.EssFiniteType ↥L K := IntermediateField.fg_top_iff.mp hFG
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic
  -- `L` is a rational function field over `𝔽`, hence has a place over `𝔽`.
  have hplaceL : Work.FFResidual.HasFunctionFieldPlace 𝔽 ↥L := by
    have h0 : Work.FFResidual.HasFunctionFieldPlace 𝔽 (FractionRing (MvPolynomial s 𝔽)) :=
      hasFunctionFieldPlace_fractionRing_mvPolynomial_of_nonempty 𝔽 (σ := s)
    have hrange : Set.range (Subtype.val : s → K) = (s : Set K) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    have hEq : IntermediateField.adjoin 𝔽 (Set.range (Subtype.val : s → K)) = L := by
      rw [hrange]
    have e : FractionRing (MvPolynomial s 𝔽) ≃ₐ[𝔽] ↥L :=
      (AlgebraicIndependent.aevalEquivField hs.1).trans (IntermediateField.equivOfEq hEq)
    exact Work.FFResidual.Geometry.hasFunctionFieldPlace_of_algEquiv e h0
  obtain ⟨P⟩ := hplaceL
  letI := P.commRing
  letI := P.isDomain
  letI := P.isDiscreteValuationRing
  letI := P.algebraF
  letI := P.algebraR
  letI := P.tower
  letI := P.isFractionRing
  -- `K` is an algebra over the valuation ring `P.R` of `L`, through `L`.
  letI : Algebra P.R K := RingHom.toAlgebra ((algebraMap ↥L K).comp (algebraMap P.R ↥L))
  haveI hTowR : IsScalarTower P.R ↥L K :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hTowFK : IsScalarTower 𝔽 P.R K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap 𝔽 K x = algebraMap ↥L K (algebraMap P.R ↥L (algebraMap 𝔽 P.R x))
      rw [← IsScalarTower.algebraMap_apply 𝔽 P.R ↥L, ← IsScalarTower.algebraMap_apply 𝔽 ↥L K]
  -- The integral closure `S` of `P.R` in `K`: a Dedekind domain with fraction field `K`.
  let S : Subalgebra P.R K := integralClosure P.R K
  haveI : IsDedekindDomain ↥S := integralClosure.isDedekindDomain P.R ↥L K
  haveI : IsFractionRing ↥S K := integralClosure.isFractionRing_of_finite_extension ↥L K
  -- A nonzero prime of `S`.
  have hinjPRK : Function.Injective (algebraMap P.R K) := by
    have h1 : Function.Injective (algebraMap P.R ↥L) := IsFractionRing.injective P.R ↥L
    have h2 : Function.Injective (algebraMap ↥L K) := by
      intro x y hxy
      exact Subtype.ext hxy
    exact h2.comp h1
  have hmax : ∃ p : Ideal P.R, p ≠ ⊥ ∧ p.IsPrime :=
    ⟨IsLocalRing.maximalIdeal P.R, IsDiscreteValuationRing.not_a_field P.R,
      (IsLocalRing.maximalIdeal.isMaximal P.R).isPrime⟩
  obtain ⟨Q, hQne, hQprime⟩ := exists_ne_bot_isPrime_integralClosure hinjPRK hmax
  haveI : Q.IsPrime := hQprime
  -- The localization of `S` at `Q`, viewed inside `K`, is a discrete valuation ring with
  -- fraction field `K`.
  let R : Subalgebra ↥S K :=
    Localization.subalgebra.ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing ↥R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥S hQne ↥R
  letI : Algebra 𝔽 ↥S := RingHom.toAlgebra ((algebraMap P.R ↥S).comp (algebraMap 𝔽 P.R))
  haveI : IsScalarTower 𝔽 ↥S K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap 𝔽 K x = algebraMap ↥S K (algebraMap P.R ↥S (algebraMap 𝔽 P.R x))
      rw [← IsScalarTower.algebraMap_apply P.R ↥S K, ← IsScalarTower.algebraMap_apply 𝔽 P.R K]
  letI : Algebra 𝔽 ↥R := RingHom.toAlgebra ((algebraMap ↥S ↥R).comp (algebraMap 𝔽 ↥S))
  haveI : IsScalarTower 𝔽 ↥R K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap 𝔽 K x = algebraMap ↥R K (algebraMap ↥S ↥R (algebraMap 𝔽 ↥S x))
      rw [← IsScalarTower.algebraMap_apply ↥S ↥R K, ← IsScalarTower.algebraMap_apply 𝔽 ↥S K]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥R
  exact ⟨{ R := ↥R, π := π, isUniformizer := hπ.maximalIdeal_eq }⟩

end Work.MotR.FunctionField
