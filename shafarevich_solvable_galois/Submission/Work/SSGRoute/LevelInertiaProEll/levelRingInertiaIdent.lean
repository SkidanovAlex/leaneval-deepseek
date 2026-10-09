import Mathlib
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.Work.SSGRoute.LevelInertiaProEll.stabilizerValuationSubringAtPrime
import Submission.Work.SSGRoute.LevelInertiaProEll.idealInertiaValuationBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition and inertia subgroups of a level in local terms

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` over `k` and a finite
normal level `M ⊆ Ω` which is a number field, put `B := A ∩ M = A.comap (algebraMap ↥M Ω)` (a
valuation subring of `↥M`) and let `P` be the prime of `𝓞 ↥M` cut out by `A`
(`Work.SSGRoute.levelPrime k Ω A hA M`).

This file proves

* `B.decompositionSubgroup k = MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal` — the elements of
  `Gal(M/k)` stabilising the local ring `B` are exactly those stabilising the prime ideal `P`
  (Mathlib's `decompositionSubgroup` is by definition the stabiliser of the valuation subring,
  so this identifies it with the classical, ideal-theoretic decomposition group);
* `(B.inertiaSubgroup k).map (B.decompositionSubgroup k).subtype = Ideal.inertia Gal(M/k) P.asIdeal`
  — the kernel of the action of the decomposition group on the residue field of `B`
  (Mathlib's `inertiaSubgroup`) is exactly the ideal-theoretic inertia subgroup of `P`.

Both are the dictionary between the valuation-theoretic (`ValuationSubring`) and the
ideal-theoretic (`Ideal.inertia`) descriptions of ramification at a finite level, and are the
input for the "the inertia subgroup of the decomposition group is pro-`ℓ`" development
(`Submission/Work/SSGRoute/LevelInertiaProEll/levelRingUniformizerData.lean` and below).

The two mathematical inputs are proved in the sibling files:

* `stabilizerValuationSubringAtPrime` — the stabiliser of `valuationSubringAtPrime L P` is the
  stabiliser of `P.asIdeal`, for a finite Galois extension `L/K` of number fields;
* `idealInertiaValuationBridge` — on the local ring `𝒪_{L,P}`, acting trivially modulo its maximal
  ideal (equivalently, on its residue field) is the same as acting trivially modulo `P` on `𝓞 L`.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.LevelInertiaProEll

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The inertia subgroup of the local ring at `P` is the ideal inertia of `P`.**

For a finite normal level `M/k` and a prime `P` of `𝓞 ↥M`, the image in `Gal(M/k)` of the kernel
of the action of the decomposition subgroup of the local ring `𝒪_{M,P}` on its residue field is
the ideal-theoretic inertia subgroup of `P`. -/
private theorem inertiaSubgroup_map_subtype_eq_idealInertia
    {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M)) :
    ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).inertiaSubgroup k).map
        ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).decompositionSubgroup
          k).subtype
      = Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
  classical
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  set B : ValuationSubring ↥M :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P with hB
  have hD : B.decompositionSubgroup k = MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
    rw [hB]; exact stabilizerValuationSubringAtPrime P
  -- The elementwise dictionary: for `σ` in the decomposition subgroup of `B`, acting trivially on
  -- the residue field of `B` is the same as acting trivially modulo `P` on `𝓞 ↥M`.
  have key : ∀ σ : B.decompositionSubgroup k,
      σ ∈ B.inertiaSubgroup k ↔
        (σ : ↥M ≃ₐ[k] ↥M) ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
    intro σ
    have hσstab : (σ : ↥M ≃ₐ[k] ↥M) ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      rw [← hD]; exact σ.2
    have hspecσ : (σ : ↥M ≃ₐ[k] ↥M) • P.asIdeal = P.asIdeal :=
      MulAction.mem_stabilizer_iff.mp hσstab
    -- `G_0` of the ramification filtration is the inertia subgroup of a valuation subring.
    have h1 : σ ∈ B.inertiaSubgroup k ↔
        ∀ x : B, σ • x - x ∈ IsLocalRing.maximalIdeal B := by
      rw [← NK.Ramification.ramificationSubgroup_zero (K := k) B]
      simpa using (NK.Ramification.mem_ramificationSubgroup_iff B 0 σ)
    have h2 : (σ : ↥M ≃ₐ[k] ↥M) ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal ↔
        ∀ x : 𝓞 ↥M, (σ : ↥M ≃ₐ[k] ↥M) • x - x ∈ P.asIdeal :=
      AddSubgroup.mem_inertia
    -- The maximal ideal of `B` is described by the `P`-adic valuation, which is equivalent to the
    -- canonical valuation of the valuation subring `B`.
    have hequiv : B.valuation.IsEquiv (IsDedekindDomain.HeightOneSpectrum.valuation ↥M P) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr (by
        rw [ValuationSubring.valuationSubring_valuation,
          ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring])
    have hval : ∀ y : B, σ • y - y ∈ IsLocalRing.maximalIdeal B ↔
        (IsDedekindDomain.HeightOneSpectrum.valuation ↥M P)
          ((σ : ↥M ≃ₐ[k] ↥M) (y : ↥M) - (y : ↥M)) < 1 := by
      intro y
      rw [ValuationSubring.valuation_lt_one_iff]
      rw [show ((σ • y - y : B) : ↥M) =
          (σ : ↥M ≃ₐ[k] ↥M) (y : ↥M) - (y : ↥M) from by
        simp [NK.Ramification.coe_smul]]
      exact hequiv.lt_one_iff_lt_one
    have hbridge := idealInertiaValuationBridge (K := k) (L := ↥M) P (σ : ↥M ≃ₐ[k] ↥M) hspecσ
    rw [h1, h2]
    simp only [hval]
    exact hbridge.symm
  have hKeq : B.inertiaSubgroup k =
      (Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal).subgroupOf (B.decompositionSubgroup k) := by
    ext σ
    rw [Subgroup.mem_subgroupOf]
    exact key σ
  rw [hKeq, AddSubgroup.subgroupOf_inertia, AddSubgroup.inertia_map_subtype, hD]
  exact inf_eq_left.mpr (Ideal.inertia_le_stabilizer P.asIdeal)

theorem levelRingInertiaIdent
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k =
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) ∧
    (((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype =
      Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) := by
  classical
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- `A ∩ M` is the localisation of `𝓞 ↥M` at the level prime `P`
  have hspec : A.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
        (Work.SSGRoute.levelPrime k Ω A hA M) :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hA M)
  have hgoal := inertiaSubgroup_map_subtype_eq_idealInertia M
    (Work.SSGRoute.levelPrime k Ω A hA M)
  constructor
  · rw [hspec]
    exact stabilizerValuationSubringAtPrime (Work.SSGRoute.levelPrime k Ω A hA M)
  · rwa [← hspec] at hgoal

end Work.SSGRoute.LevelInertiaProEll
