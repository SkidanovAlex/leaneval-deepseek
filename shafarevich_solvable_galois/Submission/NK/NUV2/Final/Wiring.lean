import Mathlib
import Submission.NK.NUV2.RouteE.assembly
import Submission.NK.NUV2.RouteE.levelCompat
import Submission.NK.NUV2.RouteE.levelCoherent
import Submission.NK.NUV2.RouteE.levelH2
import Submission.NK.NUV2.RouteE.levelArtinMap
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The final wiring: a coherent family of fundamental classes with L7 gives the local reciprocity law

This file assembles the character-formula route:

* the coherent family of fundamental classes (König, `L3`), as a hypothesis `hfamily`;
* the kernel/surjectivity of the level symbols (L7), as a hypothesis `hker`;
* the proved compatibility (L5, `NK.NUV2.RouteE.levelSymbol_restrict`);
* the proved assembly (`NK.NUV2.RouteE.nonempty_kernelCondition_of_levelMaps`),

into `Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K) (SeparableClosure _))`, which
is the deliverable `NK.NUV2.kernelCondition_all`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory

namespace NK.NUV2.Final

/-- **The local reciprocity law in kernel form from the coherent family (L3) and L7.** -/
theorem nonempty_kernelCondition_of_family
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hfamily : ∃ (u : (L : FiniteGaloisIntermediateField (Q.adicCompletion K)
            (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
              (SeparableClosure (Q.adicCompletion K)))) →
          groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)
        (_hu : ∀ L, addOrderOf (u L) = Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)),
        ∀ (L E : FiniteGaloisIntermediateField (Q.adicCompletion K)
            (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
              (SeparableClosure (Q.adicCompletion K)))) (h : L ≤ E),
          (NK.NUV2.RouteE.levelInfHom L E h) (u L)
            = ((Nat.card (↥E ≃ₐ[(Q.adicCompletion K)] ↥E)
                / Nat.card (↥L ≃ₐ[(Q.adicCompletion K)] ↥L) : ℕ) : ℤ) • (u E))
    (hker : ∀ (L : IntermediateField (Q.adicCompletion K)
          (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K))))
        [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L]
        [Finite (groupCohomology
          (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)]
        (hcomm : ∀ σ τ : ↥L ≃ₐ[(Q.adicCompletion K)] ↥L, σ * τ = τ * σ)
        (u : groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)
        (hu : addOrderOf u = Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)),
        MonoidHom.ker (NK.NUV2.RouteE.levelSymbol hcomm u hu)
            = NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L ∧
          Function.Surjective (NK.NUV2.RouteE.levelSymbol hcomm u hu)) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  classical
  obtain ⟨u, hu, hcompatFamily⟩ := hfamily
  have hfin : ∀ (L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))))
      [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L],
      Finite (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2) := fun L _ _ => by
    haveI : IsGalois (Q.adicCompletion K) ↥L := NK.NUV2.RouteE.isGalois_level Q L
    exact Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
      (Q := Q) (F := Q.adicCompletion K) (E := ↥L)
      (Group.isSolvable_of_comm (NK.LocalCFT.Reduction.commutative_level L))
  -- the level symbol at each level, from the coherent family
  let th : ∀ (L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))))
      [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L]
      (_ : ∀ σ τ : ↥L ≃ₐ[(Q.adicCompletion K)] ↥L, σ * τ = τ * σ),
      (Q.adicCompletion K)ˣ →* (↥L ≃ₐ[(Q.adicCompletion K)] ↥L) :=
    fun L _ _ hcomm => by
      haveI : IsGalois (Q.adicCompletion K) ↥L := NK.NUV2.RouteE.isGalois_level Q L
      haveI : Finite (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2) := hfin L
      exact NK.NUV2.RouteE.levelSymbol hcomm (u ⟨L⟩) (hu ⟨L⟩)
  refine NK.NUV2.RouteE.nonempty_kernelCondition_of_levelMaps
    (F := Q.adicCompletion K)
    (F' := SeparableClosure (Q.adicCompletion K)) th ?_ ?_ ?_
  · intro L hfd hnorm hcomm
    haveI : IsGalois (Q.adicCompletion K) ↥L := NK.NUV2.RouteE.isGalois_level Q L
    exact (@hker L hfd hnorm (hfin L) hcomm (u ⟨L⟩) (hu ⟨L⟩)).1
  · intro L hfd hnorm hcomm
    haveI : IsGalois (Q.adicCompletion K) ↥L := NK.NUV2.RouteE.isGalois_level Q L
    exact (@hker L hfd hnorm (hfin L) hcomm (u ⟨L⟩) (hu ⟨L⟩)).2
  · intro L₁ L₂ hfd₁ hnorm₁ hfd₂ hnorm₂ h₁ h₂ h a
    haveI : IsGalois (Q.adicCompletion K) ↥L₁ := NK.NUV2.RouteE.isGalois_level Q L₁
    haveI : IsGalois (Q.adicCompletion K) ↥L₂ := NK.NUV2.RouteE.isGalois_level Q L₂
    letI : Algebra ↥L₂ ↥L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
    haveI : IsScalarTower (Q.adicCompletion K) ↥L₂ ↥L₁ :=
      IsScalarTower.of_algebraMap_eq (congrFun rfl)
    haveI hfin₁ : Finite (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₁) 2) := hfin L₁
    haveI hfin₂ : Finite (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₂) 2) := hfin L₂
    -- the cardinality of `H²` is the cardinality of the level's Galois group (L1)
    have hc₁ : Nat.card (↥L₁ ≃ₐ[(Q.adicCompletion K)] ↥L₁) = Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₁) 2) := by
      rw [IsGalois.card_aut_eq_finrank]
      exact ((NK.NUV2.RouteE.h2_cyclic_level (Q := Q) (F := Q.adicCompletion K)
        (E := ↥L₁) h₁).1).symm
    have hc₂ : Nat.card (↥L₂ ≃ₐ[(Q.adicCompletion K)] ↥L₂) = Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₂) 2) := by
      rw [IsGalois.card_aut_eq_finrank]
      exact ((NK.NUV2.RouteE.h2_cyclic_level (Q := Q) (F := Q.adicCompletion K)
        (E := ↥L₂) h₂).1).symm
    have hdvd : Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₂) 2)
        ∣ Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₁) 2) := by
      rw [← hc₁, ← hc₂, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      exact ⟨Module.finrank ↥L₂ ↥L₁,
        (Module.finrank_mul_finrank (Q.adicCompletion K) ↥L₂ ↥L₁).symm⟩
    -- the coherence relation for the family
    have hfam := hcompatFamily ⟨L₂⟩ ⟨L₁⟩
      ((FiniteGaloisIntermediateField.le_iff (k := Q.adicCompletion K) _ _).mpr h)
    have hcoh : (NK.NUV2.RouteC.levelInfMap (F := Q.adicCompletion K)
          (M := ↥L₂) (L := ↥L₁)) (u ⟨L₂⟩)
        = ((Nat.card (groupCohomology
              (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₁) 2)
            / Nat.card (groupCohomology
              (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L₂) 2) : ℕ) : ℤ) • (u ⟨L₁⟩) := by
      rw [← hc₁, ← hc₂]
      exact hfam
    exact NK.NUV2.RouteE.levelSymbol_restrict (F := Q.adicCompletion K) h₂ h₁
      (u ⟨L₂⟩) (hu ⟨L₂⟩) (u ⟨L₁⟩) (hu ⟨L₁⟩) hdvd hcoh a

end NK.NUV2.Final
