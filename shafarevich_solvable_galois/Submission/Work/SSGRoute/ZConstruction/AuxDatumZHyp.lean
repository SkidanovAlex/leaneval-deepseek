import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.ZDataInduction
import Submission.Work.SSGRoute.ZConstruction.AuxDatumRealisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Piece (c) of the section-4 level step: the `ZHyp` clauses of the auxiliary datum from the
prescriptions alone

`Work.SSGRoute.AuxDatumRealisation` (`ZConstruction/AuxDatumRealisation.lean`) asks for a class `yAux`
satisfying `Work.SSGRoute.ZHyp` at the enlarged pair `(N, S')` and the two prescriptions

* agreement with the line component `y₁` on the local groups of the places of `cs(S)`,
* vanishing on the local groups of the places of `cs(S') ∖ cs(S)`.

Of the six clauses of `ZHyp K N S'`, four are either verbatim hypotheses of the realisation
(additivity, local constancy, the unramifiedness `hyS` at `(N,S')`, which is the *primal condition*
of the realisation at the level `N`, and the killing of the involutions) or derived here.  This file
supplies the derivation of the remaining two:

* `hyT` at `(N, S')` -- `yAux` kills the inertia of every place of `cs(S')`: at a place of `cs(S)` this
  is the prescribed agreement together with `hyT` of `y₁` at `(Λ, S)`, and at a place of
  `cs(S') ∖ cs(S)` it is the prescribed vanishing;
* `hy0` at `(N, S')` -- the same splitting, with `hy0` of `y₁` at `(Λ, S)`.

Note that no relation between `Λ` and `N` is needed for this step, and none between `S` and `S'`:
the two clauses are *consequences* of the prescriptions (this is the same derivation as in the proof
of `Work.SSGRoute.auxExists_of_weakened`, extracted as a standalone lemma).
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The datum conditions of the auxiliary class, from the two prescriptions.**

Let `y₁` satisfy the hypotheses `ZHyp` of the target theorem at the pair `(Λ, S)`, and let `yAux`
agree with `y₁` on the level-`K` local group of every place of `cs(S)` and vanish on the local group
of every finite place of `cs(S') ∖ cs(S)`.  If in addition `yAux` is additive and locally constant on
`G_K`, kills the involutions of `G_K`, and is unramified outside the `S'`-classes at the places that
are not split in `N`, then `yAux` satisfies `ZHyp` at the pair `(N, S')`.

The last clause (`hyS` at `(N,S')`) is the primal condition of the realisation of the datum; the
clauses `hyT` and `hy0` are derived here. -/
theorem zHyp_of_prescribed_localData {S S' : Finset (ValuationSubring Ω)}
    {y₁ yAux : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hy₁ : ZHyp (p := p) K Λ S y₁)
    (hadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yAux (g * h) = yAux g + yAux h)
    (hloc : SSGRoute.IsLocConstOn K.fixingSubgroup yAux)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0)
    (hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → yAux c = 0)
    (hagree : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ)
    (hvan : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0) :
    ZHyp (p := p) K N S' yAux := by
  have hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0 := by
    intro B hB hconj σ hσK hσI
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
      exact hy₁.hyT B hB hconjS σ hσK hσI
    · rw [hvan B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
  have hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → yAux σ = 0 := by
    intro B hB hconj hbad σ hσK hσd
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
      exact hy₁.hy0 B hB hconjS hbad σ hσK hσd
    · rw [hvan B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
  exact ⟨hadd, hloc, hyS, hyT, hy0, hinf⟩

end Work.SSGRoute
