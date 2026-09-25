import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Existence
import Submission.NK.LocalCFT.Instance.normGroup_real_complex
import Submission.NK.LocalCFT.Instance.posSubgroup_le_of_finiteIndex
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex

/-!
# The Lubin–Tate existence theorem at the archimedean place: `LubinTateExistence ℝ ℂ`

This file discharges the chapter's input `NK.LocalReciprocityLubinTate.LubinTateExistence ℝ ℂ`
unconditionally, i.e. it exhibits the Lubin–Tate tower for the archimedean local field `ℝ` with
separable closure `ℂ`.  This is the audit witness that the chapter's hypothesis is *inhabited* —
see `Submission/Work/LocalReciprocityLubinTate/Audit/Conventions.lean`.

## The mathematics

`Gal(ℂ/ℝ) = {1, conj} ≅ ℤ/2` is commutative, so the maximal abelian subextension
`ℝ^{ab} = maxAbelianSubext ℝ ℂ` is all of `ℂ` (the commutator subgroup is trivial).  There are
therefore only two levels, `ℝ` and `ℂ`, and the whole tower degenerates:

* the uniformiser is `π = 1` (the archimedean "maximal ideal" is everything, and `1` generates it);
* the unit filtration is the constant filtration by the positive reals
  `U^n = ℝ_{>0} = N_{ℂ/ℝ} ℂˣ` (there is no ramification, so the filtration is constant);
* *every* level is `⊤ = ℂ`: the Lubin–Tate levels of the tower all collapse to the single
  quadratic extension `ℂ/ℝ`, whose norm group is `ℝ_{>0} = ⟨π^{m+1}⟩ · U^{n+1}`;
* cofinality holds because every finite-index subgroup of `ℝˣ` contains the divisible group
  `ℝ_{>0}` (`NK.LocalCFT.Instance.posSubgroup_le_of_finiteIndex`).

So the Lubin–Tate existence theorem holds at `ℝ ⊆ ℂ`, and the chapter's reduction
`LubinTateExistence + KernelCondition + NormIndex ⟹ Nonempty (ArtinReciprocity ℝ ℂ)` is not
vacuous.
-/

open scoped Classical

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.LocalReciprocityLubinTate.Audit

noncomputable section

/-- **The Lubin–Tate existence theorem at the archimedean local field `ℝ`.**

Levels `⊤ = ℂ`, uniformiser `π = 1`, unit filtration `U^n = ℝ_{>0}`. -/
theorem lubinTateExistence_real_complex [IsGalois ℝ ℂ] :
    NK.LocalReciprocityLubinTate.LubinTateExistence ℝ ℂ := by
  -- `Gal(ℂ/ℝ)` is commutative, so the maximal abelian subextension is all of `ℂ`.
  have hM : NK.LocalReciprocity.maxAbelianSubext ℝ ℂ = ⊤ := by
    rw [NK.LocalReciprocity.maxAbelianSubext, NK.LocalCFT.Instance.commutator_galComplex,
      IntermediateField.fixedField_bot]
  -- The identification of the ambient field with `ℂ`.
  have eM : ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) ≃ₐ[ℝ] ℂ :=
    (IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv
  haveI : FiniteDimensional ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) :=
    FiniteDimensional.of_injective eM.toLinearEquiv.toLinearMap eM.toLinearEquiv.injective
  -- The top level is normal, being the whole extension `↥(maxAbelianSubext ℝ ℂ)/ℝ`.
  haveI : Normal ℝ (⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) :=
    Normal.of_algEquiv (IntermediateField.topEquiv (F := ℝ)
      (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))).symm
  -- The norm group of the single level `ℂ/ℝ` is the group of positive real units.
  have hnormTop : NK.LocalReciprocity.normGroup ℝ
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) =
      Units.posSubgroup ℝ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (IntermediateField.topEquiv (F := ℝ)
          (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))),
      NK.LocalReciprocity.normGroup_eq_of_algEquiv eM,
      NK.LocalCFT.Instance.normGroup_real_complex]
  have hfinTop : FiniteDimensional ℝ
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) :=
    FiniteDimensional.of_injective
      (IntermediateField.topEquiv (F := ℝ)
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))).toLinearEquiv.toLinearMap
      (IntermediateField.topEquiv (F := ℝ)
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))).toLinearEquiv.injective
  -- The Galois group of the top level is abelian (indeed of order two).
  have hcommTop : ∀ σ τ :
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) ≃ₐ[ℝ]
        ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)), σ * τ = τ * σ :=
    NK.LocalCFT.Instance.mul_comm_of_autCongr
      (IntermediateField.topEquiv (F := ℝ)
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)))
      (NK.LocalCFT.Instance.mul_comm_of_autCongr eM NK.LocalCFT.Instance.galComplex_mul_comm)
  -- The tower: all levels are `⊤ = ℂ`, indexed by the uniformiser `π = 1` and the constant unit
  -- filtration `U^n = ℝ_{>0}`.
  refine ⟨1, fun _ => Units.posSubgroup ℝ, 2, ⟨?_⟩, fun _ _ _ => le_refl _, ?_⟩
  · refine ⟨fun _ _ => ⊤, fun _ _ => hfinTop, fun _ _ => inferInstance,
      fun _ _ σ τ => hcommTop σ τ, ?_⟩
    · -- the norm-group description: `N_{ℂ/ℝ} ℂˣ = ⟨1^{m+1}⟩ · ℝ_{>0} = ℝ_{>0}`
      intro m n
      rw [hnormTop, one_pow, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
  · -- cofinality: `ℝ_{>0}` is contained in every finite-index subgroup of `ℝˣ`
    intro M hM'
    exact ⟨0, NK.LocalCFT.Instance.posSubgroup_le_of_finiteIndex M hM'⟩

end

end NK.LocalReciprocityLubinTate.Audit
