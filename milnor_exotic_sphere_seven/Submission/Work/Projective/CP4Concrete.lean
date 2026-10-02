import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.Model
import Submission.Work.Projective.t2Space_CP
import Submission.Work.Projective.cpn_cohomology
import Submission.Work.Projective.cpn_homology
import Submission.Work.Projective.Interface
import Submission.Work.Projective.CP2Concrete

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `ℂP⁴` in the cochain model: the model `SSet`, its cohomology and homology isomorphisms

The `n = 4` companion of `Submission/Work/Projective/CP2Concrete.lean`, built on the additive
computations `Work.Projective.cpn_cohomology` and `Work.Projective.cpn_homology` (valid for every
`n`):

* `Work.Projective.cp4SSet` — the `SSet` model `TopCat.toSSet (TopCat.of (CP 4))` of `ℂP⁴`;
* `Work.Projective.cpnCohIsoInt`, `…cpnHomIsoInt` — `H^{2k}(ℂPⁿ;ℤ) ≅ ℤ` and `H_{2k}(ℂPⁿ;ℤ) ≅ ℤ`
  for `2k ≤ 2n`;
* `Work.Projective.cp4CohIso2`, `…cp4CohIso4`, `…cp4HomIso` — the degree `2`, `4` and `8` cases for
  `ℂP⁴`;
* `Work.Projective.cp4C` — a chosen generator of `H₈(ℂP⁴;ℤ) ≅ ℤ`, the fundamental class;
* `Work.Projective.cpnHomFree` — the homology of `ℂPⁿ` is degreewise free (needed for the
  universal-coefficient/Kronecker identification `Work.Cohomology.kronH_isIso`).

The multiplicative structure (`h ⌣ h` generating `H⁴(ℂP⁴;ℤ)`) is
`Work.Projective.cp4_cupSquare_generates`, and the Pontryagin numbers and the generator check are
assembled in `Submission/Work/Projective/CP4Duality.lean`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-! ## Manifold instances for the `TopCat` `CPSpace 4` -/

instance instT2SpaceCPSpaceFour : T2Space ↥(CPSpace 4) := t2Space_CP 4

instance instCompactSpaceCPSpaceFour : CompactSpace ↥(CPSpace 4) := compactSpace_CP 4

/-- The simplicial-set model of the manifold `ℂP⁴`. -/
abbrev cp4SSet : SSet := TopCat.toSSet.obj (CPSpace 4)

/-! ## The cohomology and homology of `ℂPⁿ` in even degrees -/

/-- **`H^{2k}(ℂPⁿ;ℤ) ≅ ℤ` for `2k ≤ 2n`**, from `Work.Projective.cpn_cohomology`. -/
noncomputable def cpnCohIsoInt (n k : ℕ) (h : Even k ∧ k ≤ 2 * n) :
    (cochainC ℤ (TopCat.toSSet.obj (CPSpace n))).homology k ≅ ModuleCat.of ℤ ℤ := by
  have e : (cochainC ℤ (TopCat.toSSet.obj (CPSpace n))).homology k ≅ cpnModel n k :=
    Classical.choice (cpn_cohomology n k)
  have hM : cpnModel n k = ModuleCat.of ℤ (Fin 1 → ℤ) := by
    show ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ) = _
    rw [if_pos h]
  exact e ≪≫ eqToIso hM ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- **`H_{2k}(ℂPⁿ;ℤ) ≅ ℤ` for `2k ≤ 2n`**, from `Work.Projective.cpn_homology`. -/
noncomputable def cpnHomIsoInt (n k : ℕ) (h : Even k ∧ k ≤ 2 * n) :
    (chainC ℤ (TopCat.toSSet.obj (CPSpace n))).homology k ≅ ModuleCat.of ℤ ℤ := by
  have e : (chainC ℤ (TopCat.toSSet.obj (CPSpace n))).homology k ≅
      ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ) :=
    Classical.choice (cpn_homology n k)
  have hM : ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)
      = ModuleCat.of ℤ (Fin 1 → ℤ) := by rw [if_pos h]
  exact e ≪≫ eqToIso hM ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- **The homology of `ℂPⁿ` is degreewise free**: by `cpn_homology` it is `ℤ` (free) in even
degrees and `0` otherwise. -/
theorem cpnHomFree (n k : ℕ) :
    Module.Free ℤ ↥((singularChains ℤ (CPSpace n)).homology k) := by
  by_cases h : Even k ∧ k ≤ 2 * n
  · exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ)
      (cpnHomIsoInt n k h).symm.toLinearEquiv
  · have e : (chainC ℤ (TopCat.toSSet.obj (CPSpace n))).homology k ≅
        ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ) :=
      Classical.choice (cpn_homology n k)
    haveI hA : IsZero (ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)) := by
      rw [if_neg h]
      exact ModuleCat.isZero_of_subsingleton _
    haveI : Subsingleton ↥((singularChains ℤ (CPSpace n)).homology k) :=
      ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso hA e)
    exact Module.Free.of_subsingleton ℤ ↥((singularChains ℤ (CPSpace n)).homology k)

/-! ## The degrees needed for `ℂP⁴` -/

/-- `H²(ℂP⁴;ℤ) ≅ ℤ`. -/
noncomputable def cp4CohIso2 : (cochainC ℤ cp4SSet).homology 2 ≅ ModuleCat.of ℤ ℤ :=
  cpnCohIsoInt 4 2 ⟨⟨1, by norm_num⟩, by norm_num⟩

/-- `H⁴(ℂP⁴;ℤ) ≅ ℤ`. -/
noncomputable def cp4CohIso4 : (cochainC ℤ cp4SSet).homology 4 ≅ ModuleCat.of ℤ ℤ :=
  cpnCohIsoInt 4 4 ⟨⟨2, by norm_num⟩, by norm_num⟩

/-- `H₈(ℂP⁴;ℤ) ≅ ℤ`. -/
noncomputable def cp4HomIso : (chainC ℤ cp4SSet).homology 8 ≅ ModuleCat.of ℤ ℤ :=
  cpnHomIsoInt 4 8 ⟨⟨4, by norm_num⟩, by norm_num⟩

/-- **A chosen generator of `H₈(ℂP⁴;ℤ) ≅ ℤ`**, the fundamental class of `ℂP⁴` (up to the sign,
which is fixed in `Submission/Work/Projective/CP4Duality.lean` by the normalisation
`⟨h ⌣ h  ⌣ h ⌣ h, c⟩ = 1`). -/
noncomputable def cp4C : (chainC ℤ cp4SSet).homology 8 := cp4HomIso.inv (1 : ℤ)

/-- `cp4C` generates `H₈(ℂP⁴;ℤ) ≅ ℤ`. -/
theorem cp4C_span : Submodule.span ℤ {cp4C} = ⊤ :=
  span_singleton_eq_top_of_iso cp4HomIso

end

end Work.Projective
