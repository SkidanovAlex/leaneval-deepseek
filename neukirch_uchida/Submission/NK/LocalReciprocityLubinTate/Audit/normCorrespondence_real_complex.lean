import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormCorrespondence
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex

/-!
# Audit: Hasse's *Normensatz* at the archimedean place, `NormCorrespondence ℝ ℂ`

`NK.LocalReciprocityLubinTate.NormCorrespondence F F'` is the norm-subgroup correspondence of
local class field theory in the form in which the Lubin–Tate chapter consumes it: for finite
abelian levels `L₁, L₂ ≤ F^{ab}`,

  `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ → L₂ ≤ L₁`.

The purpose of this file is the audit witness that this hypothesis is *inhabited*, i.e. that the
statement is not vacuous: we prove it unconditionally for the archimedean local field `ℝ` with
separable closure `ℂ` (from `[IsSepClosure ℝ ℂ]`).  This complements
`NK.LocalReciprocityLubinTate.Audit.lubinTateExistence_real_complex` (the corresponding audit of
`LubinTateExistence ℝ ℂ`).

## The mathematics

`Gal(ℂ/ℝ) ≅ ℤ/2` is commutative, so the maximal abelian subextension `ℝ^{ab}` is all of `ℂ`, and
the intermediate fields of `ℂ/ℝ` that are finite over `ℝ` are only `ℝ` and `ℂ` (degree `2` is
prime).  The norm groups of the two levels are computed independently:

* `N_{ℝ/ℝ} ℝˣ = ℝˣ` (the norm map of the identity extension is the identity), and
* `N_{ℂ/ℝ} ℂˣ = ℝ_{>0}` (`Algebra.norm ℝ` is the squared modulus on `ℂ`).

Since `-1 ∈ ℝˣ` but `-1 ∉ ℝ_{>0}`, a containment of norm groups can only happen in the three cases
in which the field containment `L₂ ≤ L₁` also holds: `L₂ = ℝ` (trivial), or `L₁ = ℂ` (trivial), or
`L₁ = L₂`.  Note that the proof does *not* go through the Artin reciprocity datum: it is a direct
computation with the two levels.
-/

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Audit

noncomputable section

theorem normCorrespondence_real_complex [IsSepClosure ℝ ℂ] :
    NK.LocalReciprocityLubinTate.NormCorrespondence ℝ ℂ := by
  -- `Gal(ℂ/ℝ)` is commutative, so the maximal abelian subextension is all of `ℂ`.
  have hM : NK.LocalReciprocity.maxAbelianSubext ℝ ℂ = ⊤ := by
    rw [NK.LocalReciprocity.maxAbelianSubext, NK.LocalCFT.Instance.commutator_galComplex,
      IntermediateField.fixedField_bot]
  -- The identification of the ambient field `ℝ^{ab}` with `ℂ`.
  have eM : ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) ≃ₐ[ℝ] ℂ :=
    (IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv
  have hfinM : Module.finrank ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) = 2 :=
    eM.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex
  -- **The norm group of the bottom level.**  `⊥ = ℝ` sits in `ℝ^{ab} = ℂ`; its norm group in `ℝˣ`
  -- is everything, because the norm map `ℝ → ℝ` of the identity extension is the identity.
  have hnormBot : NK.LocalReciprocity.normGroup ℝ
      ↥(⊥ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) = ⊤ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (IntermediateField.botEquiv ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)),
      NK.LocalReciprocity.normGroup, Algebra.norm_self, Units.map_id, MonoidHom.range_eq_top]
    intro x
    exact ⟨x, rfl⟩
  -- **The norm group of the top level.**  `⊤ = ℂ` inside `ℝ^{ab} = ℂ`, whose norm group is the
  -- group of positive real units.
  have hnormTop : NK.LocalReciprocity.normGroup ℝ
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) =
      Units.posSubgroup ℝ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (IntermediateField.topEquiv (F := ℝ)
          (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))),
      NK.LocalReciprocity.normGroup_eq_of_algEquiv eM,
      NK.LocalCFT.Instance.normGroup_real_complex]
  -- The correspondence itself.
  intro L₁ L₂ fd₁ n₁ fd₂ n₂ c₁ c₂ h
  haveI := fd₁
  haveI := fd₂
  -- Every finite level is `ℝ` or `ℂ`, since `[ℂ : ℝ] = 2`.
  rcases NK.LocalCFT.Instance.intermediateField_eq_bot_or_top L₁ hfinM with h₁ | h₁
  · rcases NK.LocalCFT.Instance.intermediateField_eq_bot_or_top L₂ hfinM with h₂ | h₂
    · -- `L₁ = ℝ`, `L₂ = ℝ`: trivial.
      rw [h₁, h₂]
    · -- `L₁ = ℝ`, `L₂ = ℂ`: the norm group of `ℝ/ℝ` is `ℝˣ`, which is not contained in
      -- `N_{ℂ/ℝ} ℂˣ = ℝ_{>0}` because of `-1`.  Contradiction.
      exfalso
      have hn₁ : NK.LocalReciprocity.normGroup ℝ ↥L₁ = ⊤ := by
        rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.equivOfEq h₁),
          hnormBot]
      have hn₂ : NK.LocalReciprocity.normGroup ℝ ↥L₂ = Units.posSubgroup ℝ := by
        rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.equivOfEq h₂),
          hnormTop]
      have hmem : (-1 : ℝˣ) ∈ NK.LocalReciprocity.normGroup ℝ ↥L₂ := by
        rw [hn₁] at h
        exact h (Subgroup.mem_top _)
      rw [hn₂] at hmem
      have hpos : (0 : ℝ) < ((-1 : ℝˣ) : ℝ) := (Units.mem_posSubgroup (-1)).mp hmem
      norm_num at hpos
  · -- `L₁ = ℂ`: the goal is `L₂ ≤ ℂ`.
    rw [h₁]
    exact le_top

end

end NK.LocalReciprocityLubinTate.Audit
