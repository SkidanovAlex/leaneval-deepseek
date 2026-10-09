import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.unramifiedNormGroup_eq_zpowers_sup
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Audit: the norm-correspondence hypothesis is satisfiable at a `p`-adic place

`NK.LocalReciprocityLubinTate.NormCorrespondence F F'` (Hasse's *Normensatz*) is the statement

  `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ → L₂ ≤ L₁`

for finite abelian levels `L₁, L₂ ≤ F^{ab}` of local class field theory.  This file is the audit
witness that the hypothesis is *inhabited*: for `F = Q.adicCompletion K` (the completion of a number
field at a finite place) we exhibit two finite abelian levels `L₂ ≤ L₁` of `F^{ab}` with

  `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ`   but   `¬ (N_{L₂/F} L₂ˣ ≤ N_{L₁/F} L₁ˣ)`,

i.e. the containment of norm groups asserted in the hypothesis of the correspondence really
happens for a *strict* pair of levels, so `NormCorrespondence` is not vacuously true for a `p`-adic
field.  This complements `Audit.normCorrespondence_real_complex` (the archimedean case).

## The witness

* `L₂ = ⊥` — the base field itself, whose norm group is all of `Fˣ`;
* `L₁` — the **unramified level of degree `2`**, i.e. the quadratic unramified extension of `F`
  (`NK.Unramified.exists_unramified_level_adicCompletion`), transported into the maximal abelian
  subextension `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F (SeparableClosure F)`.

Its norm group is `⟨π²⟩ · U⁰` (`unramifiedNormGroup_eq_zpowers_sup`), and this is a *proper*
subgroup of `Fˣ`: the uniformiser `π` itself is not a norm from the unramified quadratic
extension, because the value of a norm of an unramified extension of degree `m` is an `m`-th power
of a value (equivalently `valUnits π = valUnits π ^ (2k)` would force `2k = 1`).  This last step is
elementary and needs no class field theory: it is `aux_uniformizer` below.
-/

open scoped ValuativeRel

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Audit

noncomputable section

/-- **A uniformiser is not in `⟨π²⟩ · U⁰`.**  Equivalently: `π` is not a norm from the unramified
quadratic extension of a nonarchimedean local field `F` with uniformiser `π`.

Route: `U⁰ = ker (valUnits : Fˣ →* (ValueGroupWithZero F)ˣ)` is exactly the group of units of the
ring of integers (`ker_valUnits`, `higherUnits_zero`), so from `π = (π²)^k · b` with `b ∈ U⁰` we
deduce `valUnits π = (valUnits π) ^ (2k)` in the (torsion-free) value group, hence
`(valUnits π) ^ (2k-1) = 1` and `2k - 1 = 0` by `zpow_valUnits_pi_eq_one_iff` — impossible. -/
private lemma aux_uniformizer {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F)) :
    (π : Fˣ) ∉ Subgroup.zpowers (π ^ 2) ⊔ NK.LocalReciprocityLubinTate.higherUnits F 0 := by
  intro hmem
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Subgroup.mem_zpowers_iff] at ha
  obtain ⟨k, hk⟩ := ha
  rw [← hk] at hab
  -- `b` is a unit of the ring of integers, so its valuation is trivial
  have hbker : NK.LocalReciprocityLubinTate.Units.valUnits F b = 1 := by
    have h : b ∈ (NK.LocalReciprocityLubinTate.Units.valUnits F).ker := by
      rw [NK.LocalReciprocityLubinTate.Units.ker_valUnits,
        ← NK.LocalReciprocityLubinTate.Unramified.higherUnits_zero]
      exact hb
    simpa using h
  have h2 : ((NK.LocalReciprocityLubinTate.Units.valUnits F) π ^ 2) ^ k
      = ((NK.LocalReciprocityLubinTate.Units.valUnits F) π) ^ (2 * k) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  have hmain : (NK.LocalReciprocityLubinTate.Units.valUnits F) π
      = ((NK.LocalReciprocityLubinTate.Units.valUnits F) π) ^ (2 * k) := by
    calc (NK.LocalReciprocityLubinTate.Units.valUnits F) π
        = (NK.LocalReciprocityLubinTate.Units.valUnits F) ((π ^ 2) ^ k * b) := by rw [hab]
      _ = ((NK.LocalReciprocityLubinTate.Units.valUnits F) π) ^ (2 * k) := by
            rw [map_mul, hbker, mul_one, map_zpow, map_pow, h2]
  have hkey : ((NK.LocalReciprocityLubinTate.Units.valUnits F) π) ^ (2 * k - 1) = 1 := by
    rw [zpow_sub, ← hmain, zpow_one, mul_inv_cancel]
  have hzero :=
    (NK.LocalReciprocityLubinTate.Units.zpow_valUnits_pi_eq_one_iff F π hπ (2 * k - 1)).mp hkey
  omega

/-- **The norm-correspondence hypothesis is satisfiable at a `p`-adic place.**  There are two
finite abelian levels `L₂ ≤ L₁` of `F^{ab}` (`F = Q.adicCompletion K`) with
`N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ` but not conversely — namely `L₂ = ⊥` and `L₁` the unramified level
of degree `2`.  Hence `NK.LocalReciprocityLubinTate.NormCorrespondence F F'` is not vacuous. -/
theorem normCorrespondence_hypothesis_satisfiable {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    ∃ (L₁ L₂ : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K)))),
      FiniteDimensional (Q.adicCompletion K) L₁ ∧ Normal (Q.adicCompletion K) L₁ ∧
      (∀ σ τ : ↥L₁ ≃ₐ[Q.adicCompletion K] ↥L₁, σ * τ = τ * σ) ∧
      FiniteDimensional (Q.adicCompletion K) L₂ ∧ Normal (Q.adicCompletion K) L₂ ∧
      (∀ σ τ : ↥L₂ ≃ₐ[Q.adicCompletion K] ↥L₂, σ * τ = τ * σ) ∧
      L₂ ≤ L₁ ∧ L₁ ≠ L₂ ∧
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁ ≤
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ ∧
      ¬ (NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ ≤
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁) := by
  classical
  -- ## Step 1.  The unramified level of degree `2`, inside the algebraic closure of `F`.
  obtain ⟨E, θ, _hE, hfdE, hgalE, hcommE, hrankE, hNE⟩ :=
    NK.Unramified.exists_unramified_level_adicCompletion K Q 2 (by norm_num)
  haveI : FiniteDimensional (Q.adicCompletion K) ↥E := hfdE
  haveI : IsGalois (Q.adicCompletion K) ↥E := hgalE
  -- ## Step 2.  Transport it into the separable closure of `F`.
  obtain ⟨E', ⟨e⟩⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.exists_intermediateField_algEquiv_of_isSepClosed
      (F := Q.adicCompletion K) (F' := SeparableClosure (Q.adicCompletion K)) E
  haveI : FiniteDimensional (Q.adicCompletion K) ↥E' := Module.Finite.equiv e.toLinearEquiv
  haveI : Normal (Q.adicCompletion K) ↥E' := Normal.of_algEquiv e
  have hcommE' : ∀ σ τ : ↥E' ≃ₐ[Q.adicCompletion K] ↥E', σ * τ = τ * σ := by
    intro σ τ
    apply (AlgEquiv.autCongr e).symm.injective
    rw [map_mul, map_mul]
    exact hcommE _ _
  -- ## Step 3.  Its Galois group is commutative, so it lies in the maximal abelian subextension.
  have hle : E' ≤ NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative E' hcommE'
  -- ## Step 4.  The two norm groups.
  have hnormL₁ : NK.LocalReciprocity.normGroup (Q.adicCompletion K)
      ↥(NK.LocalReciprocityLubinTate.Unramified.restrictLevel E' hle)
      = Subgroup.zpowers (π ^ 2) ⊔
        NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K) 0 := by
    rw [NK.LocalReciprocityLubinTate.Unramified.normGroup_restrictLevel,
      ← NK.LocalReciprocity.normGroup_eq_of_algEquiv e, hNE,
      NK.LocalReciprocityLubinTate.Unramified.unramifiedNormGroup_eq_zpowers_sup Q π hπ 2]
  have hnormL₂ : NK.LocalReciprocity.normGroup (Q.adicCompletion K)
      ↥(⊥ : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K)))) = ⊤ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.botEquiv (Q.adicCompletion K)
        ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K)))),
      NK.LocalReciprocity.normGroup, Algebra.norm_self, Units.map_id, MonoidHom.range_eq_top]
    intro x
    exact ⟨x, rfl⟩
  -- ## Step 5.  `L₂ = ⊥` and `L₁` the unramified level of degree `2` are the required witnesses.
  refine ⟨NK.LocalReciprocityLubinTate.Unramified.restrictLevel E' hle, ⊥,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · exact inferInstance
  · exact NK.LocalReciprocityLubinTate.Unramified.commutative_restrictLevel E' hle hcommE'
  · exact inferInstance
  · exact inferInstance
  · -- the Galois group of the base field is trivial
    haveI : Subsingleton (↥(⊥ : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K)))) ≃ₐ[Q.adicCompletion K]
        ↥(⊥ : IntermediateField (Q.adicCompletion K)
          (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K))))) :=
      ⟨fun σ τ => by
        apply (AlgEquiv.autCongr (IntermediateField.botEquiv (Q.adicCompletion K)
          ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K))))).injective
        exact Subsingleton.elim _ _⟩
    intro σ τ
    rw [Subsingleton.elim σ τ]
  · exact bot_le
  · -- `L₁` is a quadratic extension, hence not the base field
    intro h
    have h1 : Module.finrank (Q.adicCompletion K)
        ↥(NK.LocalReciprocityLubinTate.Unramified.restrictLevel E' hle) = 2 :=
      (e.toLinearEquiv.finrank_eq.trans
        (NK.LocalReciprocityLubinTate.Unramified.restrictLevelEquiv E' hle).toLinearEquiv.finrank_eq).symm.trans
        hrankE
    have h2 : Module.finrank (Q.adicCompletion K)
        ↥(NK.LocalReciprocityLubinTate.Unramified.restrictLevel E' hle) = 1 := by
      rw [h, (IntermediateField.botEquiv (Q.adicCompletion K)
          ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K)))).toLinearEquiv.finrank_eq,
        Module.finrank_self]
    omega
  · rw [hnormL₂]
    exact le_top
  · -- the uniformiser is not a norm from the unramified quadratic level
    intro h
    rw [hnormL₂] at h
    have hmem : π ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K)
        ↥(NK.LocalReciprocityLubinTate.Unramified.restrictLevel E' hle) := h (Subgroup.mem_top π)
    rw [hnormL₁] at hmem
    exact aux_uniformizer π hπ hmem

end

end NK.LocalReciprocityLubinTate.Audit
