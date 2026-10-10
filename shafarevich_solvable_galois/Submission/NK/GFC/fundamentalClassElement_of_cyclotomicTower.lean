import Mathlib.GroupTheory.Complement
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary
import Submission.NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary
import Submission.NK.CFTLib.Translation.inf_range_le_ker_res_of_norm
import Submission.NK.GFC.exists_auxiliary_galois_tower_cyclotomic

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.GFC

/-- **The global fundamental class (Milne, CFT, VIII.4.7) from the auxiliary tower with its cyclotomic structure.**

Final assembly of the general (non-cyclic) case of the global fundamental class, using the
auxiliary tower of Route B *with its cyclotomic structure recorded*
(`NK.GFC.exists_auxiliary_galois_tower_cyclotomic`), the arithmetic input `hA` in its `H⁰` form
for that tower (supplied by `NK.GFC.normImage_of_auxiliary_cyclotomic`, whose proof runs the
`CFTLib/Arl/` idèlic Artin map construction with the *cyclotomic* case of the reciprocity law,
which is available unconditionally in this workspace) and the translation between the `H⁰`- and
`H²`-forms of that input (`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm`, proved).

Concretely, given the tower `L₀, M ⊆ E` (with the cyclotomic data `Ω, q, φ`) one has to

* `hnorm` = `hA` (the arithmetic input),
* the two subgroup identities `Msub ⊓ Nsub = ⊥`, `Msub ⊔ Nsub = ⊤` for
  `Msub := M.fixingSubgroup`, `Nsub := L₀.fixingSubgroup` (from the Galois correspondence,
  `IsGalois.fixedField_fixingSubgroup`, `IntermediateField.fixingSubgroup_sup` and `hdisj`, `hsup`),
* `IsCyclic ↥Nsub` (from `hcyc` through the isomorphism `Gal(E/L₀) ≅ Gal(M/K)`, which follows
  from `Msub · Nsub = Gal(E/K)`, `Msub ⊓ Nsub = ⊥` and the injectivity of the composite
  `↥Nsub → Gal(E/K) ⧸ Msub`),
* the `H²` form of `hnorm`
  (`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm Msub Nsub …`), together with the
  `H¹`-vanishing `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup`,
* the cohomological twist: the cyclic fundamental class at the `M`-level
  (`NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary`, from
  `NK.CFTLib.PrimePowerReciprocity`) transported to `H²(Gal(L/K), C_L)`
  (`NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary`), which needs
  `Nat.card (Gal(E/K) ⧸ Msub) = Nat.card Gal(L/K)` and
  `Nat.card (Gal(E/K) ⧸ Nsub) = Nat.card Gal(L/K)` (both from `hcard` and `↥L₀ ≃ₐ[K] L` via
  `IsGalois.normalAutEquivQuotient` and `AlgEquiv.autCongr`). -/
theorem fundamentalClassElement_of_cyclotomicTower (hpp : NK.CFTLib.PrimePowerReciprocity)
    (hA : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
      [FiniteDimensional K E] [IsGalois K E] (L₀ M : IntermediateField K E) [IsGalois K ↥L₀]
      [IsGalois K ↥M] (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
      (hcard : Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = Nat.card (↥M ≃ₐ[K] ↥M))
      (hcyc : IsCyclic (↥M ≃ₐ[K] ↥M)) [Fintype ↥(L₀.fixingSubgroup)]
      (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra ↥L₀ Ω] [IsScalarTower K ↥L₀ Ω]
      [FiniteDimensional ↥L₀ Ω] (q : ℕ) (hq : Nat.Prime q)
      (hcycΩ : IsCyclotomicExtension {q} ↥L₀ Ω) (φ : E →ₐ[↥L₀] Ω) (hφ : Function.Injective φ),
      ∀ a : (NK.GlobalCFT.IdeleClassGroup.rep K E).V,
        (∀ g : Gal(E/K), (NK.GlobalCFT.IdeleClassGroup.rep K E).ρ g a = a) →
        ∃ b : (NK.GlobalCFT.IdeleClassGroup.rep K E).V,
          (∑ n : ↥(L₀.fixingSubgroup),
            (NK.GlobalCFT.IdeleClassGroup.rep K E).ρ (n : Gal(E/K)) b) = a) :
    NK.GlobalCFTdeep.FundamentalClassElement := by
  refine ⟨fun {K L} _ _ _ _ _ _ _ => ?_⟩
  classical
  obtain ⟨E, hfE, hnfE, halgE, hfdE, hgalE, L₀, M, he, hgalM, hcycM, hcardM, hdisj, hsup,
    Ω, hfΩ, halgΩ, halgLΩ, htowerΩ, hfdΩ, q, hq, hcycΩ, φ, hφ⟩ :=
    exists_auxiliary_galois_tower_cyclotomic K L
  letI : Algebra K E := halgE
  letI : FiniteDimensional K E := hfdE
  letI : IsGalois K E := hgalE
  letI : Algebra K Ω := halgΩ
  letI : Algebra ↥L₀ Ω := halgLΩ
  letI : IsScalarTower K ↥L₀ Ω := htowerΩ
  letI : FiniteDimensional ↥L₀ Ω := hfdΩ
  obtain ⟨e⟩ := he
  haveI : IsGalois K ↥L₀ := IsGalois.of_algEquiv e.symm
  haveI : IsGalois K ↥M := hgalM
  let Msub : Subgroup Gal(E/K) := M.fixingSubgroup
  let Nsub : Subgroup Gal(E/K) := L₀.fixingSubgroup
  haveI : Msub.Normal := inferInstance
  haveI : Nsub.Normal := inferInstance
  haveI : Fintype ↥(L₀.fixingSubgroup) := Fintype.ofFinite _
  have hfixM : IntermediateField.fixedField Msub = M :=
    IsGalois.fixedField_fixingSubgroup (F := K) (E := E) M
  have hfixN : IntermediateField.fixedField Nsub = L₀ :=
    IsGalois.fixedField_fixingSubgroup (F := K) (E := E) L₀
  -- The two cardinalities `|Gal(E/K) ⧸ Nsub| = |Gal(L/K)| = |Gal(E/K) ⧸ Msub|`.
  have hcardN : Nat.card (Gal(E/K) ⧸ Nsub) = Nat.card Gal(L/K) := by
    have h1 : Nat.card (Gal(E/K) ⧸ Nsub) =
        Nat.card Gal(↥(IntermediateField.fixedField Nsub)/K) :=
      Nat.card_congr (IsGalois.normalAutEquivQuotient Nsub).toEquiv
    have h2 : Nat.card Gal(↥(IntermediateField.fixedField Nsub)/K) = Nat.card Gal(↥L₀/K) := by
      rw [hfixN]
    have h3 : Nat.card Gal(↥L₀/K) = Nat.card Gal(L/K) :=
      Nat.card_congr (AlgEquiv.autCongr e).toEquiv
    exact h1.trans (h2.trans h3)
  have hcycM' : IsCyclic (Gal(E/K) ⧸ Msub) := by
    have : IsCyclic Gal(↥(IntermediateField.fixedField Msub)/K) := by
      rw [hfixM]
      exact hcycM
    exact (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mpr this
  have hcardM' : Nat.card (Gal(E/K) ⧸ Msub) = Nat.card Gal(L/K) := by
    have h1 : Nat.card (Gal(E/K) ⧸ Msub) =
        Nat.card Gal(↥(IntermediateField.fixedField Msub)/K) :=
      Nat.card_congr (IsGalois.normalAutEquivQuotient Msub).toEquiv
    have h2 : Nat.card Gal(↥(IntermediateField.fixedField Msub)/K) = Nat.card Gal(↥M/K) := by
      rw [hfixM]
    exact h1.trans (h2.trans hcardM)
  -- The Galois correspondence: the fixed fields of `Msub` and `Nsub` are complementary.
  have hdisj' : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥ := by
    rw [hfixM, hfixN, inf_comm]
    exact hdisj
  have hsup' : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤ := by
    rw [hfixM, hfixN, sup_comm]
    exact hsup
  -- The same complementarity at the level of the subgroups themselves.
  have hdisjSub : Msub ⊓ Nsub = ⊥ := by
    have h1 : (IntermediateField.fixedField Msub ⊔
        IntermediateField.fixedField Nsub).fixingSubgroup = Msub ⊓ Nsub := by
      rw [IntermediateField.fixingSubgroup_sup,
        IntermediateField.fixingSubgroup_fixedField Msub,
        IntermediateField.fixingSubgroup_fixedField Nsub]
    rw [← h1, hfixM, hfixN, sup_comm, hsup, IntermediateField.fixingSubgroup_top]
  have hsupSub : Msub ⊔ Nsub = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Msub ⊔ Nsub)]
    have hle : IntermediateField.fixedField (Msub ⊔ Nsub) ≤ ⊥ := by
      rw [← hdisj, ← hfixM, ← hfixN]
      exact le_inf (IntermediateField.fixedField_antitone le_sup_right)
        (IntermediateField.fixedField_antitone le_sup_left)
    have hbot : IntermediateField.fixedField (Msub ⊔ Nsub) = ⊥ := le_bot_iff.mp hle
    rw [hbot, IntermediateField.fixingSubgroup_bot]
  -- `Gal(E/L₀) ≅ Gal(E/K) ⧸ Msub ≅ Gal(M/K)` is cyclic.
  haveI hcycN : IsCyclic ↥Nsub := by
    have hcomp : Msub.IsComplement' Nsub := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff]
        exact hdisjSub
      · rw [← Subgroup.mul_normal Msub Nsub, hsupSub]
        rfl
    exact (MulEquiv.isCyclic (hcomp.symm.QuotientMulEquiv)).mp hcycM'
  -- The arithmetic input `hA`, in its `H⁰` form, for this tower.
  have hcardLM : Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = Nat.card (↥M ≃ₐ[K] ↥M) :=
    (Nat.card_congr (AlgEquiv.autCongr e).toEquiv).trans hcardM.symm
  have hnorm := hA L₀ M hdisj hsup hcardLM hcycM Ω q hq hcycΩ φ hφ
  -- Its `H²` form.
  have hle := NK.CFTLib.Translation.inf_range_le_ker_res_of_norm (M := Msub) (N := Nsub)
    hsupSub hdisjSub (NK.GlobalCFT.IdeleClassGroup.rep K E)
    (NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup Msub)
    (NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup Nsub)
    hnorm
  -- The cyclic fundamental class at the `M`-level, and the twist back to `L/K`.
  obtain ⟨x, hx⟩ :=
    NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary hpp Msub Nsub hcycM' hcardM'
      hdisj' hsup'
  exact NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary Msub Nsub (hfixN ▸ e) hcardN x hx
    hle

end NK.GFC
