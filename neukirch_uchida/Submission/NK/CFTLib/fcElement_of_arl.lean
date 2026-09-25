import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.CFTLib.primePowerReciprocity_of_arl
import Submission.NK.CFTLib.Translation.inf_range_le_ker_res_of_norm
import Submission.NK.GlobalCFTdeep.H1All
import Submission.NK.CFTLib.Arl.arl_invariants
import Submission.Commons.GroupTheory.Subgroup.card_sup_mul_card_inf_of_normal

/-!
# The global fundamental class from the ideal-theoretic Artin reciprocity law

Target: the theorem `NK.CFTLib.fcElement_of_arl` stated at the end of this file, namely that the
ideal-theoretic Artin reciprocity law `NK.CFTLib.ArtinReciprocityIdeal` implies the global
fundamental class `NK.GlobalCFTdeep.FundamentalClassElement`.

This is Milne, *Class Field Theory*, VIII.4 Theorem 4.7: for every finite Galois extension `L/K` of
number fields, `H²(Gal(L/K), C_L)` contains an element of order `[L:K]` (the *global fundamental
class*), deduced here from the ideal-theoretic reciprocity law `h`.

## How it is proved

The reduction is the "Route B" of `Submission/Work/CFTLib/RouteB/plan.lean` (Milne VIII.4, the
classical "compare `L` with a cyclic extension of the same degree" argument), and it is carried out
here as follows.

* `NK.CFTLib.primePowerReciprocity_of_arl h : PrimePowerReciprocity`: the cyclicity of
  `C_E ⧸ N_{F/E}C_F` for cyclic `F/E` (this is unconditional in this workspace, hence `h` is not
  needed for it).
* `NK.CFTLib.fundamentalClassElement_of_arithmeticInput` (proved in
  `Submission/Work/CFTLib/fundamentalClassElement.lean`): the cyclic fundamental class at the
  auxiliary level, the cohomological twist
  (`NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary`) and the auxiliary Galois tower
  (`NK.CFTLib.GFC.exists_auxiliary_galois_tower`) give `FundamentalClassElement` **provided** the
  single arithmetic input `NK.CFTLib.fundamentalClassArithmeticInput`, i.e. for the auxiliary
  tower `range (inf_{Msub}) ≤ ker (res_{Nsub})`.
* `fundamentalClassArithmeticInput_of_arl` below reduces that input to its `H⁰`-form
  `C_K ⊆ N_{Ω/L₀}C_Ω` (`A^G ≤ range(N_{Nsub})`), via the proved translation
  `NK.CFTLib.Translation.inf_range_le_ker_res_of_norm`; the Galois-correspondence identities
  `fixedField (M ⊔ N) = fixedField M ⊓ fixedField N`, `fixedField (M ⊓ N) = fixedField M ⊔ fixedField N`
  and the cardinality computation `Nat.card ↥Nsub = Msub.index` (hence `|Msub| = |Nsub|`, and
  `IsCyclic ↥Nsub` from `IsCyclic (Gal(Ω/K) ⧸ Msub)`) are proved here.

The single remaining arithmetic input is the delegated lemma
`NK.CFTLib.Arl.arl_invariants` (`Submission/Work/CFTLib/Arl/arl_invariants.lean`): with
`G = Gal(Ω/K) = Msub × Nsub`, `Nsub` cyclic of order `n = |Msub|`, every `G`-invariant element of
`C_Ω` is a norm for `Nsub`.  It is the Verlagerung computation `θ_{Ω/L} ∘ i = θ_{M/K} ∘ N_{L/K}`
(equivalently `Artin_{Ω/L}(i x) = Artin_{M/K}(x)^n = 1` since `Gal(M/K)` has exponent `n`), the
one place where the arithmetic of `C_•` — as opposed to the abstract class-formation axioms —
enters; see the docstring of that file and `RouteB/plan.lean` for the route (weak approximation at
the ramified places plus unramified Frobenius functoriality).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain Pointwise

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

section GaloisCorr

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

lemma fixedField_injective :
    Function.Injective (IntermediateField.fixedField : Subgroup Gal(Ω/K) → IntermediateField K Ω) := by
  intro M N h
  have h2 := congrArg IntermediateField.fixingSubgroup h
  rwa [IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_fixedField] at h2

lemma fixedField_sup_eq (M N : Subgroup Gal(Ω/K)) :
    IntermediateField.fixedField (M ⊔ N) =
      IntermediateField.fixedField M ⊓ IntermediateField.fixedField N := by
  refine le_antisymm ?_ ?_
  · exact le_inf (IntermediateField.fixedField_le le_sup_left)
      (IntermediateField.fixedField_le le_sup_right)
  · have h : M ⊔ N ≤ IntermediateField.fixingSubgroup
        (IntermediateField.fixedField M ⊓ IntermediateField.fixedField N) := by
      refine sup_le ?_ ?_
      · have hle : IntermediateField.fixedField M ⊓ IntermediateField.fixedField N ≤
            IntermediateField.fixedField M := inf_le_left
        have h1 := IntermediateField.fixingSubgroup_le hle
        rwa [IntermediateField.fixingSubgroup_fixedField M] at h1
      · have hle : IntermediateField.fixedField M ⊓ IntermediateField.fixedField N ≤
            IntermediateField.fixedField N := inf_le_right
        have h1 := IntermediateField.fixingSubgroup_le hle
        rwa [IntermediateField.fixingSubgroup_fixedField N] at h1
    have h2 := IntermediateField.fixedField_le h
    rwa [IsGalois.fixedField_fixingSubgroup] at h2

lemma fixedField_inf_eq (M N : Subgroup Gal(Ω/K)) :
    IntermediateField.fixedField (M ⊓ N) =
      IntermediateField.fixedField M ⊔ IntermediateField.fixedField N := by
  have h : (IntermediateField.fixedField M ⊔ IntermediateField.fixedField N).fixingSubgroup
      = M ⊓ N := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField]
  have h2 := congrArg IntermediateField.fixedField h
  rw [IsGalois.fixedField_fixingSubgroup] at h2
  exact h2.symm

lemma fixedField_bot_eq_top :
    IntermediateField.fixedField (⊥ : Subgroup Gal(Ω/K)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  rw [Subgroup.mem_bot] at hf
  rw [hf]
  rfl

lemma card_eq_index_of_sup_eq_top_of_inf_eq_bot {G : Type*} [Group G] [Finite G]
    (M N : Subgroup G) [N.Normal] (hMN : M ⊔ N = ⊤) (hdisj : M ⊓ N = ⊥) :
    Nat.card ↥N = M.index := by
  have h1 : Nat.card ↥(M ⊔ N) * Nat.card ↥(M ⊓ N) = Nat.card ↥M * Nat.card ↥N :=
    Commons.GroupTheory.Subgroup.card_sup_mul_card_inf_of_normal M N inferInstance
  rw [hMN, hdisj, Subgroup.card_top, Subgroup.card_bot, mul_one] at h1
  have h2 := Subgroup.card_mul_index M
  rw [h1] at h2
  exact (Nat.mul_left_cancel (Nat.card_pos) h2).symm

end GaloisCorr

/-- **The arithmetic input of Route B, from the ideal-theoretic Artin law.** -/
theorem fundamentalClassArithmeticInput_of_arl (h : ArtinReciprocityIdeal) :
    fundamentalClassArithmeticInput := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ _ Msub Nsub _ _ hN hM hcyc hdisj hsup
  classical
  have hMN : Msub ⊔ Nsub = ⊤ := by
    apply fixedField_injective
    rw [fixedField_sup_eq, hdisj, IsGalois.fixedField_top]
  have hdisj' : Msub ⊓ Nsub = ⊥ := by
    apply fixedField_injective
    rw [fixedField_inf_eq, hsup, fixedField_bot_eq_top]
  have hNsub : Nat.card ↥Nsub = Msub.index :=
    card_eq_index_of_sup_eq_top_of_inf_eq_bot Msub Nsub hMN hdisj'
  have hMsub : Nat.card ↥Msub = Nsub.index :=
    card_eq_index_of_sup_eq_top_of_inf_eq_bot Nsub Msub (by rw [sup_comm]; exact hMN)
      (by rw [inf_comm]; exact hdisj')
  have hcard : Nat.card ↥Nsub = Nat.card ↥Msub := by
    rw [hNsub, hMsub, Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact hM.trans hN.symm
  have hcyc' : IsCyclic ↥Nsub := by
    have hbij : Function.Bijective
        ((QuotientGroup.mk' Msub).comp Nsub.subtype : ↥Nsub → Gal(Ω/K) ⧸ Msub) := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        have h1 : ((x : Gal(Ω/K))⁻¹ * (y : Gal(Ω/K))) ∈ Msub := by
          have hxy' : (((QuotientGroup.mk' Msub).comp Nsub.subtype) x)
              = (((QuotientGroup.mk' Msub).comp Nsub.subtype) y) := hxy
          rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy'
          exact hxy'
        have h2 : ((x : Gal(Ω/K))⁻¹ * (y : Gal(Ω/K))) ∈ Nsub :=
          Nsub.mul_mem (Nsub.inv_mem x.2) y.2
        have h3 : ((x : Gal(Ω/K))⁻¹ * (y : Gal(Ω/K))) ∈ (⊥ : Subgroup Gal(Ω/K)) := by
          rw [← hdisj']; exact ⟨h1, h2⟩
        rw [Subgroup.mem_bot] at h3
        exact Subtype.ext (inv_mul_eq_one.mp h3)
      · intro z
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Msub z
        have hg : g ∈ (Msub : Set (Gal(Ω/K))) * (Nsub : Set (Gal(Ω/K))) := by
          rw [← Subgroup.mul_normal Msub Nsub, hMN]
          exact Subgroup.mem_top g
        obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hg
        refine ⟨⟨n, hn⟩, ?_⟩
        show (QuotientGroup.mk' Msub) n = (QuotientGroup.mk' Msub) g
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hmn]
        simpa only [mul_assoc] using
          Subgroup.Normal.conj_mem' (inferInstance : Msub.Normal) m hm n
    exact (MulEquiv.isCyclic (MulEquiv.ofBijective _ hbij)).mpr hcyc
  exact NK.CFTLib.Translation.inf_range_le_ker_res_of_norm Msub Nsub hMN hdisj'
    (IdeleClassGroup.rep K Ω)
    (NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup Msub)
    (NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup Nsub)
    (Arl.arl_invariants h Msub Nsub hcyc' hMN hdisj' hcard)

theorem fcElement_of_arl (h : NK.CFTLib.ArtinReciprocityIdeal) : NK.GlobalCFTdeep.FundamentalClassElement :=
  NK.CFTLib.fundamentalClassElement_of_arithmeticInput
    (NK.CFTLib.primePowerReciprocity_of_arl h)
    (NK.CFTLib.fundamentalClassArithmeticInput_of_arl h)

end NK.CFTLib
