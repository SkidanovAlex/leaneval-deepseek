import Mathlib
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFTdeep.natCard_groupCohomology_two_le_card
import Submission.NK.GlobalCFTdeep.H1All
import Submission.NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower
import Submission.NK.CFTLib.exists_addOrderOf_eq_card_of_cyclic_normClassQuotient
import Submission.NK.CFTLib.isCyclic_normClassQuotient_of_primePower

/-! # The inputs of the global fundamental class

This module is `sorry`-free and holds the pieces of the reduction of
`NK.GlobalCFTdeep.FundamentalClassElement` (Milne, *Class Field Theory*, VIII.4 Theorem 4.7)
that are available unconditionally in this workspace:

* `NK.CFTLib.PrimePowerReciprocity` — the one remaining arithmetic input of the *cyclic* case:
  for cyclic `L/K` of prime-power degree, the norm class quotient `C_K ⧸ N_{L/K}C_L` is cyclic
  (Artin reciprocity at prime-power cyclic levels; `Submission/Work/GlobalCFTdeep/README.md` §18);
* `NK.CFTLib.NormQuotientGeneratorInput` — the cohomological passage from the cyclicity of the
  norm class quotient to the fundamental class (cyclic `2`-periodicity of group cohomology), and
  its unconditional proof `NK.CFTLib.normQuotientGeneratorInput`;
* `NK.CFTLib.exists_fundamentalClass_of_isCyclic` — the fundamental class for every **cyclic**
  extension of number fields, from `PrimePowerReciprocity` alone.

The remaining content of `FundamentalClassElement` is then the *general* (non-cyclic) case, Milne
VIII.4 Theorem 4.7, which compares `L` with a cyclic cyclotomic extension of the same degree
inside a common overfield.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-- **Artin reciprocity for cyclic extensions of prime-power degree**: for cyclic `L/K` with
`[L:K] = p^a`, the norm class quotient `C_K ⧸ N_{L/K}C_L` is cyclic (of order `p^a`).

This is the input consumed by `NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower`, and
the sharpest form of the arithmetic content of the fundamental class for cyclic extensions. -/
def PrimePowerReciprocity : Prop :=
  ∀ {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)],
    (∃ p k : ℕ, p.Prime ∧ 0 < k ∧ Nat.card (F ≃ₐ[E] F) = p ^ k) →
    IsCyclic (IdeleClassGroup E ⧸ Idele.normClassSubgroup E F)

/-- **The cohomological content of reciprocity for cyclic extensions**: if `x` generates the norm
class quotient `C_K ⧸ N_{L/K}C_L` (a cyclic group of order `[L:K]`), then `H²(Gal(L/K), C_L)`
contains an element of order `[L:K]`.

The proof is the `2`-periodicity of the cohomology of a cyclic group: `H²(G, C_L) ≅ Ĥ²(G, C_L) ≅
Ĥ⁰(G, C_L) ≅ C_K ⧸ N_{L/K}C_L`; this is the global analogue of the proved
`Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_card_of_cyclic_norm_quotient`
(units of a cyclic extension). -/
def NormQuotientGeneratorInput : Prop :=
  ∀ {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)] (x : IdeleClassGroup E),
    (∀ k : ℕ, x ^ k ∈ Idele.normClassSubgroup E F ↔ Nat.card (F ≃ₐ[E] F) ∣ k) →
    ∃ α : groupCohomology (IdeleClassGroup.rep E F) 2, addOrderOf α = Nat.card (F ≃ₐ[E] F)

/-- **The prime-power Artin-reciprocity input is available unconditionally**: this is the proved
`NK.CFTLib.isCyclic_normClassQuotient_of_primePower` (whose proof reduces the prime-power case to
`a = 1`, `a = 2` and `a ≥ 3` by induction on the group order). -/
theorem primePowerReciprocity : PrimePowerReciprocity := by
  intro E F _ _ _ _ _ _ _ _ h
  exact NK.CFTLib.isCyclic_normClassQuotient_of_primePower (K := E) (L := F) h

/-- **The cyclic-periodicity input is available unconditionally**: this is the proved
`NK.CFTLib.exists_addOrderOf_eq_card_of_cyclic_normClassQuotient`. -/
theorem normQuotientGeneratorInput : NormQuotientGeneratorInput := by
  intro E F _ _ _ _ _ _ _ _ x hx
  exact exists_addOrderOf_eq_card_of_cyclic_normClassQuotient (K := E) (L := F) x hx

/-- **The fundamental class for cyclic extensions of number fields**, from the two inputs of the
cyclic case: Artin reciprocity at prime-power cyclic levels and the cyclic-periodicity passage. -/
theorem exists_fundamentalClass_of_isCyclic_of_inputs (hpp : PrimePowerReciprocity)
    (hgen : NormQuotientGeneratorInput) {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ α : groupCohomology (IdeleClassGroup.rep K L) 2, addOrderOf α = Nat.card (L ≃ₐ[K] L) := by
  haveI hcyc : IsCyclic (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower hpp
  have hcard : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) =
      Nat.card (L ≃ₐ[K] L) := by
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup K L),
      NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic, IsGalois.card_aut_eq_finrank]
  obtain ⟨y, hy⟩ :=
    IsCyclic.exists_generator (α := IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Idele.normClassSubgroup K L) y
  refine hgen x ?_
  intro k
  rw [← QuotientGroup.eq_one_iff (x ^ k)]
  rw [show ((x ^ k : IdeleClassGroup K) : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)
      = (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) ^ k from by
    rw [← QuotientGroup.mk'_apply, map_pow]]
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_eq_card_of_forall_mem_zpowers hy, hcard]

/-- **The fundamental class for cyclic extensions of number fields**, from the single arithmetic
input `PrimePowerReciprocity`. -/
theorem exists_fundamentalClass_of_isCyclic (hpp : PrimePowerReciprocity) {K L : Type}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ α : groupCohomology (IdeleClassGroup.rep K L) 2, addOrderOf α = Nat.card (L ≃ₐ[K] L) :=
  exists_fundamentalClass_of_isCyclic_of_inputs hpp normQuotientGeneratorInput

end NK.CFTLib
