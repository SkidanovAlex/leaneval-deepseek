import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
import Submission.Work.SSGRoute.ZConstruction.relaxedSum_pair_eq_zero
import Submission.Work.SSGRoute.ZConstruction.sdiff_not_mem_cs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise BigOperators

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

set_option linter.unusedVariables false

theorem auxDatum_orthogonal_relaxed_noGap {K Λ M : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [FiniteDimensional k M] [IsGalois k M]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hΛM : Λ ≤ M)
    {S T Te : Finset (ValuationSubring Ω)}
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hprod : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (hunr : Work.SSGRoute.IsUnramifiedOrthogonal (p := p) K pair)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B)
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hTcov : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T, Work.SSGRoute.KConj K A' B)
    (hTeT : ∀ A ∈ T, A ∈ Te)
    (hTefin : ∀ A ∈ Te, SSGRoute.IsFinPlace k A)
    (hTedisj : ∀ A ∈ Te, ∀ B ∈ Te, Work.SSGRoute.KConj K A B → A = B)
    {ν : (Ω ≃ₐ[k] Ω) → ZMod p} (hν : Work.SSGRoute.ZHyp (p := p) K Λ S ν)
    (hgap : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ¬ SSGRoute.IsSplitIn k M B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : Work.SSGRoute.IsRelaxedDual (p := p) K M T b) :
    ∑ A ∈ Te, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.auxDatum (p := p) K S ν A) b = 0 := by
  classical
  -- **Step 1.** The relaxed chase at `T`: `relaxedSum_pair_eq_zero` with the relaxation field `M`.
  -- Its relative-unramifiedness hypothesis is weaker than `ZHyp.hyS` (it is only asked at the
  -- places that are *not* `M`-split), and the gap hypothesis closes exactly the missing case:
  -- a place outside `cs(S)` that is `Λ`-split but not `M`-split.
  have hνsum : ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ν b = 0 := by
    refine relaxedSum_pair_eq_zero (p := p) (k := k) (Ω := Ω) (K := K) (Λ := M) (T := T)
      (pair := pair) (z := ν) (b := b) hpair hprod hunr hTfin hTdisj ?_ hν.locconst ?_ hb
    · exact Work.SSGRoute.isCocycleOn_of_addOn (le_refl K.fixingSubgroup) hν.add
    · intro B hB hnotT hnotM σ hσK hσI
      have hnotS : ∀ A' ∈ S, ¬ SSGRoute.IsConjPlace k A' B := by
        intro A' hA' hc
        obtain ⟨t, ht, hc'⟩ := hTcov B ⟨A', hA', hc⟩
        exact hnotT t ht hc'
      by_cases hsp : SSGRoute.IsSplitIn k Λ B
      · exact hgap B hB hnotS hsp hnotM σ hσK hσI
      · exact hν.hyS B hB hnotS hsp σ hσK hσI
  -- **Step 2.** On `T` the prescribed datum `auxDatum K S ν` is `ν` itself (`hTconj`).
  have hcongr : (∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (Work.SSGRoute.auxDatum (p := p) K S ν A) b)
      = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ν b := by
    refine Finset.sum_congr rfl fun A hA => ?_
    have hfun : Work.SSGRoute.auxDatum (p := p) K S ν A = ν := by
      simp only [Work.SSGRoute.auxDatum]
      rw [if_pos (hTconj A hA)]
    rw [hfun]
  -- **Step 3.** The places of `Te ∖ T` contribute nothing: they are not `k`-conjugate into `S`,
  -- so `auxDatum K S ν` vanishes there.
  have hzero' : ∑ A ∈ Te \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.auxDatum (p := p) K S ν A) b = 0 := by
    refine Finset.sum_eq_zero fun A hA => ?_
    obtain ⟨hATe, hAnT⟩ := Finset.mem_sdiff.mp hA
    have hnot : ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A :=
      Work.SSGRoute.not_exists_isConjPlace_of_mem_sdiff K hTcov hTeT hTedisj hATe hAnT
    simp only [Work.SSGRoute.auxDatum]
    rw [if_neg hnot]
    exact Work.SSGRoute.pair_zero_left (p := p) hpair (hTefin A hATe)
      ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
        ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
  -- **Step 4.** Split the sum over `Te = T ∪ (Te ∖ T)`.
  have hunion : T ∪ (Te \ T) = Te := Finset.union_sdiff_of_subset (fun a ha => hTeT a ha)
  calc ∑ A ∈ Te, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (Work.SSGRoute.auxDatum (p := p) K S ν A) b
      = ∑ A ∈ T ∪ (Te \ T), pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
          (Work.SSGRoute.auxDatum (p := p) K S ν A) b := by rw [hunion]
    _ = (∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
            (Work.SSGRoute.auxDatum (p := p) K S ν A) b)
          + ∑ A ∈ Te \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
            (Work.SSGRoute.auxDatum (p := p) K S ν A) b :=
        Finset.sum_union Finset.disjoint_sdiff
    _ = (∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
            (Work.SSGRoute.auxDatum (p := p) K S ν A) b) + 0 := by rw [hzero']
    _ = 0 := by rw [add_zero, hcongr, hνsum]

end Work.SSGRoute.ZConstruction
