import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxExistsOfCounting
import Submission.Work.SSGRoute.ZConstruction.AuxDatumZHyp
import Submission.Work.SSGRoute.ZConstruction.auxDatum_realisation_of_counting_vanishing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Second step of the glue: the `ZHyp` clauses of the auxiliary class from the two gates

This consumes the vanishing-form bridge
`Work.SSGRoute.ZConstruction.auxDatum_realisation_of_counting_vanishing` (H162-L2450) with the two
pinned gates `AuxDatumOrthogonality` / `AuxDatumCounting` (instantiated at the auxiliary level `N`),
and derives `Work.SSGRoute.ZHyp K N T⁺ yAux` for the realised class by
`Work.SSGRoute.ZConstruction.zHyp_of_prescribed_localData`.

The involution clause is discharged as in `Work.SSGRoute.auxRealisationExt_of_noInv`: for odd `p` and a
primitive `p`-th root of unity `ζ ∈ K`, the only element of `G_K` of order two is `1`
(`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`), and `yAux 1 = 0` is the cocycle
identity.  Hence the statement carries `hp : p ≠ 2`, `hζ` and `hζK` -- the node's own hypotheses.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] [FiniteDimensional k Λ] [IsGalois k Λ]
  [FiniteDimensional k N] [IsGalois k N]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The auxiliary class's `ZHyp` at `(N, T⁺)`, from the two gates.** -/
theorem exists_zHyp_of_countingBlocks (hp : p ≠ 2) (hΛN : Λ ≤ N)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    {S T Te : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B)
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hTcov : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T, Work.SSGRoute.KConj K A' B)
    (hTeT : ∀ A ∈ T, A ∈ Te) (hTefin : ∀ A ∈ Te, SSGRoute.IsFinPlace k A)
    (hTedisj : ∀ A ∈ Te, ∀ B ∈ Te, Work.SSGRoute.KConj K A B → A = B)
    (hTecov : ∀ B : ValuationSubring Ω, (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ Te, Work.SSGRoute.KConj K A' B)
    (hcover : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ Te, SSGRoute.IsConjPlace k A B)
    {ν : (Ω ≃ₐ[k] Ω) → ZMod p} (hν : Work.SSGRoute.ZHyp (p := p) K Λ S ν)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hgate : AuxDatumOrthogonality (p := p) (K := K) (Λ := Λ) pair)
    (hcount : AuxDatumCounting (p := p) (K := K) (Λ := Λ)) :
    ∃ yAux : (Ω ≃ₐ[k] Ω) → ZMod p,
      Work.SSGRoute.ZHyp (p := p) K N Te yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = ν σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0) := by
  classical
  obtain ⟨yAux, hcoc, hloc, hag, hvan, hunr⟩ :=
    auxDatum_realisation_of_counting_vanishing p hp k Ω K Λ N hΛN pair hpair hrec
      hSfin hTfin hTdisj hTconj hTcov hTeT hTefin hTedisj hTecov hν
      (hgate N hΛN hSfin hTfin hTdisj hTconj hTcov hTeT hTefin hTedisj hν)
      (hcount N hΛN hTefin hcover)
  have hyAuxadd := addOn_of_isCocycleOn hcoc
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → yAux c = 0 := by
    intro c hc hc2
    have hc1 : c = 1 := by
      have hcc : c.toRingEquiv * c.toRingEquiv = 1 := by
        ext x
        have h : c (c x) = x := by
          have h2 := congrArg (fun (g : Ω ≃ₐ[k] Ω) => g x) hc2
          simpa using h2
        simpa using h
      have hfix : c.toRingEquiv ζ = ζ := by
        have h : c ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff K c).mp hc ζ hζK
        simpa using h
      have h := eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot (c.toRingEquiv) hcc
        (Fact.out : p.Prime) hp hζ hfix
      ext x
      have h2 := congrArg (fun (g : Ω ≃+* Ω) => g x) h
      simpa using h2
    rw [hc1]
    have h := hyAuxadd 1 (one_mem _) 1 (one_mem _)
    rw [one_mul] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  exact ⟨yAux,
    zHyp_of_prescribed_localData (p := p) hν hyAuxadd hloc hunr hinf hag hvan,
    hag, hvan⟩

end Work.SSGRoute.ZConstruction
