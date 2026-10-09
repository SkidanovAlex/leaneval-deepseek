import Mathlib
import Submission.Work.SSGRoute.ZConstruction.auxDatum_orthogonal_enlarged
import Submission.Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation
import Submission.Work.SSGRoute.ZConstruction.AuxRealisationHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

theorem auxDatum_realisation_of_counting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ] [FiniteDimensional k N] [IsGalois k N] (hΛN : Λ ≤ N)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
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
    {ν : (Ω ≃ₐ[k] Ω) → ZMod p} (hν : Work.SSGRoute.ZHyp (p := p) K Λ S ν)
    (horth : Work.SSGRoute.ZDataMup.IsOrthogonalToDual p k Ω K pair Te
      (Work.SSGRoute.auxDatum (p := p) K S ν))
    (hcount : Work.SSGRoute.ZDataMup.CountingInequality p k Ω K Te) :
    ∃ yAux : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup yAux ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = ν σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ Te, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0) := by
  classical
  -- (0) the prescribed datum is a locally constant `1`-cocycle on every local group of `Te`:
  -- either it is `ν` (at the places conjugate into `S`) or it is `0`.
  have hf : ∀ A ∈ Te, SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
          (Work.SSGRoute.auxDatum (p := p) K S ν A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
          (Work.SSGRoute.auxDatum (p := p) K S ν A) := by
    intro A hA
    by_cases hc : ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A
    · have hd : Work.SSGRoute.auxDatum (p := p) K S ν A = ν := by
        funext σ
        simp only [Work.SSGRoute.auxDatum]
        rw [if_pos hc]
      constructor
      · rw [hd]
        intro g hg h' hh
        have hgK : g ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hg).2
        rw [Work.SSGRoute.ZDataMup.res_eq_one_of_mem_fixingSubgroup hgK, one_smul]
        exact hν.add g hgK h' (Subgroup.mem_inf.mp hh).2
      · rw [hd]
        obtain ⟨U, hUo, hU⟩ := hν.locconst
        exact ⟨U, hUo,
          fun g hg u hu huK => hU g (Subgroup.mem_inf.mp hg).2 u hu (Subgroup.mem_inf.mp huK).2⟩
    · have hd : Work.SSGRoute.auxDatum (p := p) K S ν A = 0 := by
        funext σ
        simp only [Work.SSGRoute.auxDatum]
        rw [if_neg hc]
      constructor
      · rw [hd]
        intro g hg h' hh
        simp
      · rw [hd]
        obtain ⟨U, hUo, _⟩ := hν.locconst
        exact ⟨U, hUo, fun g hg u hu huK => rfl⟩
  -- (1) the level-`K` degree-one realisation at the enlarged place set `Te`, with the local datum
  -- `auxDatum K S ν`, supplied by the counting inequality.
  obtain ⟨z, hzc, hzl, hzcob, hzunr⟩ :=
    Work.SSGRoute.ZConstruction.levelK_realisation_of_counting p hp k Ω K pair hpair hrec Te hTefin
      (fun A hA B hB h => hTedisj A hA B hB (Work.SSGRoute.kConj_of_forall_mem h))
      (Work.SSGRoute.auxDatum (p := p) K S ν) hf horth hcount
  refine ⟨z, hzc, hzl, ?_, ?_⟩
  -- (2) the prescription at every place `G_k`-conjugate into `S`: transport the agreement at the
  -- level-`K` representative `A' ∈ T ⊆ Te` (where the datum is `ν`) along level-`K` conjugacy.
  · intro B hB hconjB σ hσ
    obtain ⟨A', hA'T, hA'B⟩ := hTcov B hconjB
    have hA'Te : A' ∈ Te := hTeT A' hA'T
    have hd : ∀ τ, Work.SSGRoute.auxDatum (p := p) K S ν A' τ = ν τ := by
      intro τ
      simp only [Work.SSGRoute.auxDatum]
      rw [if_pos (hTconj A' hA'T)]
    have hagree : ∀ ρ ∈ SSGRoute.decomp k A' ⊓ K.fixingSubgroup, z ρ = ν ρ := by
      intro ρ hρ
      have h := (Work.SSGRoute.ZDataMup.sub_isCoboundaryOn_iff_eqOn (K := K)
        (fun x hx => (Subgroup.mem_inf.mp hx).2) z
        (Work.SSGRoute.auxDatum (p := p) K S ν A')).mp (hzcob A' hA'Te) ρ hρ
      rwa [hd ρ] at h
    refine Work.SSGRoute.ZConstruction.kConj_of_local_agree (z := z) (w := ν) (A := A') (B := B)
      ?_ hν.add hA'B hagree σ hσ
    intro g hg h' hh
    have h := hzc g hg h' hh
    rwa [Work.SSGRoute.ZDataMup.res_eq_one_of_mem_fixingSubgroup hg, one_smul] at h
  -- (3) the vanishing clause: a place that is not conjugate into `Te` is a fortiori not
  -- level-`K`-conjugate to an element of `Te`, where the realisation is unramified.
  · intro B hB hnot hns σ hσK hσI
    refine hzunr B hB ?_ σ hσK hσI
    intro A hA hconj
    exact hnot A hA (Work.SSGRoute.ZConstruction.kConj_isConjPlace
      (Work.SSGRoute.kConj_of_forall_mem hconj))

end Work.SSGRoute.ZConstruction
