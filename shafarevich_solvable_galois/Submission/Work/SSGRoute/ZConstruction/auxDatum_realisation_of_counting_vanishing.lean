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
import Submission.Work.SSGRoute.ZConstruction.AuxDatumZHyp
import Submission.Work.SSGRoute.ZConstruction.sdiff_not_mem_cs
import Submission.Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

/-- **The realisation of the prescribed datum with the *vanishing* prescription at `cs(Te) ∖ cs(S)`.**

This is the strengthening of `Work.SSGRoute.ZConstruction.auxDatum_realisation_of_counting` in which
the realised cocycle `yAux` is required, in addition, to *vanish* on the level-`K` local group of
every finite place which is `G_k`-conjugate into `Te` but not into `S` (the clause `hvan` of
`Work.SSGRoute.zHyp_of_prescribed_localData`, i.e. the vanishing of the §4 auxiliary class `ỹ` at the
places of `cs(S') ∖ cs(S)`).

The proof is that of the base realisation (a single application of the level-`K` degree-one
realisation `Work.SSGRoute.ZConstruction.levelK_realisation_of_counting` with datum `auxDatum K S ν`),
together with the observation that the extra clause is *already* a consequence of the pointwise
agreement of the realised cocycle with `auxDatum K S ν` at the place set `Te`: a place `B` that is
`G_k`-conjugate into `Te` but not into `S` has, by the cover hypothesis `hTecov`, a level-`K`
conjugate `A' ∈ Te`; the datum at `A'` is *zero* (if `A'` were `S`-conjugate then `B` would be too),
and `z` agrees with `auxDatum K S ν A' = 0` on the local group of `A'`; this propagates to the local
group of `B` along level-`K` conjugacy (`Work.SSGRoute.ZConstruction.kConj_of_local_agree`). -/
theorem auxDatum_realisation_of_counting_vanishing (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
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
    (hTecov : ∀ B : ValuationSubring Ω, (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ Te, Work.SSGRoute.KConj K A' B)
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
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0) ∧
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
  -- (2) `z` is additive on the level-`K` subgroup `G_K`.
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    have h := hzc g hg h hh
    rwa [Work.SSGRoute.ZDataMup.res_eq_one_of_mem_fixingSubgroup hg, one_smul] at h
  refine ⟨z, hzc, hzl, ?_, ?_, ?_⟩
  -- (3) the prescription at every place `G_k`-conjugate into `S`: transport the agreement at the
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
    exact Work.SSGRoute.ZConstruction.kConj_of_local_agree (z := z) (w := ν)
      hzadd hν.add hA'B hagree σ hσ
  -- (4) the vanishing prescription at places `G_k`-conjugate into `Te` but not into `S`: take the
  -- level-`K` representative `A' ∈ Te` of the level-`K` class of `B` (`hTecov`), where the datum
  -- `auxDatum K S ν A'` is `0` because `A'` too is not `S`-conjugate, and transport the agreement
  -- `z = 0` from the local group of `A'` to that of `B`.
  · intro B hB hnotS hconjTe σ hσ
    obtain ⟨A', hA'Te, hA'B⟩ := hTecov B hconjTe
    have hnotS' : ∀ A'' ∈ S, ¬ SSGRoute.IsConjPlace k A'' A' := by
      intro A'' hA'' hc
      exact hnotS A'' hA'' (SSGRoute.isConjPlace_trans hc (kConj_isConjPlace hA'B))
    have hzero : ∀ τ, Work.SSGRoute.auxDatum (p := p) K S ν A' τ = 0 := by
      intro τ
      simp only [Work.SSGRoute.auxDatum]
      rw [if_neg]
      · rfl
      · rintro ⟨A'', hA'', hc⟩
        exact hnotS' A'' hA'' hc
    have hagree0 : ∀ ρ ∈ SSGRoute.decomp k A' ⊓ K.fixingSubgroup,
        z ρ = (fun _ : Ω ≃ₐ[k] Ω => (0 : ZMod p)) ρ := by
      intro ρ hρ
      have h := (Work.SSGRoute.ZDataMup.sub_isCoboundaryOn_iff_eqOn (K := K)
        (fun x hx => (Subgroup.mem_inf.mp hx).2) z
        (Work.SSGRoute.auxDatum (p := p) K S ν A')).mp (hzcob A' hA'Te) ρ hρ
      rw [h]
      exact hzero ρ
    have h0add : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
        (fun _ : Ω ≃ₐ[k] Ω => (0 : ZMod p)) (g * h) =
          (fun _ : Ω ≃ₐ[k] Ω => (0 : ZMod p)) g +
            (fun _ : Ω ≃ₐ[k] Ω => (0 : ZMod p)) h := by
      intro g hg h hh
      simp
    exact Work.SSGRoute.ZConstruction.kConj_of_local_agree
      (z := z) (w := fun _ : Ω ≃ₐ[k] Ω => (0 : ZMod p)) hzadd h0add hA'B hagree0 σ hσ
  -- (5) the vanishing clause: a place that is not conjugate into `Te` is a fortiori not
  -- level-`K`-conjugate to an element of `Te`, where the realisation is unramified.
  · intro B hB hnot hns σ hσK hσI
    refine hzunr B hB ?_ σ hσK hσI
    intro A hA hconj
    exact hnot A hA (Work.SSGRoute.ZConstruction.kConj_isConjPlace
      (Work.SSGRoute.kConj_of_forall_mem hconj))

end Work.SSGRoute.ZConstruction
