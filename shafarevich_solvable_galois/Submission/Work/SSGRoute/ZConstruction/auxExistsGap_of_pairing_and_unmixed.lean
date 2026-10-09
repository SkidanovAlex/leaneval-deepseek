import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxExistsUnmixed
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
import Submission.Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `AuxExistsGap` from the pairing gate and the *unmixed* realisation gate

`Work.SSGRoute.ZConstruction.AuxExistsGap K Λ S` (`ZConstruction/AuxExistsUnmixed.lean`) is the
auxiliary-class obligation of Schmidt--Wingberg §4 for a **one-dimensional** datum `y₁` which
additionally satisfies the no-gap condition `AuxGapFun K Λ S N y₁` at the level `N` of the
enlargement.  It is `Work.SSGRoute.AuxExists` with the uniform provision `AuxGapProv` (for *every*
one-dimensional `ZHyp` datum) replaced by the *pointwise* hypothesis on the datum at hand -- which is
strictly weaker, since `AuxGapProv` may fail for individual data.

The present file proves it from

* `Work.SSGRoute.AuxPairingGate K` -- the level-`K` local Tate system with the product formula, and
* `∀ M, Work.SSGRoute.AuxRealisationExt K M M` -- the **unmixed** degree-one realisation, i.e. the
  statement matched by the level-`K` Poitou--Tate exactness (primal and dual local conditions at the
  same level `M`),

by the *same* assembly as `Work.SSGRoute.ZConstruction.auxExists_of_pairing_and_unmixed_and_gap`,
except that the orthogonality hypothesis of the realisation is discharged by the chase
`Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap` at the relaxation level `N` using
the pointwise no-gap hypothesis, transported to the `ZMod p`-valued datum by
`Work.SSGRoute.ZConstruction.AuxGapFun.of_addEquiv`.

The proof proceeds by first establishing the weakened form (`AuxExistsGapWeakened`, the analogue of
`Work.SSGRoute.AuxExistsWeakened` with the no-gap hypothesis) and then assembling the `ZHyp`
structure from it exactly as `Work.SSGRoute.auxExists_of_weakened` does.
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The weakened auxiliary-class obligation with the no-gap hypothesis.**  This is
`Work.SSGRoute.AuxExistsWeakened` with the extra hypothesis `AuxGapFun K Λ S N y₁` on the
one-dimensional datum: the conclusion is the six-component form of the realised class (additivity,
local constancy, unramifiedness outside `cs(S')` at the `¬N`-split places, vanishing on the
involutions, agreement with `y₁` on `cs(S)`, and vanishing on `cs(S') ∖ cs(S)`), from which the
`ZHyp` structure at `(N, S')` is reassembled in the proof of the main theorem. -/
private def AuxExistsGapWeakened (K Λ : IntermediateField k Ω)
    (S : Finset (ValuationSubring Ω)) : Prop :=
  ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
    ∀ (S' : Finset (ValuationSubring Ω)),
    (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ S', SSGRoute.IsConjPlace k A' B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
      ∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
    ∀ (L : Type) [AddCommGroup L] [Module (ZMod p) L] [Finite L],
      Module.finrank (ZMod p) L = 1 →
    ∀ (y₁ : (Ω ≃ₐ[k] Ω) → L), Work.SSGRoute.ZHyp (p := p) K Λ S y₁ →
    AuxGapFun K Λ S N y₁ →
    ∃ yAux : (Ω ≃ₐ[k] Ω) → L,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yAux (g * h) = yAux g + yAux h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → yAux c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0)

/-- **`AuxExistsGap` from the pairing gate and the *unmixed* realisation gate.** -/
theorem auxExistsGap_of_pairing_and_unmixed {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      Work.SSGRoute.AuxRealisationExt (p := p) K M M)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZConstruction.AuxExistsGap (p := p) K Λ S := by
  classical
  -- (A) the weakened obligation with the pointwise no-gap hypothesis
  have hweak : AuxExistsGapWeakened (p := p) K Λ S := by
    intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub _hS'ram L _instLadd _instLmod _instLfin
      hL y₁ hy₁ hgapfun
    -- (1) the local Tate system
    obtain ⟨pair, hpair, hprod, hunr⟩ := hP
    -- (2) the base place set: representatives of the level-`K` classes of `cs(S)`
    obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ :=
      exists_KConj_reps (k := k) (Ω := Ω) K S hSfin
    -- (3) the enlarged place set: representatives of the level-`K` classes of `cs(S')`
    obtain ⟨T'', hT''fin, hT''disj, hT''conj, hT''cov⟩ :=
      exists_KConj_reps (k := k) (Ω := Ω) K S' hS'fin
    -- (4) the realisation place set: `T` together with the new classes of `cs(S')`
    set T' : Finset (ValuationSubring Ω) := T ∪ T''.filter (fun A => ¬ ∃ t ∈ T, KConj K t A) with hT'
    have hT'T : ∀ A ∈ T, A ∈ T' := by
      intro A hA
      rw [hT']
      exact Finset.mem_union_left _ hA
    have hT'fin : ∀ A ∈ T', SSGRoute.IsFinPlace k A := by
      intro A hA
      rw [hT', Finset.mem_union] at hA
      rcases hA with hA | hA
      · exact hTfin A hA
      · exact hT''fin A (Finset.mem_filter.mp hA).1
    have hT'disj : ∀ A ∈ T', ∀ B ∈ T', KConj K A B → A = B := by
      intro A hA B hB hAB
      rw [hT', Finset.mem_union] at hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · exact hTdisj A hA B hB hAB
      · exact absurd ⟨A, hA, hAB⟩ (Finset.mem_filter.mp hB).2
      · exact absurd ⟨B, hB, kConj_symm hAB⟩ (Finset.mem_filter.mp hA).2
      · exact hT''disj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hAB
    have hT'sub : ∀ A ∈ T', ∃ A' ∈ S', SSGRoute.IsConjPlace k A' A := by
      intro A hA
      rw [hT', Finset.mem_union] at hA
      rcases hA with hA | hA
      · obtain ⟨A'', hA'', hc⟩ := hTconj A hA
        exact hS'sub A ⟨A'', hA'', hc⟩
      · exact hT''conj A (Finset.mem_filter.mp hA).1
    have hT'cov : ∀ B : ValuationSubring Ω, (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∃ A' ∈ T', KConj K A' B := by
      intro B hB
      obtain ⟨A, hA, hc⟩ := hT''cov B hB
      by_cases hnew : ∃ t ∈ T, KConj K t A
      · obtain ⟨t, ht, htA⟩ := hnew
        exact ⟨t, hT'T t ht, kConj_trans htA hc⟩
      · exact ⟨A, by rw [hT']; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hnew⟩), hc⟩
    -- (5) the one-dimensional module `L` is `ZMod p`
    haveI : FiniteDimensional (ZMod p) L := Module.Finite.of_finite
    haveI : Nontrivial L := Module.finrank_pos_iff.mp (by rw [hL]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : L)
    have hap : ∀ x : ZMod p, LinearMap.toSpanSingleton (ZMod p) L v x = x • v := by
      intro x
      have h := map_smul (LinearMap.toSpanSingleton (ZMod p) L v) x (1 : ZMod p)
      rw [show x • (1 : ZMod p) = x from by rw [smul_eq_mul, mul_one],
        LinearMap.toSpanSingleton_apply_one] at h
      exact h
    have hinj : Function.Injective (LinearMap.toSpanSingleton (ZMod p) L v) := by
      intro a b hab
      have h2 : a • v = b • v := by rw [← hap a, ← hap b]; exact hab
      have h3 : (a - b) • v = 0 := by rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have hrank : Module.finrank (ZMod p) (ZMod p) = Module.finrank (ZMod p) L := by
      rw [hL, CommSemiring.finrank_self]
    let e : ZMod p ≃ₗ[ZMod p] L := LinearEquiv.ofInjectiveOfFinrankEq _ hinj hrank
    -- (6) the datum transported to `ZMod p`
    set ν : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => e.symm (y₁ σ) with hν
    have hνhyp : Work.SSGRoute.ZHyp (p := p) K Λ S ν :=
      Work.SSGRoute.ZHyp.mapAdd (f := (e.symm : L →ₗ[ZMod p] ZMod p).toAddMonoidHom) hy₁
    -- (7) the prescribed data at `T'`
    set f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
      fun A => Work.SSGRoute.auxDatum (p := p) K S ν A with hf
    have hfT : ∀ A ∈ T, f A = ν := by
      intro A hA
      simp only [hf, Work.SSGRoute.auxDatum]
      rw [if_pos (hTconj A hA)]
    have hfcoc : ∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
      intro A hA
      by_cases hAT : A ∈ T
      · rw [hfT A hAT]
        exact Work.SSGRoute.isCocycleOn_of_addOn inf_le_right
          (fun g hg h hh => hνhyp.add g (Subgroup.mem_inf.mp hg).2 h (Subgroup.mem_inf.mp hh).2)
      · have hnot : ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
          intro hconj
          obtain ⟨t, ht, hc⟩ := hTcov A hconj
          have hEq : A = t := hT'disj A hA t (hT'T t ht) (kConj_symm hc)
          exact hAT (hEq ▸ ht)
        have hfz : f A = 0 := by
          simp only [hf, Work.SSGRoute.auxDatum]
          rw [if_neg hnot]
        rw [hfz]
        exact fun g hg h hh => by simp
    have hfloc : ∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
      intro A hA
      by_cases hAT : A ∈ T
      · rw [hfT A hAT]
        exact ZDataMup.isLocConstOn_of_le inf_le_right hνhyp.locconst
      · have hnot : ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
          intro hconj
          obtain ⟨t, ht, hc⟩ := hTcov A hconj
          have hEq : A = t := hT'disj A hA t (hT'T t ht) (kConj_symm hc)
          exact hAT (hEq ▸ ht)
        have hfz : f A = 0 := by
          simp only [hf, Work.SSGRoute.auxDatum]
          rw [if_neg hnot]
        rw [hfz]
        exact ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
    -- (8) the datum is zero on `T' ∖ T`
    have hfzero : ∀ A ∈ T' \ T, f A = 0 := by
      intro A hA
      obtain ⟨hAT', hAnT⟩ := Finset.mem_sdiff.mp hA
      have hnot : ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
        intro hconj
        obtain ⟨t, ht, hc⟩ := hTcov A hconj
        have hEq : A = t := hT'disj A hAT' t (hT'T t ht) (kConj_symm hc)
        exact hAnT (hEq ▸ ht)
      simp only [hf, Work.SSGRoute.auxDatum]
      rw [if_neg hnot]
    -- (9) the orthogonality: the no-gap chase at the relaxation level `N`, with the pointwise
    -- no-gap hypothesis transported to the `ZMod p`-valued datum `ν = e.symm ∘ y₁`
    have horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, Work.SSGRoute.IsRelaxedDual (p := p) K N T b →
        ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
      intro b hb
      exact auxDatum_orthogonal_relaxed_noGap (p := p) (K := K) (Λ := Λ) (M := N) hΛN
        (S := S) (T := T) (Te := T') pair hpair hprod hunr hSfin hTfin hTdisj hTconj hTcov
        hT'T hT'fin hT'disj hνhyp
        (AuxGapFun.of_addEquiv (e := e.toAddEquiv) hgapfun) hb
    -- (10) the realisation at the unmixed level `N`
    obtain ⟨z, hzcoc, hzloc, hzagree, hzinf, hzunr⟩ :=
      hU N pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
    have hzadd := Work.SSGRoute.addOn_of_isCocycleOn hzcoc
    -- (11) the realised class in `L`
    set yAux : (Ω ≃ₐ[k] Ω) → L := fun σ => e (z σ) with hyAux
    refine ⟨yAux, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- additivity
      intro g hg h hh
      show e (z (g * h)) = e (z g) + e (z h)
      rw [hzadd g hg h hh, map_add]
    · -- local constancy
      obtain ⟨U, hUo, hU⟩ := hzloc
      refine ⟨U, hUo, fun g hg u hu huK => ?_⟩
      show e (z (g * u)) = e (z g)
      rw [hU g hg u hu huK]
    · -- `hyS` at `(N,S')`
      intro B hB hnotS hnotsplit σ hσK hσI
      have hnotT' : ∀ A ∈ T', ¬ KConj K A B := by
        intro A hA hc
        obtain ⟨A'', hA'', hc''⟩ := hT'sub A hA
        exact hnotS A'' hA''
          (SSGRoute.isConjPlace_trans hc'' (kConj_isConjPlace hc))
      show e (z σ) = 0
      rw [hzunr B hB hnotT' hnotsplit σ hσK hσI, map_zero]
    · -- vanishing on the involutions
      intro c hc hc2
      show e (z c) = 0
      rw [hzinf c hc hc2, map_zero]
    · -- agreement with `y₁` on the local groups of `cs(S)`
      intro B hB hconj σ hσ
      obtain ⟨t, ht, hc⟩ := hTcov B hconj
      have hloc : ∀ ρ ∈ SSGRoute.decomp k t ⊓ K.fixingSubgroup, yAux ρ = y₁ ρ := by
        intro ρ hρ
        have hρ' : ρ ∈ SSGRoute.decomp k t ⊓ K.fixingSubgroup := hρ
        show e (z ρ) = y₁ ρ
        rw [hzagree t (hT'T t ht) ρ hρ', hfT t ht]
        show e (e.symm (y₁ ρ)) = y₁ ρ
        rw [LinearEquiv.apply_symm_apply]
      exact kConj_of_local_agree (k := k) (Ω := Ω)
        (fun g hg h hh => by
          show e (z (g * h)) = e (z g) + e (z h)
          rw [hzadd g hg h hh, map_add])
        hy₁.add hc hloc σ (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hσ).1, (Subgroup.mem_inf.mp hσ).2⟩)
    · -- vanishing on the local groups of `cs(S') ∖ cs(S)`
      intro B hB hnotS hconj σ hσ
      obtain ⟨A, hA, hc⟩ := hT'cov B hconj
      have hAnT : A ∉ T := by
        intro hAT
        obtain ⟨A'', hA'', hc''⟩ := hTconj A hAT
        exact hnotS A'' hA''
          (SSGRoute.isConjPlace_trans hc'' (kConj_isConjPlace hc))
      have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAnT⟩
      have hloc : ∀ ρ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          yAux ρ = (0 : (Ω ≃ₐ[k] Ω) → L) ρ := by
        intro ρ hρ
        show e (z ρ) = 0
        rw [hzagree A hA ρ hρ, hfzero A hmem]
        simp
      exact kConj_of_local_agree (k := k) (Ω := Ω)
        (fun g hg h hh => by
          show e (z (g * h)) = e (z g) + e (z h)
          rw [hzadd g hg h hh, map_add])
        (fun g hg h hh => by simp) hc hloc σ
        (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hσ).1, (Subgroup.mem_inf.mp hσ).2⟩)
  -- (B) assemble the `ZHyp` structure at `(N, S')` from the weakened witness, exactly as in
  -- `Work.SSGRoute.auxExists_of_weakened`.
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub hS'ram L _instLadd _instLmod _instLfin
    hL y₁ hy₁ hgapfun
  obtain ⟨yAux, hadd, hloc, hyS, hinf, hagree, hvanish⟩ :=
    hweak N hΛN S' hS'fin hS'disj hS'sub hS'ram L hL y₁ hy₁ hgapfun
  have hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → yAux σ = 0 := by
    intro B hB hconj σ hσK hσI
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
      exact hy₁.hyT B hB hconjS σ hσK hσI
    · rw [hvanish B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)]
  have hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → yAux σ = 0 := by
    intro B hB hconj hbad σ hσK hσd
    by_cases hconjS : ∃ A ∈ S, SSGRoute.IsConjPlace k A B
    · rw [hagree B hB hconjS σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
      exact hy₁.hy0 B hB hconjS hbad σ hσK hσd
    · rw [hvanish B hB (fun A hA hc => hconjS ⟨A, hA, hc⟩) hconj σ
        (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
  exact ⟨yAux, ⟨hadd, hloc, hyS, hyT, hy0, hinf⟩, hagree, hvanish⟩

end Work.SSGRoute.ZConstruction
