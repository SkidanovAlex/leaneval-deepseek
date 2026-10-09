import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
import Submission.Work.SSGRoute.ZConstruction.AuxChase
import Submission.Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap
import Submission.Work.SSGRoute.ZConstruction.ZDataAux
import Submission.Work.SSGRoute.ZConstruction.ZDataInduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `AuxExists` from the *unmixed* realisation gate and the no-gap condition

## The point of this file

The p. 18 auxiliary class of Schmidt--Wingberg is produced by the degree-one Tate--Poitou
realisation of the prescribed datum `Work.SSGRoute.auxDatum K S ν` (the local data of the
one-dimensional datum `ν` at the places of `cs(S)`, extended by zero).  The realisation is applied
at a place set `T'` of level-`K` representatives of `cs(S')` and its **primal** condition is

> `z₁` is unramified at every finite place outside `cs(T')` that is not split in the level `M`
> of the *other* summand of the §4 induction (`M = N = N₀ ⊔ Λ` in
> `Work.SSGRoute.z_data_of_spanning_of_aux`).

The **exactness** of the level-`K` Poitou--Tate sequence identifies the image of the localisation
map with the annihilator of the *dual* Selmer group, and the dual of the primal above is

> `Work.SSGRoute.IsRelaxedDual K M T'`  (duals unramified outside `cs(T')`, locally zero at the
> `M`-split places outside `cs(T')`).

Since `Λ ≤ M`, `IsRelaxedDual K M T` is strictly **larger** than `IsRelaxedDual K Λ T`: the
relaxation level of the dual must be the level of the primal.  The p. 18 product-formula chase
produces orthogonality only against a family in which the dual is *locally zero* at the places
where the datum ramifies; `Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap`
(`Submission/Work/SSGRoute/ZConstruction/auxDatum_orthogonal_relaxed_noGap.lean`, proved) is the
sharp form: for `Λ ≤ M` it gives orthogonality against the whole family `IsRelaxedDual K M T`
**provided** the datum is unramified at the places outside `cs(S)` that are `Λ`-split but not
`M`-split.  That is the hypothesis `AuxGapFun` below.

In the paper's setting the hypothesis is *vacuous*: Schmidt--Wingberg assume (H1) that `y` is
unramified at every prime `P ∉ T(K)`, so the datum is unramified everywhere outside `cs(S)`
(`auxGapFun_of_unramified`).  In the formalised setting the hypotheses on `y` (`ZHyp`: `hyS`,
`hyT`) are weaker -- they only forbid ramification at the `¬Λ`-split places outside `cs(S)` and at
the places of `cs(S)` -- so the no-gap condition is an extra requirement on the datum.  It is the
*only* extra requirement: with it, `AuxExists` follows from the local Tate pairing gate and the
**unmixed** realisation gate at every level.

## The corrected gate list

`Work.SSGRoute.auxExists_of_pairing_and_realisation` (`ZConstruction/AuxAssembly.lean`) consumes
the *mixed* gate `∀ M, AuxRealisationExt K Λ M` (dual relaxed at `Λ`, primal at `M`), whose
hypothesis is supplied by the (proved) chase at `Λ`; that gate is not the statement of
Poitou--Tate, and its difference from the PT statement is the "slack" recorded in
`ZConstruction/AuxRealisationSlack.lean` (an open definition-level restatement).  The present file
replaces it by the **unmixed** gate `∀ M, AuxRealisationExt K M M`, which *is* the PT statement,
whose hypothesis is supplied by `auxDatum_orthogonal_relaxed_noGap` under `AuxGapProv` -- so the
node's obligation becomes

    Work.SSGRoute.MupGate K  +  Work.SSGRoute.AuxPairingGate K
      + (∀ M, AuxRealisationExt K M M)     -- the standard realisation at level `M` (PT exactness)
      + AuxGapProv                         -- the no-gap condition on the datum

with

* `AuxRealisationExt K M M` supplied by the level-`K` counting identity (`ZSplit/PT` lanes), and
* `AuxGapProv` automatic in the paper's (H1) setting (`auxGapFun_of_unramified`), and
  automatic for the *line component* as soon as the span of the ramification of `y` at the
  `Λ`-split places outside `cs(S)` is a proper subspace of the coefficient module
  (`auxGapFun_comp_of_junkSpan_le`).
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

/-! ## The no-gap condition -/

/-- **The no-gap condition for a datum `ν`**: `ν` is unramified at the places outside `cs(S)` that
are `Λ`-split but not `N`-split.

This is exactly the hypothesis under which the p. 18 chase
`Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap` produces orthogonality against the
dual family `Work.SSGRoute.IsRelaxedDual K N T` of the primal at level `N`.  It is vacuous when
`N ≤ Λ` (no place is `Λ`-split and not `N`-split), and it is automatic when `ν` is unramified at
every place outside `cs(S)` -- the paper's (H1). -/
def AuxGapFun (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (N : IntermediateField k Ω) {E : Type} [Zero E] (ν : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
    ¬ SSGRoute.IsSplitIn k N B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0

/-- The no-gap condition is monotone in the level `N`: a larger level splits fewer places, so the
condition gets stronger. -/
theorem AuxGapFun.mono {K Λ N N' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [Zero E] {ν : (Ω ≃ₐ[k] Ω) → E}
    (hle : N ≤ N') (h : AuxGapFun K Λ S N' ν) : AuxGapFun K Λ S N ν :=
  fun B hB hnot hsp hnspt σ hσK hσI =>
    h B hB hnot hsp (fun hsplit => hnspt (le_trans hsplit (IntermediateField.fixingSubgroup_le hle)))
      σ hσK hσI

/-- The no-gap condition is vacuous when the level is contained in `Λ`. -/
theorem auxGapFun_of_le {K Λ N : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [Zero E] {ν : (Ω ≃ₐ[k] Ω) → E} (h : N ≤ Λ) : AuxGapFun K Λ S N ν :=
  fun _B _ _ hsp hnspt _ _ _ =>
    absurd (le_trans hsp (IntermediateField.fixingSubgroup_le h)) hnspt

/-- **In the paper's setting the no-gap condition is automatic**: a datum which is unramified at
every finite place outside `cs(S)` satisfies it at every level.  (Schmidt--Wingberg's hypothesis
(H1) is exactly this unramifiedness for the datum `y` at the places outside `T(K)`.) -/
theorem auxGapFun_of_unramified {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [Zero E] {ν : (Ω ≃ₐ[k] Ω) → E}
    (h : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) :
    AuxGapFun K Λ S N ν :=
  fun B hB hnot _ _ σ hσK hσI => h B hB hnot σ hσK hσI

/-- **The no-gap condition transported along a linear map which kills the ramification of the
datum at the `Λ`-split places outside `cs(S)`.**  This is the form in which the condition is
verified for the *line component* `π ∘ y` of the §4 induction. -/
theorem auxGapFun_comp_of_forall_eq_zero {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (π : E →+ E') (y : (Ω ≃ₐ[k] Ω) → E)
    (h : ∀ (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω), SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      σ ∈ K.fixingSubgroup → SSGRoute.IsInertia k B σ → π (y σ) = 0) :
    AuxGapFun K Λ S N (fun σ => π (y σ)) :=
  fun B hB hnot hsp _ σ hσK hσI => h B σ hB hnot hsp hσK hσI

/-! ## The no-gap provision -/

/-- **The no-gap provision** at the pair `(Λ, S)`: every one-dimensional-coefficient datum
satisfying `ZHyp` at `(Λ, S)` satisfies the no-gap condition at every level `N ⊇ Λ`.

This is the hypothesis that the corrected assembly
`Work.SSGRoute.ZConstruction.auxExists_of_pairing_and_unmixed_and_gap` carries in place of the
"slack" of `ZConstruction/AuxRealisationSlack.lean`.  It is automatic in the paper's setting
(`auxGapFun_of_unramified`), and it holds for the line component of §4 whenever the ramification of
the datum at the `Λ`-split places outside `cs(S)` misses at least one line of the coefficient
module (`auxGapFun_comp_of_forall_eq_zero`). -/
def AuxGapProv (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) : Prop :=
  ∀ (N : IntermediateField k Ω), Λ ≤ N → ∀ {E : Type} [AddCommGroup E]
    (ν : (Ω ≃ₐ[k] Ω) → E), Work.SSGRoute.ZHyp (p := p) K Λ S ν →
    AuxGapFun K Λ S N ν

/-! ## The corrected assembly -/

/-- **`AuxExists` from the pairing gate, the *unmixed* realisation gate and the no-gap provision.**

This is `Work.SSGRoute.auxExists_of_pairing_and_realisation` with the *mixed* realisation gate
`∀ M, AuxRealisationExt K Λ M` (whose hypothesis is the chase at the relaxation level `Λ`)
replaced by the **unmixed** gate `∀ M, AuxRealisationExt K M M`, which is the statement matched by
the level-`K` Poitou--Tate exactness: the dual of the primal "unramified at the places outside
`cs(T')` that are not `M`-split" is `IsRelaxedDual K M T'`.  Its orthogonality hypothesis is
supplied by the proved no-gap chase
`Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap` under `AuxGapProv`. -/
theorem auxExists_of_pairing_and_unmixed_and_gap {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      Work.SSGRoute.AuxRealisationExt (p := p) K M M)
    (hgap : AuxGapProv (p := p) K Λ S)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.AuxExists (p := p) K Λ S := by
  classical
  refine Work.SSGRoute.auxExists_of_weakened (p := p) ?_
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub _hS'ram L _instLadd _instLmod _instLfin
    hL y₁ hy₁
  -- (1) the local Tate system
  obtain ⟨pair, hpair, hprod, hunr⟩ := hP
  -- (2) the base place set: representatives of the level-`K` classes of `cs(S)`
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ :=
    ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S hSfin
  -- (3) the enlarged place set: representatives of the level-`K` classes of `cs(S')`
  obtain ⟨T'', hT''fin, hT''disj, hT''conj, hT''cov⟩ :=
    ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S' hS'fin
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
    · exact absurd ⟨B, hB, ZConstruction.kConj_symm hAB⟩ (Finset.mem_filter.mp hA).2
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
      exact ⟨t, hT'T t ht, ZConstruction.kConj_trans htA hc⟩
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
        have hEq : A = t := hT'disj A hA t (hT'T t ht) (ZConstruction.kConj_symm hc)
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
        have hEq : A = t := hT'disj A hA t (hT'T t ht) (ZConstruction.kConj_symm hc)
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
      have hEq : A = t := hT'disj A hAT' t (hT'T t ht) (ZConstruction.kConj_symm hc)
      exact hAnT (hEq ▸ ht)
    simp only [hf, Work.SSGRoute.auxDatum]
    rw [if_neg hnot]
  -- (9) the orthogonality: the no-gap chase at the relaxation level `N`
  have horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, Work.SSGRoute.IsRelaxedDual (p := p) K N T b →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
    intro b hb
    exact auxDatum_orthogonal_relaxed_noGap (p := p) (K := K) (Λ := Λ) (M := N) hΛN
      (S := S) (T := T) (Te := T') pair hpair hprod hunr hSfin hTfin hTdisj hTconj hTcov
      hT'T hT'fin hT'disj hνhyp (hgap N hΛN ν hνhyp) hb
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
        (SSGRoute.isConjPlace_trans hc'' (ZConstruction.kConj_isConjPlace hc))
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
      show e (z ρ) = y₁ ρ
      rw [hzagree t (hT'T t ht) ρ hρ, hfT t ht]
      show e (e.symm (y₁ ρ)) = y₁ ρ
      rw [LinearEquiv.apply_symm_apply]
    exact ZConstruction.kConj_of_local_agree (k := k) (Ω := Ω)
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
        (SSGRoute.isConjPlace_trans hc'' (ZConstruction.kConj_isConjPlace hc))
    have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAnT⟩
    have hloc : ∀ ρ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        yAux ρ = (0 : (Ω ≃ₐ[k] Ω) → L) ρ := by
      intro ρ hρ
      show e (z ρ) = 0
      rw [hzagree A hA ρ hρ, hfzero A hmem]
      simp
    exact ZConstruction.kConj_of_local_agree (k := k) (Ω := Ω)
      (fun g hg h hh => by
        show e (z (g * h)) = e (z g) + e (z h)
        rw [hzadd g hg h hh, map_add])
      (fun g hg h hh => by simp) hc hloc σ
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hσ).1, (Subgroup.mem_inf.mp hσ).2⟩)


/-! ## The no-gap condition for the line component of the §4 induction -/

/-- **The span of the ramification of `y` at the `Λ`-split places outside `cs(S)`**: the additive
subgroup of `E` generated by the values `y σ` at the elements `σ` of `G_K` which lie in the inertia
group of a finite place `B ∉ cs(S)` that splits completely in `Λ`.

These are exactly the places at which the datum of §4 is allowed to ramify (`ZHyp.hyS` says
nothing there), and they are the places at which the no-gap condition has to be checked for the
line component `π₁ ∘ y` of the induction.  If the line `L = ker π₀` of the decomposition
`E = E₀ ⊕ L` is chosen inside a complement of `junkSpan`, then the *other* component `π₀ ∘ y` does
not see the ramification, and `π₁ ∘ y` is unramified there -- which is `AuxGapFun`. -/
def junkSpan (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) {E : Type}
    [AddCommGroup E] (y : (Ω ≃ₐ[k] Ω) → E) : AddSubgroup E :=
  AddSubgroup.closure {v : E | ∃ (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω),
    SSGRoute.IsFinPlace k B ∧ (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      SSGRoute.IsSplitIn k Λ B ∧ σ ∈ K.fixingSubgroup ∧ SSGRoute.IsInertia k B σ ∧ y σ = v}

/-- **The no-gap condition is automatic for a component whose projection kills the junk
ramification.**  If `E₀` contains `junkSpan K Λ S y` and `π` vanishes on `E₀`, then `π ∘ y`
satisfies `AuxGapFun` at every level.

In the induction `π` is the projection onto the line `L` of the decomposition `E = E₀ ⊕ L` with
`E₀ ⊇ junkSpan`: the hypothesis of this lemma is then satisfied because the junk places are exactly
the places where the other component `(1 - π) ∘ y` carries all the ramification. -/
theorem auxGapFun_comp_of_junkSpan_le {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (y : (Ω ≃ₐ[k] Ω) → E) (E₀ : AddSubgroup E) (hsub : junkSpan K Λ S y ≤ E₀)
    (π : E →+ E') (hπ : ∀ x ∈ E₀, π x = 0) :
    AuxGapFun K Λ S N (fun σ => π (y σ)) := by
  refine auxGapFun_comp_of_forall_eq_zero π y ?_
  intro B σ hB hnot hsp hσK hσI
  exact hπ (y σ) (hsub (AddSubgroup.subset_closure ⟨B, σ, hB, hnot, hsp, hσK, hσI, rfl⟩))

/-- The no-gap provision is automatic whenever the datum is unramified outside `cs(S)` (the paper's
(H1)). -/
theorem auxGapProv_of_unramified {K Λ : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)}
    (h : ∀ {E : Type} [AddCommGroup E] (ν : (Ω ≃ₐ[k] Ω) → E),
      Work.SSGRoute.ZHyp (p := p) K Λ S ν →
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) :
    AuxGapProv (p := p) K Λ S := by
  intro N _hΛN E _instE ν hν
  exact auxGapFun_of_unramified (h ν hν)

/-! ## The `z`-data of the node from the corrected gate list -/

/-- **The `z`-data of the node from the corrected gate list.**
`hmup` is the one-dimensional gate (the two `μ_p` cores of Schmidt--Wingberg §4), `hP` the local
Tate system with the product formula, `hU` the **unmixed** degree-one realisation at every level
(the level-`K` Poitou--Tate exactness, supplied by the counting identity of the `ZSplit`/`PT`
lanes), and `hgap` the no-gap provision `AuxGapProv` of this file. -/
theorem z_data_general_of_unmixed_gates_gap {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hmup : Work.SSGRoute.MupGate (p := p) K) (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      Work.SSGRoute.AuxRealisationExt (p := p) K M M)
    (hgap : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), AuxGapProv (p := p) K Λ S) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), Work.SSGRoute.ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      Work.SSGRoute.ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, Work.SSGRoute.HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF y hy
  exact Work.SSGRoute.z_data_general_of_mup_and_aux (p := p) hAmb hmup
    (auxExists_of_pairing_and_unmixed_and_gap (p := p) (K := K) (Λ := Λ)
      hP hU (hgap Λ S) hAmb.hSfin) E y hy

/-! ## The gate matched by Poitou--Tate -/

/-- **Gate (R′): the degree-one realisation in the form matched by the level-`K` Poitou--Tate
exactness.**

This is `Work.SSGRoute.AuxRealisationExt K M M` with the *unramifiedness clause of the conclusion
stated over the base place set `T`* rather than over the enlarged set `T'`:

> the realised class `z` is unramified at every finite place `B` outside `cs(T)` that is not split
> in `M`.

The primal condition of the realisation is therefore "unramified at the places outside `cs(T)` that
are not `M`-split", whose Poitou--Tate dual is *exactly* `Work.SSGRoute.IsRelaxedDual K M T`:

* the dual classes are unramified at the places outside `cs(T)` that are not `M`-split (they are the
  classes of `H¹(k_{cs(M|k) ∪ cs(T)}|K, μ_p)`), and
* they vanish at the `M`-split places outside `cs(T)` (which is the same as outside `cs(T')` in the
  application, since the places of `T' ∖ T` are ramified in the level `M` and hence not `M`-split).

Both clauses are precisely the two clauses of `IsRelaxedDual K M T`, which is the family against
which the p. 18 chase -- in its sharp form
`Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap`, under the no-gap provision
`AuxGapProv` -- produces orthogonality.  By contrast the *hypothesis* of
`Work.SSGRoute.AuxRealisationExt K M M` is the same family while its conclusion is weaker (it
exempts the places of `cs(T') ∖ cs(T)` from the unramifiedness requirement), so it is strictly
stronger than the Poitou--Tate statement; in the application the exemption is anyway void, because
the datum prescribes the value `0` at the places of `T' ∖ T`. -/
def AuxRealisationT (K M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p),
    ZDataMup.IsLocalTateSystem p k Ω K pair →
    ZDataMup.IsProductFormula p k Ω K pair →
    IsUnramifiedOrthogonal (p := p) K pair →
    ∀ (T T' : Finset (ValuationSubring Ω)),
      (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T', ∀ B ∈ T', KConj K A B → A = B) →
      (∀ A ∈ T, A ∈ T') →
    ∀ (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T' \ T, f A = 0) →
      (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K M T b →
        ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0) →
      ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
        SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
        (∀ A ∈ T', ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T, ¬ KConj K A B) → ¬ SSGRoute.IsSplitIn k M B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)

/-- The Poitou--Tate-matched gate implies the gate `Work.SSGRoute.AuxRealisationExt K M M`
consumed by the existing assembly: the latter only requires the realised class to be unramified at
the places of `cs(T') ∖ cs(T)` as well, which is contained in the requirement of the former. -/
theorem auxRealisationExt_of_realisationT {K M : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (h : AuxRealisationT (p := p) K M) :
    Work.SSGRoute.AuxRealisationExt (p := p) K M M := by
  intro pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  obtain ⟨z, hzc, hzl, hza, hzi, hzu⟩ :=
    h pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  exact ⟨z, hzc, hzl, hza, hzi, fun B hB hnotT' hnsplit =>
    hzu B hB (fun A hA hc => hnotT' A (hT'T A hA) hc) hnsplit⟩

/-- **`AuxExists` from the pairing gate, the Poitou--Tate-matched realisation gate and the no-gap
provision.** -/
theorem auxExists_of_pairing_and_realisationT_and_gap {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      AuxRealisationT (p := p) K M)
    (hgap : AuxGapProv (p := p) K Λ S)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.AuxExists (p := p) K Λ S :=
  auxExists_of_pairing_and_unmixed_and_gap (p := p) hP
    (fun M _ _ => auxRealisationExt_of_realisationT (p := p) (hU M)) hgap hSfin

/-- **The `z`-data of the node from the Poitou--Tate-matched gate list.** -/
theorem z_data_general_of_realisationT_gates {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hmup : Work.SSGRoute.MupGate (p := p) K) (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      AuxRealisationT (p := p) K M)
    (hgap : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), AuxGapProv (p := p) K Λ S) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), Work.SSGRoute.ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      Work.SSGRoute.ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, Work.SSGRoute.HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF y hy
  exact Work.SSGRoute.z_data_general_of_mup_and_aux (p := p) hAmb hmup
    (auxExists_of_pairing_and_realisationT_and_gap (p := p) (K := K) (Λ := Λ)
      hP hU (hgap Λ S) hAmb.hSfin) E y hy

/-- **The no-gap condition is insensitive to the coefficient module**: it only asks for the vanishing
of the datum on the inertia of the gap places, so it transports along an additive equivalence. -/
theorem AuxGapFun.of_addEquiv {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (e : E' ≃+ E) {ν : (Ω ≃ₐ[k] Ω) → E} (h : AuxGapFun K Λ S N ν) :
    AuxGapFun K Λ S N (fun σ => e.symm (ν σ)) :=
  fun B hB hnot hsp hnspt σ hσK hσI => by
    show e.symm (ν σ) = 0
    rw [h B hB hnot hsp hnspt σ hσK hσI, map_zero]

/-- **The auxiliary-class obligation of Schmidt--Wingberg §4 with the no-gap hypothesis.**

This is `Work.SSGRoute.AuxExists` for the *one-dimensional* datum `y₁` of the §4 induction, with the
extra hypothesis `AuxGapFun K Λ S N y₁` -- the no-gap condition, which is what the p. 18 chase
`Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap` needs in order to produce the
orthogonality of the prescribed datum against the dual family `IsRelaxedDual K N T`.

The uniform provision `AuxGapProv` (for *every* one-dimensional `ZHyp` datum) is stronger than
necessary and may fail for individual data (the prescribed datum may vanish, in which case the
orthogonality is trivial although the datum ramifies at a gap place).  For the line component
`π₁ ∘ y` of the §4 induction the hypothesis is *arrangeable*: if the span `junkSpan K Λ S y` of the
ramification of `y` at the `Λ`-split places outside `cs(S)` is a proper subspace of the coefficient
module, the line `L = ker π₀` may be chosen in a complement of it, and then `π₁ ∘ y` satisfies
`AuxGapFun` at every level (`auxGapFun_comp_of_junkSpan_le`). -/
def AuxExistsGap (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω)) : Prop :=
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
      Work.SSGRoute.ZHyp (p := p) K N S' yAux ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0)

/-- If the no-gap condition holds for *every* one-dimensional `ZHyp` datum at `(Λ,S)` (the
provision `AuxGapProv`), then the obligation with the no-gap hypothesis implies the obligation. -/
theorem auxExists_of_auxExistsGap_of_gap {K Λ : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} (h : AuxExistsGap (p := p) K Λ S)
    (hgap : AuxGapProv (p := p) K Λ S) :
    Work.SSGRoute.AuxExists (p := p) K Λ S := by
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub hS'ram L _instLadd _instLmod _instLfin hL
    y₁ hy₁
  exact h N hΛN S' hS'fin hS'disj hS'sub hS'ram L hL y₁ hy₁ (hgap N hΛN y₁ hy₁)

/-! ## The `z`-data in Schmidt--Wingberg's (H1) regime -/

/-- **The `z`-data of the node in the regime where the datum is unramified outside `cs(S)`.**

If every `ZHyp` datum at `(Λ,S)` is unramified at *every* finite place outside `cs(S)` -- i.e. the
datum is (H1)-unramified, which is the hypothesis Schmidt--Wingberg's Theorem 13 imposes on `y` --
then the no-gap provision holds (`auxGapProv_of_unramified`) and the node's `z`-data follows from the
one-dimensional gate, the pairing gate and the unmixed realisation gate, with **no** extra
hypothesis.

The hypotheses of the node (`ZHyp.hyS`, `ZHyp.hyT`) are strictly weaker at the `Λ`-split places
outside `cs(S)`, where they only forbid ramification of the inertia *outside* `Λ`; the difference is
the "junk" ramification measured by `junkSpan K Λ S y`, and this lemma records that the
chase-based route is sound precisely in the regime where it vanishes. -/
theorem z_data_general_of_unmixed_gates_of_unramified {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hmup : Work.SSGRoute.MupGate (p := p) K) (hP : Work.SSGRoute.AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      Work.SSGRoute.AuxRealisationExt (p := p) K M M)
    (hAmb : Work.SSGRoute.ZAmbient (p := p) K Λ S)
    (hunr : ∀ {E : Type} [AddCommGroup E] (ν : (Ω ≃ₐ[k] Ω) → E),
      Work.SSGRoute.ZHyp (p := p) K Λ S ν →
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      Work.SSGRoute.ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, Work.SSGRoute.HasZData K Λ S y z := by
  intro E _instE _instM _instF y hy
  exact Work.SSGRoute.z_data_general_of_mup_and_aux (p := p) hAmb hmup
    (auxExists_of_pairing_and_unmixed_and_gap (p := p) (K := K) (Λ := Λ) hP hU
      (auxGapProv_of_unramified (p := p) hunr) hAmb.hSfin) E y hy

end Work.SSGRoute.ZConstruction
