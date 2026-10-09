import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mixed-level realisation gate, and the arithmetic that it needs beyond Poitou--Tate

## The object

`Work.SSGRoute.AuxRealisationNoInv K Λ M` (`ZConstruction/AuxAssembly.lean`) is the odd-`p` degree-one
realisation gate of the p. 18 auxiliary class of Schmidt--Wingberg section 4.  Its hypothesis is
orthogonality of the prescribed local datum against the classes which are *relaxed at the level `Λ`*
(`Work.SSGRoute.IsRelaxedDual K Λ T`: unramified outside the level-`K` classes of `T`, and locally
trivial outside them at the places split in `Λ`), and this is exactly the conclusion of the proved
p. 18 chase `Work.SSGRoute.auxDatum_orthogonal_of_productFormula`.  Its conclusion prescribes the
local data at the places of `T'` and requires the realised class `z` to be unramified at the finite
places outside the level-`K` classes of `T'` that are *not split in `M`*.

The two levels `Λ` and `M` are *different* in the use made by the section-4 assembly: the assembly
`Work.SSGRoute.auxExists_of_pairing_and_realisation` applies the gate at `M = N`, the level of the
*other* summand of the induction (`Work.SSGRoute.z_data_of_spanning_of_aux`, applied at `N = N₀ ⊔ Λ`),
while the orthogonality hypothesis is supplied by the chase at the level `Λ` (the chase closes only
there: at a larger level the extra places at which the datum ramifies are no longer split).  So the
statement used is the **mixed** one -- dual relaxation at `Λ`, primal unramifiedness at `N` -- and
this file isolates exactly what the mixed statement needs.

## REFUTATION OF `RelaxedDualsAgree` (recorded 2026-09-29, two independent reviewers)

`Work.SSGRoute.RelaxedDualsAgree K Λ M` is **FALSE** as stated (even with `Λ ≤ M`, and even with the
agreement required only at the places of `T`).  Both reviewers gave the same counterexample:

`p = 2`, `k = K = Λ = ℚ`, `Ω = ℚ̄`, `M = ℚ(i)`, `T = {A₀}` a place over `2`, and `b` the quadratic
character of `ℚ(i)/ℚ` (a continuous homomorphism `G_ℚ → ℤ/2`, trivial on `G_{ℚ(i)}`).  Then `b` is
cocycle + locally constant, unramified outside the places over `2`, and vanishes on `D_B` for every
`M`-split place `B`, so `b` is `M`-relaxed; but a `Λ = ℚ`-relaxed `b'` has to vanish on `D_B` for
*every* finite place `B` outside the class of `T` (all places are `ℚ`-split), and those decomposition
groups generate `G_ℚ` (Chebotarev), so `b' = 0`, whereas the agreement clause at `T` would require
`b'|D_{A₀} = b|D_{A₀} ≠ 0` (`2` is ramified in `ℚ(i)/ℚ`).

**What this does and does not refute.**  The *implication* proved below
(`AuxRealisationNoInv K M M` + `RelaxedDualsAgree K Λ M → AuxRealisationNoInv K Λ M`) is true, but its
second hypothesis is false, so it is not applicable, and in particular the mixed gate is *not*
obtained from the unmixed one by a comparison of local components.  The counterexample does **not** by
itself refute the mixed gate: the local Tate pairing on the local data space is *degenerate* (its left
radical is the vanishing submodule `ZDataMup.localVanish`, see
`Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`), so the relevant condition is the
*double annihilator* `W_M ⊆ W_Λ^{⊥⊥}` -- equivalently *every `M`-relaxed dual class is orthogonal,
over the places of `T'`, to every class which is a `Λ`-primal class* -- and the counterexample's `b`
does satisfy that (its pairing with the `ℚ`-primal classes vanishes by the product formula, the only
contributing place being the one over `2`, which lies in `T`).  So the corrected obligation is this
**reciprocity statement**, not the local-component agreement; it is the statement that the relaxation
step of the level-`K` Poitou--Tate sequence has to supply, and it is what a future session should
attack (or refute, with a pairing computation in the local data space).

## The two ingredients of the mixed statement

* **(PT at the level `M`)** the *unmixed* statement `AuxRealisationNoInv K M M`: the same conclusion,
  with the orthogonality hypothesis against the classes relaxed at the level `M`.  This is the
  standard level-`K` degree-one Poitou--Tate realisation (primal and dual local conditions at the
  same level); it is what the level-`K` **counting identity** supplies
  (`Submission/Work/SSGRoute/PT/pt_counting_identity_h1.lean` is *below* this node; the `ZSplit`
  interface `Work.SSGRoute.ZSplit.kRealizable_of_orthogonal_of_counting` is its
  `kRealizable`/`kDualSelmer` form, and that module is *above* the node because
  `ZSplit/levelKCounting.lean` imports `shafarevich_theorem13`; the verbatim relocation of its
  vocabulary to a below-node module is `ZConstruction/LevelKVocab.lean`).

* **(`RelaxedDualsAgree K Λ M`)** the *relaxation slack*: every class satisfying the `M`-relaxed dual
  conditions agrees, **at the places of the base set `T`**, with a class satisfying the `Λ`-relaxed
  conditions (definition below).  The restriction to the places of `T` is exactly what the gate
  needs: the prescribed datum *vanishes* at the places of `T' ∖ T` (hypothesis `hfzero` of the gate),
  so only the local components at `T` enter the reciprocity sum.  Both families consist of classes
  unramified outside the level-`K` classes of `T`; they differ exactly by the condition "locally
  trivial" (for `Λ`) respectively "unramified" (for `M`) at the finite places outside the classes of
  `T` that are split in `Λ` but not in `M` (for `Λ ≤ M` these are exactly the places that are split
  in `Λ` and not in `M`).

## What is proved here

* `Work.SSGRoute.auxRealisationExt_of_selfLevel` and `Work.SSGRoute.auxRealisationNoInv_of_selfLevel`:
  `AuxRealisationNoInv K M M` (resp. `AuxRealisationExt K M M`) together with
  `RelaxedDualsAgree K Λ M` implies the mixed gate `AuxRealisationNoInv K Λ M`
  (resp. `AuxRealisationExt K Λ M`).  The proof replaces the `M`-relaxed dual by the `Λ`-relaxed one
  with the same local components at `T`, and uses
  `Work.SSGRoute.ZDataMup.pair_congr_of_eqOn_right` for the termwise equality of the reciprocity sum
  (the terms at `T' ∖ T` drop out because the datum vanishes there).
* `Work.SSGRoute.auxExists_of_pairing_and_realisation_self(_odd)`: `AuxExists K Λ S` from the pairing
  gate, the *unmixed* realisation gate at every level `N ≥ Λ`, and the relaxation slack at every
  `N ≥ Λ`.

**Consequence for the node.**  The obligation of the auxiliary class is exactly
`{AuxPairingGate, ∀M AuxRealisationNoInv K M M, ∀N ≥ Λ RelaxedDualsAgree K Λ N}`: the first two are
the standard shared arithmetic (Hilbert reciprocity; the level-`K` Poitou--Tate realisation), and the
third is isolated here for the first time.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The relaxation slack between two levels `Λ` and `M`.**  Every class satisfying the `M`-relaxed
dual conditions (`Work.SSGRoute.IsRelaxedDual K M T`) agrees, on the level-`K` local group of every
place of **`T`**, with a class satisfying the `Λ`-relaxed conditions
(`Work.SSGRoute.IsRelaxedDual K Λ T`).

The restriction to the base set `T` (and not to the enlarged set `T'`) is precisely the form the
realisation gate consumes: the prescribed datum vanishes on `T' ∖ T`, so the terms of the reciprocity
sum at those places are zero. -/
def RelaxedDualsAgree (K Λ M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (T T' : Finset (ValuationSubring Ω)), (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
    ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K M T b →
    ∃ b' : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K Λ T b' ∧
      ∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b' σ = b σ

/-- **The mixed-level gate without the involution clause, from the unmixed gate and the relaxation
slack.** -/
theorem auxRealisationNoInv_of_selfLevel {K Λ M : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hM : AuxRealisationNoInv (p := p) K M M)
    (hdual : RelaxedDualsAgree (p := p) K Λ M) :
    AuxRealisationNoInv (p := p) K Λ M := by
  intro pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  classical
  have hsum : ∀ c : (Ω ≃ₐ[k] Ω) → ZMod p,
      IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup c → IsLocConstOn K.fixingSubgroup c →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) c
        = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) c := by
    intro c hc1 hc2
    refine (Finset.sum_subset hT'T fun A hA hAnT => ?_).symm
    rw [hfzero A (Finset.mem_sdiff.mpr ⟨hA, hAnT⟩)]
    exact pair_zero_left (p := p) hpair (hT'fin A hA)
      ⟨ZDataMup.isCocycleOn_of_le inf_le_right hc1,
        ZDataMup.isLocConstOn_of_le inf_le_right hc2⟩
  have horthM : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K M T b →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
    intro b hb
    obtain ⟨b', hb', hagree⟩ := hdual T T' hT'fin b hb
    have hEq : ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
        = ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b' := by
      rw [hsum b hb.1 hb.2.1, hsum b' hb'.1 hb'.2.1]
      refine Finset.sum_congr rfl fun A hA => ?_
      exact ZDataMup.pair_congr_of_eqOn_right (K := K) hpair
        ⟨A, hT'fin A (hT'T A hA), rfl⟩ ⟨hfcoc A (hT'T A hA), hfloc A (hT'T A hA)⟩
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb'.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb'.2.1⟩
        (fun σ hσ => (hagree A hA σ hσ).symm)
    rw [hEq]
    exact horth b' hb'
  exact hM pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horthM

/-- **The mixed-level gate with the involution clause, from the unmixed gate and the relaxation
slack.** -/
theorem auxRealisationExt_of_selfLevel {K Λ M : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hM : AuxRealisationExt (p := p) K M M)
    (hdual : RelaxedDualsAgree (p := p) K Λ M) :
    AuxRealisationExt (p := p) K Λ M := by
  intro pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  classical
  have hsum : ∀ c : (Ω ≃ₐ[k] Ω) → ZMod p,
      IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup c → IsLocConstOn K.fixingSubgroup c →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) c
        = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) c := by
    intro c hc1 hc2
    refine (Finset.sum_subset hT'T fun A hA hAnT => ?_).symm
    rw [hfzero A (Finset.mem_sdiff.mpr ⟨hA, hAnT⟩)]
    exact pair_zero_left (p := p) hpair (hT'fin A hA)
      ⟨ZDataMup.isCocycleOn_of_le inf_le_right hc1,
        ZDataMup.isLocConstOn_of_le inf_le_right hc2⟩
  have horthM : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K M T b →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
    intro b hb
    obtain ⟨b', hb', hagree⟩ := hdual T T' hT'fin b hb
    have hEq : ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
        = ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b' := by
      rw [hsum b hb.1 hb.2.1, hsum b' hb'.1 hb'.2.1]
      refine Finset.sum_congr rfl fun A hA => ?_
      exact ZDataMup.pair_congr_of_eqOn_right (K := K) hpair
        ⟨A, hT'fin A (hT'T A hA), rfl⟩ ⟨hfcoc A (hT'T A hA), hfloc A (hT'T A hA)⟩
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb'.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb'.2.1⟩
        (fun σ hσ => (hagree A hA σ hσ).symm)
    rw [hEq]
    exact horth b' hb'
  exact hM pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horthM

/-- **`AuxExists` from the pairing gate and the two unmixed ingredients.**  This is
`Work.SSGRoute.auxExists_of_pairing_and_realisation` with its hypothesis
`∀ M, AuxRealisationExt K Λ M` replaced by the *unmixed* realisation gate at every level `N ≥ Λ`
together with the relaxation slack at every `N ≥ Λ`; the mixed gate at the level `N` that the
assembly actually uses is produced by `Work.SSGRoute.auxRealisationExt_of_selfLevel`. -/
theorem auxExists_of_pairing_and_realisation_self {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hP : AuxPairingGate (p := p) K)
    (hRN : ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
      AuxRealisationExt (p := p) K N N)
    (hdualN : ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
      RelaxedDualsAgree (p := p) K Λ N)
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    AuxExists (p := p) K Λ S := by
  classical
  refine auxExists_of_weakened (p := p) ?_
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub _hS'ram L _instLadd _instLmod _instLfin hL y₁ hy₁
  -- (1) the local Tate system
  obtain ⟨pair, hpair, hprod, hunr⟩ := hP
  -- (2) the base place set: representatives of the level-`K` classes of `cs(S)`
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ := ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S hSfin
  -- (3) the enlarged place set: representatives of the level-`K` classes of `cs(S')`
  obtain ⟨T'', hT''fin, hT''disj, hT''conj, hT''cov⟩ := ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S' hS'fin
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
  -- (5) the datum vanishes on `T' ∖ T` away from `cs(S)`, hence its prescribed value is `0` there
  have hT'zero : ∀ A ∈ T' \ T, ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
    intro A hA hconj
    obtain ⟨hAT', hAnT⟩ := Finset.mem_sdiff.mp hA
    obtain ⟨t, ht, hc⟩ := hTcov A hconj
    have hEq : A = t := hT'disj A hAT' t (hT'T t ht) (ZConstruction.kConj_symm hc)
    exact hAnT (hEq ▸ ht)
  -- (6) the one-dimensional module `L` is `ZMod p`
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
  -- (7) the datum transported to `ZMod p`
  set ν : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => e.symm (y₁ σ) with hν
  have hνhyp : ZHyp (p := p) K Λ S ν :=
    ZHyp.mapAdd (f := (e.symm : L →ₗ[ZMod p] ZMod p).toAddMonoidHom) hy₁
  -- (8) the prescribed data at `T'`
  set f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
    fun A => auxDatum (p := p) K S ν A with hf
  have hfT : ∀ A ∈ T, f A = ν := by
    intro A hA
    simp only [hf, auxDatum]
    rw [if_pos (hTconj A hA)]
  have hfzero : ∀ A ∈ T' \ T, f A = 0 := by
    intro A hA
    have hnot := hT'zero A hA
    simp only [hf, auxDatum]
    rw [if_neg hnot]
  have hfcoc : ∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
    intro A hA
    by_cases hAT : A ∈ T
    · rw [hfT A hAT]
      exact isCocycleOn_of_addOn inf_le_right
        (fun g hg h hh =>
          hνhyp.add g (Subgroup.mem_inf.mp hg).2 h (Subgroup.mem_inf.mp hh).2)
    · have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAT⟩
      rw [hfzero A hmem]
      exact fun g hg h hh => by simp
  have hfloc : ∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
    intro A hA
    by_cases hAT : A ∈ T
    · rw [hfT A hAT]
      exact ZDataMup.isLocConstOn_of_le inf_le_right hνhyp.locconst
    · have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAT⟩
      rw [hfzero A hmem]
      exact ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
  -- (9) the orthogonality: the extra places carry the zero datum, the places of `T` carry `ν`
  have horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K Λ T b →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
    intro b hb
    have hunion : T ∪ (T' \ T) = T' := Finset.union_sdiff_of_subset (fun a ha => hT'T a ha)
    have hdisj : Disjoint T (T' \ T) := Finset.disjoint_sdiff
    have hsplit : ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
        = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
          + ∑ A ∈ T' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b := by
      conv_lhs => rw [← hunion]
      rw [Finset.sum_union hdisj]
    rw [hsplit]
    have hzero : ∑ A ∈ T' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
      refine Finset.sum_eq_zero fun A hA => ?_
      rw [hfzero A hA]
      exact pair_zero_left (p := p) hpair (hT'fin A (Finset.mem_sdiff.mp hA).1)
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
    rw [hzero, add_zero]
    exact auxDatum_orthogonal_of_productFormula (p := p) hpair hprod hunr
      hTfin hTdisj hTconj (fun B _ hconj => hTcov B hconj) hνhyp hb
  -- (10) the realisation
  obtain ⟨z, hzcoc, hzloc, hzagree, hzinf, hzunr⟩ :=
    auxRealisationExt_of_selfLevel (p := p) (hRN N hΛN) (hdualN N hΛN) pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  have hzadd := addOn_of_isCocycleOn hzcoc
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
      have hρ' : ρ ∈ SSGRoute.decomp k t ⊓ K.fixingSubgroup := hρ
      show e (z ρ) = y₁ ρ
      rw [hzagree t (hT'T t ht) ρ hρ', hfT t ht]
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
    have hloc : ∀ ρ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, yAux ρ = (0 : (Ω ≃ₐ[k] Ω) → L) ρ := by
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

/-- **The same for odd `p`**, with the realisation gate stated *without* the involution clause (the
form in which the odd-`p` lane proves it): the involution clause is free for odd `p`
(`Work.SSGRoute.auxRealisationExt_of_noInv`). -/
theorem auxExists_of_pairing_and_realisation_self_odd {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (hp2 : p ≠ 2)
    (hP : AuxPairingGate (p := p) K)
    (hRN : ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
      AuxRealisationNoInv (p := p) K N N)
    (hdualN : ∀ (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], Λ ≤ N →
      RelaxedDualsAgree (p := p) K Λ N)
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    AuxExists (p := p) K Λ S :=
  auxExists_of_pairing_and_realisation_self (p := p) hP
    (fun N _ _ hΛN => auxRealisationExt_of_noInv (p := p) hζ hζK hp2 (hRN N hΛN)) hdualN hSfin

end Work.SSGRoute
