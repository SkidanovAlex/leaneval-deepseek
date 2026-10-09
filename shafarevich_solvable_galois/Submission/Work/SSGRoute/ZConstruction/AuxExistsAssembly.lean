import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxZHypOfGates
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.ZDataAux
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps_extends
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `AuxExists` from the three gates, assembled

This file closes the *wiring* of the auxiliary-class obligation of Schmidt--Wingberg section 4:

    Work.SSGRoute.AuxExists K Λ S
      <= Work.SSGRoute.AuxPairingGate K                      (gate P: the local Tate system)
       + AuxDatumOrthogonalityGate K Λ                       (gate O: the p. 18 orthogonality)
       + AuxDatumCounting K Λ                                (gate C: the level-K counting)

(the assembly `Work.SSGRoute.ZConstruction.auxExists_of_countingBlocks`), with the two side
hypotheses that the instantiation of the node supplies (`hcoverage`: `S` covers the places above `p`
and the places ramified in `Λ`, i.e. the `hSram` field of `Work.SSGRoute.ZAmbient`; and
`hp : p ≠ 2` plus a primitive `p`-th root of unity `ζ ∈ K`, which discharge the involution clause of
the realisation).

The route is the one recommended by the retraction of the *false* mixed gate
(`ZConstruction/NOTE_session17.lean`): the realisation is the *unmixed* level-`K` one
(`Work.SSGRoute.ZConstruction.auxDatum_realisation_of_counting_vanishing`), fed by the two counting
blocks through `Work.SSGRoute.ZConstruction.exists_zHyp_of_countingBlocks`.  The only thing that is
proved *here* is the transfer of the realised class from the level-`K` representative set `Te` of
`cs(S')` to the caller's place set `S'` (the two present the same `G_k`-conjugacy classes, and every
clause of `ZHyp` sees only `∃ A ∈ ·, IsConjPlace k A B`), and the linear transport of the datum and
of the answer along the isomorphism `ZMod p ≃ₗ L`.

## What each gate owes (updated state)

* **(P)** `Work.SSGRoute.AuxPairingGate K` -- supplier on disk for odd `p`:
  `ZConstruction/levelK_pairing_productFormula.lean`.
* **(O)** `AuxDatumOrthogonalityGate K Λ`: the prescribed datum `auxDatum K S ν` is orthogonal to the
  *honest* dual family at `Te` (`ZDataMup.IsOrthogonalToDual`), for every local Tate system with the
  product formula.  The *proved* chase (`Work.SSGRoute.auxDatum_orthogonal_of_productFormula` and its
  enlargement `Work.SSGRoute.auxDatum_orthogonal_enlarged`) gives orthogonality only against the
  **relaxed** family `Work.SSGRoute.IsRelaxedDual K Λ T` (unramified outside the level-`K` classes of
  the *base* set `T`, and locally trivial at the `Λ`-split places outside them).  The honest family
  at `Te` is *larger* (its unramifiedness is required only outside `cs(Te)`, and it has no local
  triviality clause), so **(O) is not yet supplied by the chase**: bridging the two is the open
  mathematical point of this gate.  Schmidt--Wingberg's own argument for it (p. 18--19) decomposes
  the dual class along the two subfields `Λ` and `K~` (the field cut out by the induction step):
  the `K~`-component dies by the *unramified orthogonality* of (P) (the extension `K~|K` is
  unramified at the places where the datum is prescribed, and the datum is unramified there), and the
  `Λ`-component is the image of the *global* datum under the level-`Λ` Poitou--Tate middle map, hence
  vanishes by the exactness of that sequence.  See `ZConstruction/NOTE_seam_counting.lean`.
* **(C)** `AuxDatumCounting K Λ` -- the level-`K` counting inequality at `Te`, with the coverage
  hypothesis (places above `p` and places ramified in `N`) that makes it *true*
  (`ZDataMup/TATEPOITOU_STATUS.md`, "SESSION 4"; without that hypothesis the inequality fails, e.g.
  for `(k, K, p, Te) = (Q, Q, 3, {place over 2})`).

`declare_proven` on the node therefore still waits on (P), (O), (C) and the `p = 2` sibling of the
involution clause (for `p = 2` the argument `eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot` is
vacuous, and the involutions are the archimedean condition of the correction).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-! ## The trivial `Gal(K|k)`-action on `ZMod p`, as an instance

The `ZMod p`-valued gates of this lane (`Work.SSGRoute.ZDataMup.IsOrthogonalToDual`,
`ZDataMup.localDataSpace`, `ZDataMup.CountingInequality`, ...) are stated with a
`[DistribMulAction (K ≃ₐ[k] K) (ZMod p)]` argument.  In the intended instantiation the cochain is a
`1`-cocycle with values in `μ_p ⊆ K`, on which `Gal(K|k)` acts trivially (the action is the
cyclotomic character, and `μ_p ⊆ K` makes it the restriction of `Gal(Ω/k)` to `Gal(K|k)` acting on
`μ_p ⊆ K` -- the trivial action is the one under which the workspace's `IsCocycleOn` reduces to
additivity, cf. `Work.SSGRoute.ZConstruction.addOn_of_isCocycleOn`).  Declaring it as an instance
here keeps the statements of downstream lemmas free of the bookkeeping; it is visible only to
importers of this module. -/
instance instDistribMulActionZModTrivial (p : ℕ) (K : IntermediateField k Ω) :
    DistribMulAction (K ≃ₐ[k] K) (ZMod p) where
  smul := fun _ x => x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

/-- Compatibility of the trivial `Gal(K|k)`-action with the `ZMod p`-module structure. -/
instance instSMulCommClassZModTrivial (p : ℕ) (K : IntermediateField k Ω) :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) where
  smul_comm := fun _ _ _ => rfl

/-- **Two place sets presenting the same `G_k`-conjugacy classes.**  If every place of `Te` is
conjugate to a place of `Se` and every place of `Se` has a level-`K` conjugate in `Te`, then "being
conjugate to a place of `Te`" and "being conjugate to a place of `Se`" agree. -/
theorem exists_isConjPlace_congr {K : IntermediateField k Ω}
    {Se Te : Finset (ValuationSubring Ω)}
    (hsub : ∀ A ∈ Te, ∃ A' ∈ Se, SSGRoute.IsConjPlace k A' A)
    (hcov : ∀ B : ValuationSubring Ω, (∃ A ∈ Se, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ Te, Work.SSGRoute.KConj K A' B)
    (B : ValuationSubring Ω) :
    (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) ↔ (∃ A ∈ Se, SSGRoute.IsConjPlace k A B) := by
  constructor
  · rintro ⟨A, hA, hc⟩
    obtain ⟨A', hA', hc'⟩ := hsub A hA
    exact ⟨A', hA', SSGRoute.isConjPlace_trans hc' hc⟩
  · rintro ⟨A, hA, hc⟩
    obtain ⟨A', hA', hc'⟩ := hcov B ⟨A, hA, hc⟩
    exact ⟨A', hA', ZConstruction.kConj_isConjPlace hc'⟩

/-- **`ZHyp` is a function of the `G_k`-conjugacy classes of the place set.**  Every clause of
`Work.SSGRoute.ZHyp` constrains the cochain either not at all or through the predicates
`∃ A ∈ S, IsConjPlace k A B` (`hyT`, `hy0`) and its negation (`hyS`), so replacing `Te` by a place
set `Se` with the same `G_k`-conjugacy classes changes nothing. -/
theorem zHyp_of_cs_congr {K Λ : IntermediateField k Ω} {Se Te : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] {ν : (Ω ≃ₐ[k] Ω) → E}
    (hiff : ∀ B : ValuationSubring Ω,
      (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) ↔ (∃ A ∈ Se, SSGRoute.IsConjPlace k A B))
    (h : ZHyp (p := p) K Λ Te ν) : ZHyp (p := p) K Λ Se ν where
  add := h.add
  locconst := h.locconst
  hyS B hB hnot hsp σ hσ hσI :=
    h.hyS B hB (fun A hA hc => by
      obtain ⟨A', hA', hc'⟩ := (hiff B).mp ⟨A, hA, hc⟩
      exact hnot A' hA' hc') hsp σ hσ hσI
  hyT B hB hconj σ hσ hσI := h.hyT B hB ((hiff B).mpr hconj) σ hσ hσI
  hy0 B hB hconj hbad σ hσ hσd := h.hy0 B hB ((hiff B).mpr hconj) hbad σ hσ hσd
  hyinf := h.hyinf

/-- **`AuxExists` from the three gates.**  See the module docstring for the status of each gate and
for the two side hypotheses. -/
theorem auxExists_of_countingBlocks {K Λ : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [FiniteDimensional k Λ] [IsGalois k Λ]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hp : p ≠ 2) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hcoverage : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (hP : AuxPairingGate (p := p) K)
    (hgate : AuxDatumOrthogonalityGate (p := p) (K := K) (Λ := Λ))
    (hcount : AuxDatumCounting (p := p) (K := K) (Λ := Λ)) :
    AuxExists (p := p) K Λ S := by
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub hS'ram L _instLadd _instLmod _instLfin
    hL y₁ hy₁
  classical
  -- (1) the local Tate system of the pairing gate
  obtain ⟨pair, hpair, hprod, _hunr⟩ := hP
  -- (2) the base place set: level-`K` representatives of the classes of `cs(S)`
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ := ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S hSfin
  -- (3) the enlarged place set: representatives of the classes of `cs(S')`, containing `T`
  obtain ⟨Te, hTeT, hTefin, hTedisj, hTesub, hTecov⟩ :=
    ZConstruction.exists_KConj_reps_extends (k := k) (Ω := Ω) K hS'fin hS'sub hTfin hTdisj hTconj hTcov
  -- (4) the line module `L` is one-dimensional over `ZMod p`; fix an isomorphism
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
  -- (5) the datum transported to the prime field
  set ν : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => e.symm (y₁ σ) with hν
  have hνhyp : ZHyp (p := p) K Λ S ν :=
    ZHyp.mapAdd (f := (e.symm : L →ₗ[ZMod p] ZMod p).toAddMonoidHom) hy₁
  -- (6) the coverage of the counting place set: `Te` contains the classes of the places above `p`
  -- (via `hcoverage`, `S`'s coverage, and `hS'sub`) and those of the places ramified in `N`
  -- (via `hS'ram` and the cover property of `Te`)
  have hcover : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ Te, SSGRoute.IsConjPlace k A B := by
    intro B hB hbad
    rcases hbad with hram | hpB
    · obtain ⟨A, hA, hc⟩ := hS'ram B hB hram
      obtain ⟨A', hA', hc'⟩ := hTecov B ⟨A, hA, hc⟩
      exact ⟨A', hA', ZConstruction.kConj_isConjPlace hc'⟩
    · obtain ⟨A, hA, hc⟩ := hcoverage B hB (Or.inr hpB)
      obtain ⟨A', hA', hc'⟩ := hS'sub B ⟨A, hA, hc⟩
      obtain ⟨A'', hA'', hc''⟩ := hTecov B ⟨A', hA', hc'⟩
      exact ⟨A'', hA'', ZConstruction.kConj_isConjPlace hc''⟩
  -- (6b) `Te` is closed under the passage to a level-`K` conjugate, i.e. it meets every class of
  -- `cs(Te)` in a level-`K` representative
  have hTecov' : ∀ B : ValuationSubring Ω, (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ Te, Work.SSGRoute.KConj K A' B := by
    intro B hconj
    obtain ⟨A, hA, hc⟩ := hconj
    obtain ⟨A', hA', hc'⟩ := hTesub A hA
    exact hTecov B ⟨A', hA', SSGRoute.isConjPlace_trans hc' hc⟩
  -- (7) the realisation of the transported datum at the enlarged place set
  obtain ⟨yAux₀, hyAux₀, hag, hvan⟩ :=
    exists_zHyp_of_countingBlocks (p := p) hp hΛN pair hpair hprod hSfin hTfin hTdisj hTconj
      hTcov hTeT hTefin hTedisj hTecov' hcover hνhyp hζ hζK
      (hgate pair hpair hprod) hcount
  refine ⟨fun σ => e (yAux₀ σ), ?_, ?_, ?_⟩
  · -- the `ZHyp` clauses at the caller's place set `S'`
    have h2 : ZHyp (p := p) K N Te (fun σ => e (yAux₀ σ)) :=
      ZHyp.mapAdd (f := (e : ZMod p →ₗ[ZMod p] L).toAddMonoidHom) hyAux₀
    have hiff : ∀ B : ValuationSubring Ω,
        (∃ A ∈ Te, SSGRoute.IsConjPlace k A B) ↔ (∃ A ∈ S', SSGRoute.IsConjPlace k A B) :=
      fun B => exists_isConjPlace_congr (K := K) hTesub hTecov B
    exact zHyp_of_cs_congr (p := p) (K := K) (Λ := N) (Se := S') (Te := Te)
      (ν := fun σ => e (yAux₀ σ)) (hiff := hiff) (h := h2)
  · -- agreement with the datum at `cs(S)`
    intro B hB hconj σ hσ
    show e (yAux₀ σ) = y₁ σ
    rw [hag B hB hconj σ hσ]
    exact e.apply_symm_apply (y₁ σ)
  · -- vanishing at `cs(S') ∖ cs(S)`
    intro B hB hnot hconj σ hσ
    have hconjTe : ∃ A ∈ Te, SSGRoute.IsConjPlace k A B :=
      (exists_isConjPlace_congr (K := K) hTesub hTecov B).mpr hconj
    show e (yAux₀ σ) = 0
    rw [hvan B hB hnot hconjTe σ hσ, map_zero]

end Work.SSGRoute.ZConstruction
