import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.Sha2Lib.rankOneBrickWork
import Submission.Work.Sha2Lib.rankOneLevelCocycleRoute
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.E7cOmega.functional_of_ext_nonzero
import Submission.Work.SSGRoute.C6Detector.detector_algClosedExt
import Submission.Work.Sha2Lib.levelCocycleDatum_of_constant
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one core of node `C6`

This file closes `Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` by the chain that the
`TPatom`/`C6Detector` lanes have assembled:

* `Work.Sha2Lib.rankOne_isUnramifiedDetector_of_coind` — the induced module of the statement is
  reduced to the *coinduced* model `coInd_N^Γ 𝔽_p` (a coefficient isomorphism, `Rep.indCoindIso`);
* `Work.SSGRoute.C6Detector.detector_algClosedExt` — the detector is independent of the ambient
  algebraically closed field, so it suffices to prove it in `AlgebraicClosure K`, where
  `IsAlgClosure k ·` is available by instance;
* `Work.E7cOmega.functional_of_ext_nonzero` — every nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` is a
  connecting class `δ μ` of a nonzero `D_w`-equivariant functional
  `μ : res_{D_w} M ⟶ ℚ/ℤ`;
* `Work.SSGRoute.PTdualControl.detectsAt_of_levelCocycleDatum` — the level-cocycle datum for `μ`
  produces `DetectsAt` at `δ μ`;
* the datum itself splits into the *invariant* case `μ (const 1) ≠ 0`, proved unconditionally in
  `Work.Sha2Lib.levelCocycleDatum_of_constant` (the constant cocycle of
  `exists_unramified_character_with_p_dvd_residueDeg`), and the *non-invariant* case
  `μ (const 1) = 0`, which is `Work.SSGRoute.TPatom.noninvariantLevelDatum` (the concentrated
  Kummer/Grünwald–Wang level datum of the `TPatom` lane).
-/

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- **The datum of the rank-one brick in the canonical ambient field.**  For every nonzero
`D_w`-equivariant functional `μ` on the coinduced permutation module `coInd_N^Γ 𝔽_p`, the
level-cocycle datum holds in `AlgebraicClosure K`: the invariant case is
`Work.Sha2Lib.levelCocycleDatum_of_constant`, the non-invariant case is
`Work.SSGRoute.TPatom.noninvariantLevelDatum`. -/
theorem rankOneLevelCocycleDatum_algClosure (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K (AlgebraicClosure K) w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  by_cases hconst : μ.hom (⟨fun _ : K ≃ₐ[k] K => (1 : ZMod p), by intro n g; rfl⟩ :
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V) ≠ 0
  · exact Work.Sha2Lib.levelCocycleDatum_of_constant p k K w q hwq hpq N hNI ζ hζ hNζ μ hμ hconst
  · push_neg at hconst
    exact Work.SSGRoute.TPatom.noninvariantLevelDatum p k K (AlgebraicClosure K) w q hwq hpq
      N hNI ζ hζ hNζ μ hμ hconst

/-- **The rank-one core of node `C6`** (steps (1)–(4) of `_lead_design/ssg_pt_design_1002/DESIGN.md`
§2 A1, statement `unramifiedDetector_indNormal.stmt` at `W = 𝔽_p`).

`N ⊴ Gal(K/k)` contains every inertia element at the finite place `q ∤ p` and fixes a primitive
`p`-th root of unity `ζ ∈ K`; so `K₁ := K^N` contains `μ_p` and `K₁/k` is unramified at `q`.  With
`W = 𝔽_p` (trivial `N`-action) the induced module `Ind_N^{Gal(K/k)} W` is the permutation module
`𝔽_p[Γ/N]`; the claim is that every nonzero `φ ∈ Ext¹_{D_w}(res (Ind W), ℤ)` is detected
(`Sha2Lib.DetectsAt`) at some level, with `p ∤ e(q'|q)` and an unramified global class. -/
theorem unramifiedDetector_indNormal_rankOne (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  -- Step 0: it suffices to prove the detector for the *coinduced* model.
  refine Work.Sha2Lib.rankOne_isUnramifiedDetector_of_coind p k K Ω w q hwq N
    (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)) ?_
  -- Step 1: the detector is independent of the ambient algebraically closed field, so it suffices
  -- to prove it in `AlgebraicClosure K`.
  refine Work.SSGRoute.C6Detector.detector_algClosedExt p k K (AlgebraicClosure K) Ω
    ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] Ω).restrictScalars k) ?_ ?_ w q hwq
    (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ?_
  · intro _ _ h
    exact RingHom.injective
      ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] Ω) : AlgebraicClosure K →+* Ω) h
  · intro x
    exact (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] Ω).commutes x
  -- Step 2: in `AlgebraicClosure K`, reduce every nonzero class to a connecting class `δ μ`.
  intro φ hφ
  haveI : Finite (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) :=
    Work.Sha2Lib.rankOne_coind_finite p k K N
  obtain ⟨μ, hμne, hφμ⟩ := Work.E7cOmega.functional_of_ext_nonzero p k K
    (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
    (Work.Sha2Lib.rankOne_coind_pTorsion p k K N) w φ hφ
  rw [hφμ]
  -- Step 3: the level-cocycle datum for `μ` gives `DetectsAt` at `δ μ`.
  exact Work.SSGRoute.PTdualControl.detectsAt_of_levelCocycleDatum p k K (AlgebraicClosure K)
    w q hwq (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
    (Work.Sha2Lib.rankOne_coind_pTorsion p k K N) μ
    (rankOneLevelCocycleDatum_algClosure p k K w q hwq hpq N hNI ζ hζ hNζ μ hμne)

end

end Work.SSGRoute.Sha2Lib
