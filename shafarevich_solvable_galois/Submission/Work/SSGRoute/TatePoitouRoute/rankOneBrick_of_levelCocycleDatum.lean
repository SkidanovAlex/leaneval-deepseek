import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.PTdualControl.C6_of_rankOneBrick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one core of node `C6`, assembled from the level-cocycle datum

This file supplies the **last step** of the proof of
`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` (the single remaining `sorry` of the
whole `C6`/`E9` chain, and one of the two remaining `sorry`s on the frontier of
`Work.SSGRoute.tatePoitou_sha2_image`): the assembly of the detector from the *level-cocycle datum*.

The chain, with every input already proved on disk:

* `Work.SSGRoute.Sha2Lib.rankOne_functionalDetection_of_levelCocycleDatum` — the datum for every
  nonzero `D_w`-equivariant `μ` on the coinduced permutation module yields `DetectsAt` at the class
  `δμ = (mk₀ μ) ≻ extClass (ratDivSES)`;
* `Work.E7cOmega.functional_of_ext_nonzero` — every nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` *is* such a
  `δμ` (Tate duality: `ℚ` is divisible, so `Ext¹(·, ℚ) = 0` and the long exact sequence of
  `0 → ℤ → ℚ → ℚ/ℤ → 0` exhibits `φ` as a connecting image);
* `Work.SSGRoute.Sha2Lib.isUnramifiedDetector_ind_of_coind` — the induced and coinduced models of
  the permutation module are isomorphic (`Rep.indCoindIso`) and the detector is invariant under a
  coefficient isomorphism.

So the whole remaining arithmetic content of the leaf is exactly: *produce the level-cocycle datum
for every nonzero `μ`*.  Nothing about `Ext`, `ℚ/ℤ`, the level criterion or the coefficient model is
left.
-/

namespace Work.SSGRoute.TatePoitouRoute

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1

noncomputable section

set_option linter.style.haveILetI false

/-- **The rank-one core of node `C6` from the level-cocycle datum.**

For `N ⊴ Gal(K/k)` containing the inertia at `q ∤ p` and fixing a primitive `p`-th root of unity
`ζ ∈ K`: if for every nonzero `D_w`-equivariant functional `μ` on the **coinduced** permutation
module `M = coInd_N^Γ 𝔽_p` there is a level-cocycle datum
`LevelCocycleDatum p k K Ω w q hwq M μ`, then the unramified detector holds for the **induced**
permutation module `Ind_N^Γ 𝔽_p` — i.e. for the leaf
`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` of the challenge's `C6` chain. -/
theorem unramifiedDetector_rankOne_of_levelCocycleDatum (p : ℕ) [Fact p.Prime]
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hdatum : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 →
      Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  classical
  haveI := Work.Sha2Lib.coindPerm_finite (p := p) (k := k) (K := K) N
  -- it suffices to prove the detector for the coinduced model (Step 0 of the leaf)
  refine Work.Sha2Lib.rankOne_isUnramifiedDetector_of_coind p k K Ω w q hwq N
    (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)) ?_
  -- and there it is exactly the `μ`-form produced by the datum
  intro φ hφ
  obtain ⟨μ, hμne, hμeq⟩ :=
    Work.E7cOmega.functional_of_ext_nonzero p k K
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
      (Work.Sha2Lib.coindPerm_psmul (p := p) (k := k) (K := K) N) w φ hφ
  rw [hμeq]
  exact Work.Sha2Lib.rankOne_functionalDetection_of_levelCocycleDatum p k K Ω w q hwq N hdatum
    μ hμne

end

end Work.SSGRoute.TatePoitouRoute
