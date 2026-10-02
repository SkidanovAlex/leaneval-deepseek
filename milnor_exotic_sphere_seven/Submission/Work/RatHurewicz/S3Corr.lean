import Mathlib
import Submission.Work.RatHurewicz.truncationHomologyTransfer_of_serre
import Submission.Work.Serre.StableExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology transfer of the truncation step, with the corrected Serre-exactness hypothesis

Area **RATHUREWICZ**.  `truncationHomologyTransfer_of_serre` (`S3Corr` namespace) is the reduction of
the chapter's single remaining input `Work.RatHurewicz.TruncationHomologyTransfer` to the two
statements of the neighbouring chapter:

* `Work.Serre.SerreExactRangeCorrected` — Serre's exact sequence in the stable range in its corrected
  form (with the hypothesis `1 ≤ b`; the form `Work.StemsB.SerreExactRange` stated without it is
  *false*, as area SERRE observed — see `Submission/Work/Serre/StableExact.lean`), and
* `Work.RatHurewicz.RangeModelRatAcyclic` — the vanishing of the rational homology of a range model
  of `K(A,k)` below `2k` (C2/C3 of `Submission/Work/Drive/SERRE_BLUEPRINT.md`).

The proof is the delegated argument of
`Submission/Work/RatHurewicz/truncationHomologyTransfer_of_serre.lean` (which states the same result
with the uncorrected hypothesis; that form is a true implication whose proof, however, uses only the
instances with `b = k ≥ 2`, so it is not usable as a reduction), carried by that file's mapping-track
machinery, which is imported here.  The three declarations below are the ones whose statement
mentions the Serre exactness hypothesis; everything else is used from the delegated file.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open CategoryTheory

namespace Work.RatHurewicz

namespace S3Corr

noncomputable section

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-- **Serre's exact sequence in the stable range for the track fibration**: the map of pairs
`(Track inc, trackFibre inc (inc x₀)) → (Z, {inc x₀})` induces an isomorphism on homology in the
stable range, so that `H_{n+2}` of the pair is the relative homology of the range model `Z`. -/
theorem isIso_relPairMap_trackMap (h : Work.Serre.SerreExactRangeCorrected) (inc : C(X, Z)) (x₀ : X)
    (k n : ℕ) (hk : 2 ≤ k) (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 2) :
    IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc) (inc x₀))
      (n + 2)) := by
  refine h (Track inc) Z (trackMap inc) (isHurewiczFibration_trackMap inc) (trackBase inc x₀)
    (inc x₀) (trackMap_trackBase inc x₀) k (k + 1) (by omega) ?_ ?_ (n + 2) ?_
  · intro i hi
    exact hmodel i (by omega) (by omega)
  · intro i hi
    have hbase :
        (⟨trackBase inc x₀, trackMap_trackBase inc x₀⟩ :
          ↥{x : Track inc | trackMap inc x = inc x₀})
        = ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩ := rfl
    rw [hbase]
    exact subsingleton_homotopyGroup_trackFibre inc x₀ (f := k + 1)
      (fun j hj => hconn j (by omega)) i hi
  · omega

/-- **The relative homology of the track pair in the stable range is torsion**, because Serre's
exact sequence identifies it with the relative homology of the range model `Z`, whose rational
homology vanishes below `2k`. -/
theorem nat_smul_eq_zero_trackPair (h : Work.Serre.SerreExactRangeCorrected)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic) (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hkn : k < n + 1) (hrange : n + 1 ≤ 2 * k - 2) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of (Track inc))
      (trackFibre inc (inc x₀))).homology (n + 2)), ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)) := isIso_relPairMap_trackMap h inc x₀ k n hk hmodel hconn hrange
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (trackMap inc) (inc x₀)) (n + 2)).hom :=
    injective_of_isIso_moduleCat _
  have hQ : Subsingleton ↥((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology (n + 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp (hem k hk Z (inc x₀) hmodel (n + 2) (by omega) (by omega))
  intro b
  obtain ⟨N, hN, hNb⟩ := nat_smul_eq_zero_relChains_rangeModel (z₀ := inc x₀) (j := n + 2)
    (by omega) hQ ((HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)).hom b)
  refine ⟨N, hN, ?_⟩
  refine hinj ?_
  rw [map_nsmul, hNb, map_zero]

/-- The homology transfer of the truncation step follows from Serre's exact sequence in the stable range together with the rational acyclicity of the range models of `K(π_k X,k)` below `2k`. Indeed, the long exact sequence of the pair `(X, F)` identifies `ker(H_{n+1}(F) → H_{n+1}(X))` with the image of `H_{n+2}(X,F)`, which is `H̃_{n+2}(Z)` in the stable range by Serre's result and rationally zero by the range-model hypothesis. -/
theorem truncationHomologyTransfer_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic) :
    Work.RatHurewicz.TruncationHomologyTransfer := by
  intro k hk X Z hX hZ inc x₀ hconn hmodel n hkn hrange y hy
  obtain ⟨M, hM, hMy⟩ := hy
  -- the composite identities at the level of homology
  have hcomp1 : fstH inc x₀ (n + 1) = psiH inc x₀ (n + 1) ≫ projH inc x₀ (n + 1) :=
    homologyMap_fst_eq inc x₀ (n + 1)
  have hcomp2 : psiH inc x₀ (n + 1) = homeoH inc x₀ (n + 1) ≫ inclH inc x₀ (n + 1) :=
    homologyMap_psi_eq inc x₀ (n + 1)
  -- injectivities
  have hr_inj : Function.Injective (projH inc x₀ (n + 1)).hom := by
    simpa using injective_homologyMap_trackProj inc (n + 1)
  have he_inj : Function.Injective (homeoH inc x₀ (n + 1)).hom := by
    simpa using injective_homologyMap_trackHomeo inc x₀ (n + 1)
  -- the hypothesis, in the `.hom` form
  have hMy' : M • (fstH inc x₀ (n + 1)).hom y = 0 := hMy
  -- Step 1: `M • ψ_* y = 0`
  have hmiddle : (projH inc x₀ (n + 1)).hom ((psiH inc x₀ (n + 1)).hom y)
      = (fstH inc x₀ (n + 1)).hom y := by
    have hh := hom_apply_congr hcomp1 y
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using hh.symm
  have hstep1 : M • (projH inc x₀ (n + 1)).hom ((psiH inc x₀ (n + 1)).hom y) = 0 := by
    rw [hmiddle]
    exact hMy'
  have hpsi : M • (psiH inc x₀ (n + 1)).hom y = 0 :=
    nsmul_eq_zero_of_injective_addHom (projH inc x₀ (n + 1)).hom.toAddMonoidHom hr_inj hstep1
  -- Step 2: `ı_* (M • e_* y) = 0`
  have hfactor : (psiH inc x₀ (n + 1)).hom y
      = (inclH inc x₀ (n + 1)).hom ((homeoH inc x₀ (n + 1)).hom y) := by
    have hh := hom_apply_congr hcomp2 y
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hker : (inclH inc x₀ (n + 1)).hom (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [map_nsmul, ← hfactor, hpsi]
  -- the same statement in the exact form of `inclChains`
  have hker' : HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (Track inc)) (trackFibre inc (inc x₀))) (n + 1)
      (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [inclChains_trackFibre]
    exact hker
  -- Step 3: the connecting homomorphism hits `M • e_* y`
  obtain ⟨a, ha⟩ := exists_hPairDelta_eq_of_homologyMap_eq_zero (TopCat.of (Track inc))
    (trackFibre inc (inc x₀)) (n + 1) (M • (homeoH inc x₀ (n + 1)).hom y) hker'
  -- Step 4: `a` is torsion (the relative homology of the track pair is torsion)
  obtain ⟨N, hN, hNa⟩ :=
    nat_smul_eq_zero_trackPair h hem inc x₀ k n hk hmodel hconn hkn hrange a
  have hNM : N • (M • (homeoH inc x₀ (n + 1)).hom y) = 0 := by
    rw [← ha]
    rw [show N • ((Work.Cohomology.hPairδ (TopCat.of (Track inc))
          (trackFibre inc (inc x₀)) (n + 1)) a)
        = ((Work.Cohomology.hPairδ (TopCat.of (Track inc))
          (trackFibre inc (inc x₀)) (n + 1)).hom) (N • a)
        from (map_nsmul _ N a).symm]
    rw [hNa, map_zero]
  -- Step 5: `N * M` kills `y`
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  rw [mul_comm N M]
  apply he_inj
  rw [map_nsmul, mul_nsmul, hNM, map_zero]

end

end S3Corr

end Work.RatHurewicz
