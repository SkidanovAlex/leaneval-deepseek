-- **CORRECTION (project lead, 2026-09-26): the "K5 at `b = 1` is false" claim of this area is
-- RETRACTED** (see `Submission/Work/StemsB/FINDING_K5_b1_FALSE.md`).  `Work.Serre.SerreStableExact`
-- *is* proved (`#print axioms` = `{propext, Classical.choice, Quot.sound}`) and the statements of
-- this file, which carry the stronger hypothesis `2 ≤ b`, are correct but *redundant* with it, not a
-- correction of it.  The docstring below was written under the retracted belief; read it with that
-- in mind.  (The mistake: the fibre hypothesis `∀ i < f, Subsingleton (π_i F)` includes `i = 0`,
-- i.e. path connectedness of the fibre, so a disconnected fibre is never a counterexample.)

import Mathlib
import Submission.Work.StemsB.serreStableExactTwo
import Submission.Work.RatHurewicz.S3Corr
import Submission.Work.RatHurewicz.truncationHomologyTransfer_of_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The S3 chain ported to the **corrected** K5 (`2 ≤ b`)

`Work.Serre.SerreExactRangeCorrected` (the workspace's K5, hypothesis `1 ≤ b`) is **false as stated**;
see `Submission/Work/StemsB/FINDING_K5_b1_FALSE.md` (counterexample: the universal cover `ℝ → S¹`
with `b = 1`, `f = 2`, where `H_1(ℝ, {0}) ≅ ⊕_{k≠0}ℤ` is compared with `H_1(S¹,{pt}) ≅ ℤ`).  The
corrected statement — base simply connected, `2 ≤ b`, so that the local system `H_*(F)` is simple —
is proved axiom-clean in `Submission/Work/StemsB/serreStableExactTwo.lean` as
`Work.StemsB.SerreExactRangeCorrectedTwo`.

The S3 chain consumes K5 exactly once, in `Work.RatHurewicz.S3Corr.isIso_relPairMap_trackMap`, at
`b = k` with `k ≥ 2` (the `hk : 2 ≤ k` in scope discharges `2 ≤ b`).  This file ports the three
K5-dependent declarations of `Submission/Work/RatHurewicz/S3Corr.lean` to the corrected hypothesis;
the proofs are those of that file verbatim (the only change is the type of the threaded hypothesis
`h`).  Everything else — `Track`, `trackMap`, `trackFibre`, `psiH`, `projH`, `inclH`, `homeoH`,
`fstH`, `homologyMap_fst_eq`, `homologyMap_psi_eq`, `inclChains_trackFibre`,
`exists_hPairDelta_eq_of_homologyMap_eq_zero`, `injective_homologyMap_trackProj`,
`injective_homologyMap_trackHomeo`, `subsingleton_homotopyGroup_trackFibre`,
`nat_smul_eq_zero_relChains_rangeModel`, … — is imported unchanged from area RATHUREWICZ.

Consequence: with `Work.StemsB.truncationHomologyTransfer_of_serreTwo` one gets
`Work.RatHurewicz.rationalHurewiczStable3_of_transfer` applied to it, hence this area's ladder
`Submission/Work/StemsB/contractInputs.lean` no longer needs the (false) `SerreExactRangeCorrected`.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open CategoryTheory
open Work.RatHurewicz

namespace Work.StemsB

noncomputable section

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-- **Serre's exact sequence in the stable range for the track fibration**: the map of pairs
`(Track inc, trackFibre inc (inc x₀)) → (Z, {inc x₀})` induces an isomorphism on homology in the
stable range, so that `H_{n+2}` of the pair is the relative homology of the range model `Z`. -/
theorem isIso_relPairMap_trackMapTwo (h : Work.StemsB.SerreExactRangeCorrectedTwo) (inc : C(X, Z)) (x₀ : X)
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
theorem nat_smul_eq_zero_trackPairTwo (h : Work.StemsB.SerreExactRangeCorrectedTwo)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic) (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hkn : k < n + 1) (hrange : n + 1 ≤ 2 * k - 2) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of (Track inc))
      (trackFibre inc (inc x₀))).homology (n + 2)), ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)) := isIso_relPairMap_trackMapTwo h inc x₀ k n hk hmodel hconn hrange
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

theorem truncationHomologyTransfer_of_serreTwo (h : Work.StemsB.SerreExactRangeCorrectedTwo)
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
    nat_smul_eq_zero_trackPairTwo h hem inc x₀ k n hk hmodel hconn hkn hrange a
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

end Work.StemsB

#print axioms Work.StemsB.isIso_relPairMap_trackMapTwo
#print axioms Work.StemsB.nat_smul_eq_zero_trackPairTwo
#print axioms Work.StemsB.truncationHomologyTransfer_of_serreTwo
