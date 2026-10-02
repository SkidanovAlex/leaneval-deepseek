import Mathlib
import Submission.Work.RatHurewicz.truncationHomologyTransfer_of_serre
import Submission.Work.RatHurewicz.S3Inputs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The truncation transfer from the injectivity of the stable-range Serre comparison

Area **RATHUREWICZ**.  This module is the **closing assembly** of the chapter's single remaining
input `Work.RatHurewicz.TruncationHomologyTransfer`: it derives the transfer from

* the *injectivity* of the stable-range Serre comparison for the mapping track
  (`Submission/Work/RatHurewicz/trackRelPairMap_injective.lean`), i.e. the injectivity half of K5 of
  `Submission/Work/Drive/SERRE_BLUEPRINT.md`, and
* the rational acyclicity of the range models of `K(A,k)`
  (`Submission/Work/RatHurewicz/rangeModelRatAcyclic.lean`), i.e. C2/C3.

Both are given here as hypotheses, so that the assembly is independent of their proofs; the same
argument is carried out against `Work.Serre.SerreExactRangeCorrected` in
`Submission/Work/RatHurewicz/S3Corr.lean`.  The mapping-track machinery (the track
`Track inc = {(x,γ) : γ(1) = inc x}`, its fibration `trackMap inc`, the homeomorphism of its fibre
with `homotopyFibre inc x₀`, and the comparison of the pair connective with the fibre inclusion) is
imported from `truncationHomologyTransfer_of_serre.lean`.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open CategoryTheory

namespace Work.RatHurewicz

namespace S3Inj

noncomputable section

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-- **The relative homology of the track pair is torsion in the stable range**, given the
injectivity of the comparison map and the rational acyclicity of the range model: the image of a
class of `H_{n+2}(Track, trackFibre)` in `H_{n+2}(Z, {z₀})` is killed by some positive multiple, and
injectivity pulls this back. -/
theorem nat_smul_eq_zero_trackPair_of_injective (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hinj : Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (trackMap inc) (inc x₀)) (n + 2)).hom)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic)
    (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hkn : k < n + 1) (hrange : n + 1 ≤ 2 * k - 2) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of (Track inc))
      (trackFibre inc (inc x₀))).homology (n + 2)), ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  have hQ : Subsingleton ↥((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology (n + 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp (hem k hk Z (inc x₀) hmodel (n + 2) (by omega) (by omega))
  intro b
  obtain ⟨N, hN, hNb⟩ := nat_smul_eq_zero_relChains_rangeModel (z₀ := inc x₀) (j := n + 2)
    (by omega) hQ ((HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)).hom b)
  refine ⟨N, hN, ?_⟩
  refine hinj ?_
  rw [map_nsmul, hNb, map_zero]

/-- **The homology transfer of the truncation step**, from the injectivity of the stable-range Serre
comparison for the mapping track and the rational acyclicity of the range models. -/
theorem truncationHomologyTransfer_of_track_injective
    (hinj : ∀ {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (inc : C(X, Z)) (x₀ : X)
      (k n : ℕ), 2 ≤ k → IsRangeKModel k (2 * k - 1) (inc x₀) →
      (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
        (homotopyFibreBasepoint inc x₀))) →
      n + 1 ≤ 2 * k - 2 →
      Function.Injective (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (trackMap inc) (inc x₀)) (n + 2)).hom)
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
    nat_smul_eq_zero_trackPair_of_injective inc x₀ k n hk
      (hinj inc x₀ k n hk hmodel hconn hrange) hem hmodel hkn hrange a
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

end S3Inj

end Work.RatHurewicz
