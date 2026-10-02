import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.S3Corr
import Submission.Work.RatHurewicz.S3Assembly
import Submission.Work.RatHurewicz.towerStepData
import Submission.Work.RatHurewicz.SerreHurewicz3
import Submission.Work.Serre.StableExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The truncation transfer and the stem induction, **one degree short**

The rational Hurewicz theorem in the stable range is *proved* in this area from the single input
`Work.RatHurewicz.TruncationHomologyTransfer` (`S3Wired.lean`) plus
`Work.RatHurewicz.RangeModelRatAcyclic`.  This module records the *one-degree-short* versions of
both, which are what the consumer `Work.RatHurewicz.sphere_stem_torsion` needs:

* `Work.RatHurewicz.RangeModelRatAcyclic3` — the rational vanishing of a range model of `K(A,k)`
  in degrees `k < j ≤ 2k-2` (one degree less than `RangeModelRatAcyclic`);
* `Work.RatHurewicz.TruncationHomologyTransfer3` — the homology transfer of the truncation step for
  `k < n + 1 ≤ 2k-3` (one degree less than `TruncationHomologyTransfer`), and
* `Work.RatHurewicz.truncationHomologyTransfer3_of_serre : SerreExactRangeCorrected →
  RangeModelRatAcyclic3 → TruncationHomologyTransfer3`,
  `Work.RatHurewicz.hurewiczModTorsionRange3_of_transfer3 : TruncationHomologyTransfer3 →
  HurewiczModTorsionRange3`.

The proofs are those of `S3Corr.lean` and `S3Assembly.lean` with the range bookkeeping relaxed; the
one-short form matters because the *top* degree `2k-1` of the range model is exactly where the
Eilenberg–MacLane computation of the free part is out of reach of the range-form `C2` statements
(see `Submission/Work/Stems/EMVAN_PLAN.md` §4 and `EM_C2_RANGE_FINDING.md`).

Chain: `SerreExactRangeCorrected → RangeModelRatAcyclic3 → TruncationHomologyTransfer3 →
HurewiczModTorsionRange3 → Work.Drive.RationalHurewiczStable3` (proved,
`rationalHurewiczStable3_of_range3`), and `RationalHurewiczStable3 → π_d(Sᵏ) torsion`
(`Work.RatHurewicz.sphere_stem_torsion_of_rationalHurewiczStable3`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

set_option maxHeartbeats 1000000

/-- **The rational homology of a range model, one degree short**: for `k ≥ 2` and a space `Z` with
`π_j(Z) = 0` for `j ≤ 2k-1`, `j ≠ k`, the rational homology vanishes in degrees `k < j ≤ 2k-2`. -/
def RangeModelRatAcyclic3 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (Z : Type) [TopologicalSpace Z] (z₀ : Z),
    IsRangeKModel k (2 * k - 1) z₀ →
    ∀ j : ℕ, k < j → j ≤ 2 * k - 2 →
      IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology j)

/-- **The homology transfer of the truncation step, one degree short.** -/
def TruncationHomologyTransfer3 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X),
    (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀))) →
    IsRangeKModel k (2 * k - 1) (inc x₀) →
    ∀ n : ℕ, k < n + 1 → n + 1 ≤ 2 * k - 3 →
      ∀ y : (Work.Cohomology.singularChains ℤ (TopCat.of (homotopyFibre inc x₀))).homology (n + 1),
        (∃ M : ℕ, 0 < M ∧ M • HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
              (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1) y = 0) →
        ∃ M : ℕ, 0 < M ∧ M • y = 0

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-- **Serre's exact sequence in the stable range for the track fibration**: the map of pairs
`(Track inc, trackFibre inc (inc x₀)) → (Z, {inc x₀})` induces an isomorphism on homology in the
stable range, so that `H_{n+2}` of the pair is the relative homology of the range model `Z`. -/
theorem isIso_relPairMap_trackMap3 (h : Work.Serre.SerreExactRangeCorrected) (inc : C(X, Z)) (x₀ : X)
    (k n : ℕ) (hk : 2 ≤ k) (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 3) :
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
theorem nat_smul_eq_zero_trackPair3 (h : Work.Serre.SerreExactRangeCorrected)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic3) (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j ≤ k, Subsingleton (HomotopyGroup (Fin j) (homotopyFibre inc x₀)
      (homotopyFibreBasepoint inc x₀)))
    (hkn : k < n + 1) (hrange : n + 1 ≤ 2 * k - 3) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of (Track inc))
      (trackFibre inc (inc x₀))).homology (n + 2)), ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap (trackMap inc)
      (inc x₀)) (n + 2)) := isIso_relPairMap_trackMap3 h inc x₀ k n hk hmodel hconn hrange
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
theorem truncationHomologyTransfer3_of_serre (h : Work.Serre.SerreExactRangeCorrected)
    (hem : Work.RatHurewicz.RangeModelRatAcyclic3) :
    Work.RatHurewicz.TruncationHomologyTransfer3 := by
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
    nat_smul_eq_zero_trackPair3 h hem inc x₀ k n hk hmodel hconn hkn hrange a
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
theorem hurewiczTorsionSucc_of_transfer3 (h : TruncationHomologyTransfer3) (hd : TowerStepData) :
    ∀ (d n k : ℕ), (n + 1) - k ≤ d → 2 ≤ k → n + 1 ≤ 2 * k - 3 → HurewiczTorsionSucc k n := by
  intro d
  induction d with
  | zero =>
    intro n k hle hk hr
    have hlt : n + 1 < k ∨ n + 1 = k := by omega
    rcases hlt with hlt | heq
    · exact hurewiczTorsionSucc_of_lt hlt
    · exact hurewiczTorsionSucc_firstDegree hk heq
  | succ d ih =>
    intro n k hle hk hr
    by_cases hnk : n + 1 ≤ k
    · have hlt : n + 1 < k ∨ n + 1 = k := by omega
      rcases hlt with hlt | heq
      · exact hurewiczTorsionSucc_of_lt hlt
      · exact hurewiczTorsionSucc_firstDegree hk heq
    · -- the transfer step: `k < n+1`
      have hkn : k < n + 1 := not_le.mp hnk
      intro X _ x₀ hconn a ha
      obtain ⟨Z, tZ, inc, hmodel, hfib, hsurj⟩ := hd k n hk hkn (by omega) X x₀ hconn
      letI := tZ
      obtain ⟨b, hb⟩ := hsurj a
      have hbmap : HomotopyGroup.map (homotopyFibreFst inc x₀) b = a := by
        rw [← πmap_eq_map (homotopyFibreFst inc x₀) n (homotopyFibreBasepoint inc x₀) b]
        exact hb
      -- naturality of the Hurewicz map along the projection of the homotopy fibre
      have hnat := Work.Stems.hurewiczMap_natural (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (homotopyFibreFst inc x₀)
        (x₀ := homotopyFibreBasepoint inc x₀) b
      -- the Hurewicz class of `a` is the image of that of `b`
      have hclass : Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a =
          HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
            (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1)
            (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
              (homotopyFibreBasepoint inc x₀) b) := by
        rw [← hbmap, Work.Stems.hurewiczMapN_eq_hurewiczMap,
          Work.Stems.hurewiczMapN_eq_hurewiczMap]
        exact hnat
      -- transfer the torsion of the Hurewicz class to the fibre
      obtain ⟨N, hN, hNa⟩ := ha
      have hker : ∃ M : ℕ, 0 < M ∧ M • HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
            (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1)
            (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
              (homotopyFibreBasepoint inc x₀) b) = 0 := by
        refine ⟨N, hN, ?_⟩
        rw [← hclass]
        simpa [Nat.cast_smul_eq_nsmul] using hNa
      obtain ⟨M, hM, hMb⟩ :=
        h k hk X Z inc x₀ hfib hmodel n hkn hr
          (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
            (homotopyFibreBasepoint inc x₀) b) hker
      -- the induction hypothesis at connectivity `k+1`, same degree
      obtain ⟨M', hM', hbM⟩ := ih n (k + 1) (by omega) (by omega) (by omega)
        (homotopyFibre inc x₀) (homotopyFibreBasepoint inc x₀)
        (fun j hj => hfib j (by omega)) b ⟨M, hM, by simpa [Nat.cast_smul_eq_nsmul] using hMb⟩
      refine ⟨M', hM', ?_⟩
      have hpow : (Work.StemsB.πmap (homotopyFibreFst inc x₀) n
          (homotopyFibreBasepoint inc x₀) b) ^ M' = 1 := by
        rw [← map_pow (Work.StemsB.πmap (homotopyFibreFst inc x₀) n
          (homotopyFibreBasepoint inc x₀)) b M', hbM, map_one]
      exact hb ▸ hpow


/-- **The range form of the rational Hurewicz theorem, one degree short**, from the single
homology-transfer input. -/
theorem hurewiczModTorsionRange3_of_transfer3 (h : TruncationHomologyTransfer3) :
    HurewiczModTorsionRange3 :=
  fun k hk X _ x₀ hconn n hn a ha =>
    hurewiczTorsionSucc_of_transfer3 h towerStepData (n + 1) n k (by omega) hk hn X x₀ hconn a ha

end

end Work.RatHurewicz
