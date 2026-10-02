/-
# TripodCert — the periodic ray-box chain of the `b₂`-tripod

Area `Submission/Work/TripodCert/`.  This module assembles the emitted certificate (`Data.lean`,
`Check.lean`, `Levels.lean`) into the covering statement of the chain and extracts from it the
statement used by the landing argument:

* `CT_hp` — the (D2) separation certificate of the family `CT k j`;
* `CT_D1` — the (D1) preimage cover of one step;
* `chainT` — **every ray piece of the six-angle orbit is covered by its box**
  (`Work.SeedCertRay.chain_sound_sets`);
* `landsN_mem_CT` — **the landing point of the `θ j`-ray lies in the periodic box** `CT KT j`,
  because all the pieces below any bounded level lie in the periodic family, which is constant
  from level `KT` on.
-/
import Mathlib
import Submission.Work.TripodCert.Basic
import Submission.Work.TripodCert.Data
import Submission.Work.TripodCert.Sound
import Submission.Work.TripodCert.Levels
import Submission.Work.TripodCert.lvl0_coverT
import Submission.Work.TripodCert.dirBoundT
import Submission.Work.SeedCertRay.chain_sound_sets
import Submission.Work.SeedCertRay.petal_tail_infra
import Submission.Work.SeedCertRay.landsAt_alphas_of_disks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The half-plane direction used at the chain index `k`: the descent direction below `KT`, the
interface direction at `KT - 1`, and the periodic direction from `KT` on. -/
def vdirCT (k j : ℕ) : ℚ × ℚ :=
  if k + 1 < KT then vdirOf (dirT k) j else if k < KT then vdirOf ifaceDir j else vdirOf dirPer j

/-- **(D2) of the chain**: one open half-plane contains the sub-disks of both levels `k` and
`k + 1` of each angle class. -/
theorem CT_hp (k j : ℕ) :
    (∀ i : Fin NC, (boxT (k + 1) j i).toSet ⊆ halfplane (vdirCT k j)) ∧
    (∀ i : Fin NC, (boxT k j i).toSet ⊆ halfplane (vdirCT k j)) := by
  by_cases h1 : k + 1 < KT
  · have hk : k < KT := by omega
    have hchk : chkDirT (dirT k) (dskT (k + 1)) (dskT k) = true := chkDirTAt k (by omega)
    have hd := level_HP (dirT k) (dskT (k + 1)) (dskT k) hchk j
    have e0 : vdirCT k j = vdirOf (dirT k) j := by simp only [vdirCT, if_pos h1]
    have e1 : boxT (k + 1) j
        = fun i => Work.SeedCertRay.dskOf (dskT (k + 1)) ((j % 6) * NC + i.val) := by
      funext i; simp only [boxT, boxOfT, if_pos h1]
    have e2 : boxT k j = fun i => Work.SeedCertRay.dskOf (dskT k) ((j % 6) * NC + i.val) := by
      funext i; simp only [boxT, boxOfT, if_pos hk]
    rw [e1, e2, e0]; exact hd
  · by_cases hk : k < KT
    · have hk1 : k = KT - 1 := by omega
      have hchk : chkDirT (dirT (KT - 1)) perT (dskT (KT - 1)) = true := chkDirIface
      have hd := level_HP (dirT (KT - 1)) perT (dskT (KT - 1)) hchk j
      have d1 : dirT (KT - 1) = ifaceDir := by decide
      have e0 : vdirCT k j = vdirOf ifaceDir j := by
        simp only [vdirCT, if_neg h1, if_pos hk]
      have e1 : boxT (k + 1) j = fun i => Work.SeedCertRay.dskOf perT ((j % 6) * NC + i.val) := by
        funext i; simp only [boxT, boxOfT, if_neg h1]
      have e2 : boxT k j
          = fun i => Work.SeedCertRay.dskOf (dskT (KT - 1)) ((j % 6) * NC + i.val) := by
        funext i
        simp only [boxT, boxOfT, if_pos hk]
        rw [hk1]
      rw [d1] at hd
      rw [e1, e2, e0]
      exact hd
    · have hchk : chkDirT dirPer perT perT = true := chkPerDir
      have hd := level_HP dirPer perT perT hchk j
      have e0 : vdirCT k j = vdirOf dirPer j := by
        simp only [vdirCT, if_neg h1, if_neg hk]
      have e1 : boxT (k + 1) j = fun i => Work.SeedCertRay.dskOf perT ((j % 6) * NC + i.val) := by
        funext i; simp only [boxT, boxOfT, if_neg (by omega : ¬ k + 1 < KT)]
      have e2 : boxT k j = fun i => Work.SeedCertRay.dskOf perT ((j % 6) * NC + i.val) := by
        funext i; simp only [boxT, boxOfT, if_neg hk]
      rw [e1, e2, e0]; exact hd

/-- **(D1) of one step** of the chain, for every sub-disk index. -/
theorem CT_D1 {c : ℂ} (hcX : Work.SeedCertRay.Xb.mem c) (k j : ℕ) (i : Fin NC) :
    Work.SeedCertRay.DiskCover (boxT k (j + 1) i) Work.SeedCertRay.Xb (boxT (k + 1) j i) := by
  by_cases h1 : k + 1 < KT
  · have hk : k < KT := by omega
    have hchk : chkLevelT (dskT k) (dskT (k + 1)) (crtT k) PXM PYM RADM = true :=
      chkTAt k (by omega)
    have hd := level_D1 (dskT k) (dskT (k + 1)) (crtT k) hchk j i
    have e1 : boxT k (j + 1) i
        = Work.SeedCertRay.dskOf (dskT k) (((j + 1) % 6) * NC + i.val) := by
      simp only [boxT, boxOfT, if_pos hk]
    have e2 : boxT (k + 1) j i
        = Work.SeedCertRay.dskOf (dskT (k + 1)) ((j % 6) * NC + i.val) := by
      simp only [boxT, boxOfT, if_pos h1]
    rw [e1, e2]; exact hd
  · by_cases hk : k < KT
    · have hk1 : k = KT - 1 := by omega
      have hchk : chkLevelT (dskT (KT - 1)) perT ifaceCrtT PXM PYM RADM = true := chkT_iface
      have hd := level_D1 (dskT (KT - 1)) perT ifaceCrtT hchk j i
      have e1 : boxT k (j + 1) i
          = Work.SeedCertRay.dskOf (dskT (KT - 1)) (((j + 1) % 6) * NC + i.val) := by
        simp only [boxT, boxOfT, if_pos hk]
        rw [hk1]
      have e2 : boxT (k + 1) j i = Work.SeedCertRay.dskOf perT ((j % 6) * NC + i.val) := by
        simp only [boxT, boxOfT, if_neg h1]
      rw [e1, e2]; exact hd
    · have hchk : chkLevelT perT perT crtPer PXM PYM RADM = true := chkPer
      have hd := level_D1 perT perT crtPer hchk j i
      have e1 : boxT k (j + 1) i
          = Work.SeedCertRay.dskOf perT (((j + 1) % 6) * NC + i.val) := by
        simp only [boxT, boxOfT, if_neg hk]
      have e2 : boxT (k + 1) j i = Work.SeedCertRay.dskOf perT ((j % 6) * NC + i.val) := by
        simp only [boxT, boxOfT, if_neg (by omega : ¬ k + 1 < KT)]
      rw [e1, e2]; exact hd

/-- **(D1) of the chain** in the set-valued form consumed by `chain_sound_sets`. -/
theorem CT_D1sets {c : ℂ} (hcX : Work.SeedCertRay.Xb.mem c) (k j : ℕ) (u : ℂ)
    (hu : Tantibar c u ∈ CT k (j + 1)) : u ∈ CT (k + 1) j ∨ -u ∈ CT (k + 1) j := by
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hu
  rcases CT_D1 hcX k j i (Tantibar c u) c u hi hcX rfl with h | h
  · exact Or.inl (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)
  · exact Or.inr (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)

/-- **(D2) of the chain** in the set-valued form consumed by `chain_sound_sets`. -/
theorem CT_D2 (k j : ℕ) :
    IsClosed (CT (k + 1) j) ∧ Disjoint (CT (k + 1) j) (-CT (k + 1) j)
      ∧ Disjoint (CT k j) (-CT (k + 1) j) := by
  obtain ⟨h1, h2⟩ := CT_hp k j
  have h1' : CT (k + 1) j ⊆ halfplane (vdirCT k j) :=
    Work.SeedCertRay.diskUnion_subset_halfplane h1
  have h2' : CT k j ⊆ halfplane (vdirCT k j) :=
    Work.SeedCertRay.diskUnion_subset_halfplane h2
  exact ⟨Work.SeedCertRay.isClosed_diskUnion _, disjoint_neg_of_halfplane h1' h1',
    disjoint_neg_of_halfplane h2' h1'⟩

/-- The level-`0` box of the angle class `j % 6` is the emitted level-0 data. -/
theorem CT_zero_eq (j : ℕ) : CT 0 j = Work.SeedCertRay.diskUnion (lvl0DiskT (j % 6)) := by
  have h : boxT 0 j = lvl0DiskT (j % 6) := by
    funext i
    simp only [boxT, boxOfT, lvl0DiskT, if_pos (show 0 < KT by norm_num [KT]), Nat.mod_mod]
  rw [CT, h]

/-- **The chain covering.**  Every ray piece of the six-angle orbit of `22/63` lies in the
certified box family. -/
theorem chainT {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Work.SeedCertRay.Xb.mem c) :
    ∀ k j, Work.SeedCertRay.seg hN (theta j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CT k j := by
  refine Work.SeedCertRay.chain_sound_sets hN hφ theta theta_succ Work.SeedCertRay.rhoL
    Work.SeedCertRay.rhoL_spec CT ?_ ?_ ?_
  · intro j
    have hj : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have hcov := lvl0_coverT hN hφ hc hc2 (j % 6) hj (dirBoundT (j % 6) hj)
    rw [theta_mod j, CT_zero_eq j]
    exact hcov
  · intro k j u hu
    exact CT_D1sets hcX k j u hu
  · intro k j
    exact CT_D2 k j

/-- The union of the chain boxes from level `KT` on is the periodic box: the family is constant
there. -/
theorem union_CT (j : ℕ) : (⋃ l ∈ {l : ℕ | KT ≤ l}, CT l j) = CT KT j := by
  refine le_antisymm (iUnion₂_subset fun l hl => ?_) (subset_iUnion₂ (s := fun l _ => CT l j)
    KT (le_refl KT))
  have hl' : KT ≤ l := hl
  have hbox : boxT l j = boxT KT j := by
    funext i
    simp only [boxT, boxOfT, if_neg (by omega : ¬ l < KT), if_neg (by omega : ¬ KT < KT)]
  show Work.SeedCertRay.diskUnion (boxT l j) ⊆ Work.SeedCertRay.diskUnion (boxT KT j)
  rw [hbox]

/-- **The landing point of the `θ j`-ray lies in the periodic box.**  Every piece of level
`l ≥ KT` is inside `CT KT j`, and the ray points of levels below any bounded level are pieces of
levels `≥ KT` (`rho_window`), so the limit lies in the closed set `CT KT j`. -/
theorem landsN_mem_CT {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hchain : ∀ k j, Work.SeedCertRay.seg hN (theta j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CT k j)
    {j : ℕ} {y : ℂ} (hy : Work.EL.LandsN hN (theta j) y) : y ∈ CT KT j := by
  have hclosed : IsClosed (CT KT j) := Work.SeedCertRay.isClosed_diskUnion _
  rw [← hclosed.closure_eq]
  have hset : Set.Ioo (1 : ℝ) (Work.SeedCertRay.rhoL KT) ∈ nhdsWithin 1 (Set.Ioi 1) := by
    have h1 : Set.Iio (Work.SeedCertRay.rhoL KT) ∈ 𝓝 (1 : ℝ) :=
      isOpen_Iio.mem_nhds (Work.SeedCertRay.rhoL_gt_one KT)
    have h2 : Set.Ioi (1 : ℝ) ∩ Set.Iio (Work.SeedCertRay.rhoL KT)
        ∈ nhdsWithin 1 (Set.Ioi 1) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds h1)
    refine Filter.mem_of_superset h2 ?_
    intro t ht
    exact ht
  refine mem_closure_of_tendsto hy (Filter.mem_of_superset hset ?_)
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  rw [← union_CT j]
  have hwin := Work.SeedCertRay.rho_window Work.SeedCertRay.rhoL_spec ht1
    (j₀ := KT - 1) (by norm_num [KT])
    (by simpa [Nat.sub_add_cancel (by norm_num [KT] : 1 ≤ KT)] using ht2)
  obtain ⟨l, hl, hlo, hhi⟩ := hwin
  have hlKT : KT ≤ l := by
    by_contra hcon
    have h2 : Work.SeedCertRay.rhoL KT ≤ Work.SeedCertRay.rhoL (l + 1) :=
      Work.SeedCertRay.rho_antitone Work.SeedCertRay.rhoL_spec (by omega)
    linarith
  exact mem_iUnion₂.mpr ⟨l, hlKT, hchain l j ⟨t, ⟨hlo, hhi⟩, rfl⟩⟩

end Work.TripodCert
