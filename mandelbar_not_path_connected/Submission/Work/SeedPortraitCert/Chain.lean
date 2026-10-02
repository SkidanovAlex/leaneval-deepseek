/-
# SeedPortraitCert — the periodic ray-chain certificate of the two frontier orbits

Area `Submission/Work/SeedPortraitCert/`.  This module assembles the emitted certificate
(`Data.lean`, `Check.lean`, `Levels.lean`, `Sound.lean`, `Lvl0.lean`) into the two covering
statements of the chain and extracts the statement used by the landing argument:

* `CT_hpP` — the (D2) separation certificate of the disk family `boxP k j`;
* `CT_D1P` — the (D1) preimage cover of one step;
* `chainA` / `chainB` — **every ray piece of the two `5`-cycles is covered by its disk**
  (`Work.SeedCertRay.chain_sound_sets`);
* `landsN_mem_CTA` / `landsN_mem_CTB` — **the landing point of the `angA j`-ray lies in the
  periodic family** `CTA KT j` (resp. `CTB KT j`), because all pieces below any bounded level lie
  in the periodic family, which is constant from level `KT` on.

The two chains are the restrictions of the emitted ten-class data to the classes `0 … 4`
(the `12/33`-cycle, family `CTA`) and to the classes `5 … 9` (the `13/33`-cycle, family `CTB`).
-/
import Mathlib
import Submission.Work.SeedPortraitCert.Data
import Submission.Work.SeedPortraitCert.Angles
import Submission.Work.SeedPortraitCert.Lvl0
import Submission.Work.SeedPortraitCert.Sound
import Submission.Work.SeedPortraitCert.Levels
import Submission.Work.SeedCertRay.chain_sound_sets
import Submission.Work.SeedCertRay.petal_tail_infra

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

namespace Work.SeedPortraitCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The half-plane direction used at the chain index `k`: the descent direction below `KT`, the
interface direction at `KT - 1`, and the periodic direction from `KT` on. -/
def vdirCTP (k j : ℕ) : ℚ × ℚ :=
  if k + 1 < KT then vdirOfP (dirP k) j else if k < KT then vdirOfP ifaceDirP j else vdirOfP dirPerP j

/-- **(D2) of the chain**: one open half-plane contains the disks of both levels `k` and `k + 1`
of each angle class. -/
theorem CT_hpP (k j : ℕ) :
    (∀ i : Fin NC, (boxP (k + 1) j i).toSet ⊆ halfplane (vdirCTP k j)) ∧
    (∀ i : Fin NC, (boxP k j i).toSet ⊆ halfplane (vdirCTP k j)) := by
  by_cases h1 : k + 1 < KT
  · have hk : k < KT := by omega
    have hchk : chkDirP (dirP k) (dskP (k + 1)) (dskP k) = true := chkDirPAt k (by omega)
    have hd := level_HPP (dirP k) (dskP (k + 1)) (dskP k) hchk j
    have e0 : vdirCTP k j = vdirOfP (dirP k) j := by simp only [vdirCTP, if_pos h1]
    have e1 : boxP (k + 1) j
        = fun i => Work.SeedCertRay.dskOf (dskP (k + 1)) ((j % 10) * NC + i.val) := by
      funext i; simp only [boxP, boxOfP, if_pos h1]
    have e2 : boxP k j = fun i => Work.SeedCertRay.dskOf (dskP k) ((j % 10) * NC + i.val) := by
      funext i; simp only [boxP, boxOfP, if_pos hk]
    rw [e1, e2, e0]; exact hd
  · by_cases hk : k < KT
    · have hk1 : k = KT - 1 := by omega
      have hchk : chkDirP (dirP (KT - 1)) perP (dskP (KT - 1)) = true := chkDirIfaceP
      have hd := level_HPP (dirP (KT - 1)) perP (dskP (KT - 1)) hchk j
      have d1 : dirP (KT - 1) = ifaceDirP := by decide
      have e0 : vdirCTP k j = vdirOfP ifaceDirP j := by
        simp only [vdirCTP, if_neg h1, if_pos hk]
      have e1 : boxP (k + 1) j = fun i => Work.SeedCertRay.dskOf perP ((j % 10) * NC + i.val) := by
        funext i; simp only [boxP, boxOfP, if_neg h1]
      have e2 : boxP k j
          = fun i => Work.SeedCertRay.dskOf (dskP (KT - 1)) ((j % 10) * NC + i.val) := by
        funext i
        simp only [boxP, boxOfP, if_pos hk]
        rw [hk1]
      rw [d1] at hd
      rw [e1, e2, e0]
      exact hd
    · have hchk : chkDirP dirPerP perP perP = true := chkPerDirP
      have hd := level_HPP dirPerP perP perP hchk j
      have e0 : vdirCTP k j = vdirOfP dirPerP j := by
        simp only [vdirCTP, if_neg h1, if_neg hk]
      have e1 : boxP (k + 1) j = fun i => Work.SeedCertRay.dskOf perP ((j % 10) * NC + i.val) := by
        funext i; simp only [boxP, boxOfP, if_neg (by omega : ¬ k + 1 < KT)]
      have e2 : boxP k j = fun i => Work.SeedCertRay.dskOf perP ((j % 10) * NC + i.val) := by
        funext i; simp only [boxP, boxOfP, if_neg hk]
      rw [e1, e2, e0]; exact hd

/-- **(D1) of one step** of the chain, for every sub-disk index. -/
theorem CT_D1P {c : ℂ} (hcX : Work.SeedCertRay.Xb.mem c) (k : ℕ) (j : ℕ) (hj : j < 10)
    (i : Fin NC) :
    Work.SeedCertRay.DiskCover (boxP k (sucP j) i) Work.SeedCertRay.Xb (boxP (k + 1) j i) := by
  by_cases h1 : k + 1 < KT
  · have hk : k < KT := by omega
    have hchk : chkLevelP (dskP k) (dskP (k + 1)) (crtP k) PXM PYM RADM = true :=
      chkPAt k (by omega)
    have hd := level_D1P (dskP k) (dskP (k + 1)) (crtP k) hchk j i
    have e1 : boxP k (sucP j) i
        = Work.SeedCertRay.dskOf (dskP k) ((sucP j % 10) * NC + i.val) := by
      simp only [boxP, boxOfP, if_pos hk]
    have e2 : boxP (k + 1) j i
        = Work.SeedCertRay.dskOf (dskP (k + 1)) ((j % 10) * NC + i.val) := by
      simp only [boxP, boxOfP, if_pos h1]
    have esuc : sucP j % 10 = sucP j := by
      rw [Nat.mod_eq_of_lt]; simp only [sucP]; split <;> omega
    have emod : sucP (j % 10) = sucP j := by rw [Nat.mod_eq_of_lt hj]
    rw [e1, e2, esuc, ← emod]; exact hd
  · by_cases hk : k < KT
    · have hk1 : k = KT - 1 := by omega
      have hchk : chkLevelP (dskP (KT - 1)) perP ifaceCrtP PXM PYM RADM = true := chkP_iface
      have hd := level_D1P (dskP (KT - 1)) perP ifaceCrtP hchk j i
      have e1 : boxP k (sucP j) i
          = Work.SeedCertRay.dskOf (dskP (KT - 1)) ((sucP j % 10) * NC + i.val) := by
        simp only [boxP, boxOfP, if_pos hk]
        rw [hk1]
      have e2 : boxP (k + 1) j i = Work.SeedCertRay.dskOf perP ((j % 10) * NC + i.val) := by
        simp only [boxP, boxOfP, if_neg h1]
      have esuc : sucP j % 10 = sucP j := by
        rw [Nat.mod_eq_of_lt]; simp only [sucP]; split <;> omega
      have emod : sucP (j % 10) = sucP j := by rw [Nat.mod_eq_of_lt hj]
      rw [e1, e2, esuc, ← emod]; exact hd
    · have hchk : chkLevelP perP perP crtPerP PXM PYM RADM = true := chkPerP
      have hd := level_D1P perP perP crtPerP hchk j i
      have e1 : boxP k (sucP j) i
          = Work.SeedCertRay.dskOf perP ((sucP j % 10) * NC + i.val) := by
        simp only [boxP, boxOfP, if_neg hk]
      have e2 : boxP (k + 1) j i = Work.SeedCertRay.dskOf perP ((j % 10) * NC + i.val) := by
        simp only [boxP, boxOfP, if_neg (by omega : ¬ k + 1 < KT)]
      have esuc : sucP j % 10 = sucP j := by
        rw [Nat.mod_eq_of_lt]; simp only [sucP]; split <;> omega
      have emod : sucP (j % 10) = sucP j := by rw [Nat.mod_eq_of_lt hj]
      rw [e1, e2, esuc, ← emod]; exact hd

/-- **(D2) of the chain** in the set-valued form consumed by `chain_sound_sets`. -/
theorem CT_D2P (k j : ℕ) :
    IsClosed (CT (k + 1) j) ∧ Disjoint (CT (k + 1) j) (-CT (k + 1) j)
      ∧ Disjoint (CT k j) (-CT (k + 1) j) := by
  obtain ⟨h1, h2⟩ := CT_hpP k j
  have h1' : CT (k + 1) j ⊆ halfplane (vdirCTP k j) :=
    Work.SeedCertRay.diskUnion_subset_halfplane h1
  have h2' : CT k j ⊆ halfplane (vdirCTP k j) :=
    Work.SeedCertRay.diskUnion_subset_halfplane h2
  exact ⟨Work.SeedCertRay.isClosed_diskUnion _, disjoint_neg_of_halfplane h1' h1',
    disjoint_neg_of_halfplane h2' h1'⟩

/-! ## The two five-class families

The `12/33`-chain runs on the first five angle classes of the emitted data, the `13/33`-chain on
the last five; the two families are therefore the restrictions

  `CTA k j = CT k (j % 5)`   and   `CTB k j = CT k (5 + j % 5)`. -/

/-- The set family of the `12/33`-cycle. -/
def CTA (k j : ℕ) : Set ℂ := CT k (j % 5)

/-- The set family of the `13/33`-cycle. -/
def CTB (k j : ℕ) : Set ℂ := CT k (5 + j % 5)

/-- The successor inside the first cycle, as the index map of `CTA`. -/
theorem sucP_mod5 (j : ℕ) : sucP (j % 5) = (j + 1) % 5 := by
  rw [sucP_of_lt (Nat.mod_lt j (by norm_num))]
  exact (Nat.add_mod j 1 5).symm

theorem mod5_shift (j : ℕ) : (5 + j % 5 + 1) % 5 = (j + 1) % 5 := by
  have h1 : 5 + j % 5 + 1 = j % 5 + 6 := by omega
  rw [h1, Nat.add_mod, Nat.add_mod, Nat.mod_mod]
  norm_num

/-- The successor inside the second cycle, as the index map of `CTB`. -/
theorem sucP_mod5_shift (j : ℕ) : sucP (5 + j % 5) = 5 + (j + 1) % 5 := by
  rw [sucP_of_ge (by omega)]
  congr 1
  exact mod5_shift j

/-- **(D1) of the `12/33`-chain.** -/
theorem CTA_D1 {c : ℂ} (hcX : Work.SeedCertRay.Xb.mem c) (k j : ℕ) (u : ℂ)
    (hu : Tantibar c u ∈ CTA k (j + 1)) : u ∈ CTA (k + 1) j ∨ -u ∈ CTA (k + 1) j := by
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hu
  have hstep := CT_D1P hcX k (j % 5) (by omega) i
  rw [sucP_mod5 j] at hstep
  rcases hstep (Tantibar c u) c u hi hcX rfl with h | h
  · exact Or.inl (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)
  · exact Or.inr (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)

/-- **(D1) of the `13/33`-chain.** -/
theorem CTB_D1 {c : ℂ} (hcX : Work.SeedCertRay.Xb.mem c) (k j : ℕ) (u : ℂ)
    (hu : Tantibar c u ∈ CTB k (j + 1)) : u ∈ CTB (k + 1) j ∨ -u ∈ CTB (k + 1) j := by
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hu
  have hstep := CT_D1P hcX k (5 + j % 5) (by omega) i
  rw [sucP_mod5_shift j] at hstep
  rcases hstep (Tantibar c u) c u hi hcX rfl with h | h
  · exact Or.inl (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)
  · exact Or.inr (Work.SeedCertRay.mem_diskUnion.mpr ⟨i, h⟩)

/-- **(D2) of the `12/33`-chain.** -/
theorem CTA_D2 (k j : ℕ) :
    IsClosed (CTA (k + 1) j) ∧ Disjoint (CTA (k + 1) j) (-CTA (k + 1) j)
      ∧ Disjoint (CTA k j) (-CTA (k + 1) j) :=
  CT_D2P k (j % 5)

/-- **(D2) of the `13/33`-chain.** -/
theorem CTB_D2 (k j : ℕ) :
    IsClosed (CTB (k + 1) j) ∧ Disjoint (CTB (k + 1) j) (-CTB (k + 1) j)
      ∧ Disjoint (CTB k j) (-CTB (k + 1) j) :=
  CT_D2P k (5 + j % 5)

/-! ## The two chains -/

/-- **The chain covering of the `12/33`-cycle.**  Every ray piece of the `angA j`-orbit lies in
the certified disk family. -/
theorem chainA {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Work.SeedCertRay.Xb.mem c) :
    ∀ k j, Work.SeedCertRay.seg hN (angA j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CTA k j := by
  refine Work.SeedCertRay.chain_sound_sets hN hφ angA angA_succ Work.SeedCertRay.rhoL
    Work.SeedCertRay.rhoL_spec CTA ?_ ?_ ?_
  · intro j
    have hj : j % 5 < 5 := Nat.mod_lt j (by norm_num)
    have hcov := lvl0_coverA hN hφ hc hc2 (j % 5) hj
    rw [angA_mod j]
    exact hcov
  · intro k j u hu
    exact CTA_D1 hcX k j u hu
  · intro k j
    exact CTA_D2 k j

/-- **The chain covering of the `13/33`-cycle.** -/
theorem chainB {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Work.SeedCertRay.Xb.mem c) :
    ∀ k j, Work.SeedCertRay.seg hN (angB j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CTB k j := by
  refine Work.SeedCertRay.chain_sound_sets hN hφ angB angB_succ Work.SeedCertRay.rhoL
    Work.SeedCertRay.rhoL_spec CTB ?_ ?_ ?_
  · intro j
    have hj : j % 5 < 5 := Nat.mod_lt j (by norm_num)
    have hcov := lvl0_coverB hN hφ hc hc2 (j % 5) hj
    rw [angB_mod j]
    exact hcov
  · intro k j u hu
    exact CTB_D1 hcX k j u hu
  · intro k j
    exact CTB_D2 k j

/-! ## The landing points lie in the periodic family -/

theorem boxP_const {l : ℕ} (hl : KT ≤ l) (m : ℕ) (i : Fin NC) :
    boxP l m i = boxP KT m i := by
  simp only [boxP, boxOfP, if_neg (by omega : ¬ l < KT), if_neg (by omega : ¬ KT < KT)]

/-- The union of the chain families from level `KT` on is the periodic family. -/
theorem union_CTA (j : ℕ) : (⋃ l ∈ {l : ℕ | KT ≤ l}, CTA l j) = CTA KT j := by
  refine le_antisymm (iUnion₂_subset fun l hl => ?_) (subset_iUnion₂ (s := fun l _ => CTA l j)
    KT (le_refl KT))
  have hl' : KT ≤ l := hl
  have hbox : boxP l (j % 5) = boxP KT (j % 5) := by
    funext i; exact boxP_const hl' (j % 5) i
  show Work.SeedCertRay.diskUnion (boxP l (j % 5))
    ⊆ Work.SeedCertRay.diskUnion (boxP KT (j % 5))
  rw [hbox]

theorem union_CTB (j : ℕ) : (⋃ l ∈ {l : ℕ | KT ≤ l}, CTB l j) = CTB KT j := by
  refine le_antisymm (iUnion₂_subset fun l hl => ?_) (subset_iUnion₂ (s := fun l _ => CTB l j)
    KT (le_refl KT))
  have hl' : KT ≤ l := hl
  have hbox : boxP l (5 + j % 5) = boxP KT (5 + j % 5) := by
    funext i; exact boxP_const hl' (5 + j % 5) i
  show Work.SeedCertRay.diskUnion (boxP l (5 + j % 5))
    ⊆ Work.SeedCertRay.diskUnion (boxP KT (5 + j % 5))
  rw [hbox]

/-- **The landing point of the `angA j`-ray lies in the periodic family.** -/
theorem landsN_mem_CTA {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hchain : ∀ k j, Work.SeedCertRay.seg hN (angA j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CTA k j)
    {j : ℕ} {y : ℂ} (hy : Work.EL.LandsN hN (angA j) y) : y ∈ CTA KT j := by
  have hclosed : IsClosed (CTA KT j) := Work.SeedCertRay.isClosed_diskUnion _
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
  rw [← union_CTA j]
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

/-- **The landing point of the `angB j`-ray lies in the periodic family.** -/
theorem landsN_mem_CTB {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hchain : ∀ k j, Work.SeedCertRay.seg hN (angB j) (Work.SeedCertRay.rhoL (k + 1))
      (Work.SeedCertRay.rhoL k) ⊆ CTB k j)
    {j : ℕ} {y : ℂ} (hy : Work.EL.LandsN hN (angB j) y) : y ∈ CTB KT j := by
  have hclosed : IsClosed (CTB KT j) := Work.SeedCertRay.isClosed_diskUnion _
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
  rw [← union_CTB j]
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

end Work.SeedPortraitCert
