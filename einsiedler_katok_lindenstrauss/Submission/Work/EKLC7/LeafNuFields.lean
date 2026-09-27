import Mathlib
import Submission.Work.EKLC7.LeafNuGood
import Submission.Work.EKLComp.exists_leafCoord

/-!
# `Work.EKLC7.LeafNuFields` — properties of the patched leafwise measures

We prove the clauses of `Work.EKLContract.IsLeafwise` for the system
`ν = F.nu coord X'` built in `Submission/Work/EKLC7/LeafNuDefs.lean` from a flower family `F`,
on the conull good set `X'` of `Submission/Work/EKLC7/LeafNuGood.lean` (Pisa §6).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

theorem measurableSet_Blk (hcl : IsClosed (U : Set SL3)) (n : ℕ) : MeasurableSet (Blk U n) := by
  rw [Blk, Uball_eq_inter]
  exact hcl.measurableSet.inter (isOpen_UballOpen _).measurableSet

/-- `Blk U 0` is the ball of radius `2` in `U`. -/
theorem blk_zero (U : Subgroup SL3) : Blk U 0 = Uball U 2 := by
  have h : (((0 : ℕ) : ℝ) + 2 : ℝ) = 2 := by norm_num
  rw [Blk, h]

/-- `Ann U 0` is the ball of radius `2` in `U`. -/
theorem ann_zero (U : Subgroup SL3) : Ann U 0 = Uball U 2 := by
  rw [Ann_zero, blk_zero]

theorem measurableSet_Ann (hcl : IsClosed (U : Set SL3)) (n : ℕ) : MeasurableSet (Ann U n) := by
  cases n with
  | zero => rw [Ann_zero]; exact measurableSet_Blk hcl 0
  | succ n => rw [Ann_succ]; exact (measurableSet_Blk hcl _).diff (measurableSet_Blk hcl _)

end Work.EKLC7

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- Trivial stabilisers imply injectivity of the orbit map. -/
theorem free_of_fix {x : X3} (hfree : ∀ u ∈ U, u • x = x → u = 1) :
    ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ h
  have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem h₂) h₁
  have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, h, inv_smul_smul]
  have h1 := hfree _ hmem hfix
  calc u₁ = u₂ * (u₂⁻¹ * u₁) := by group
    _ = u₂ * 1 := by rw [h1]
    _ = u₂ := mul_one u₂

theorem atom_meas (F : FlowerFam U μ) (j : ℕ) (x : X3) :
    MeasurableSet (atom (F.m j) x) :=
  Work.EKLComp.measurableSet_atom_of_countablyGen ⟨F.m j⟩ (F.big j).1.1 (F.big j).1.2.1 x

/-- The atom of a plaque algebra at a point of its domain is contained in the `U`-orbit. -/
theorem atom_subset_orbit (F : FlowerFam U μ) (j : ℕ) {x : X3} (hxZ : x ∈ F.Z j) :
    atom (F.m j) x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
  ((F.big j).1.2.2.2 x hxZ).2.1

/-- Uniqueness of the leaf coordinate on a free orbit: an element of `U` mapping `x` to `y`
coincides with `coord x y`. -/
theorem coord_eq_of_mem {x y : X3} (coord : X3 → X3 → SL3)
    (hcoord : ∀ z ∈ (fun u : SL3 => u • x) '' (U : Set SL3),
      coord x z ∈ U ∧ coord x z • x = z)
    (hfree : ∀ u ∈ U, u • x = x → u = 1) {v : SL3} (hv : v ∈ U) (hvy : v • x = y)
    (hat : y ∈ (fun u : SL3 => u • x) '' (U : Set SL3)) : coord x y = v := by
  have hc := hcoord y hat
  have h1 : (v⁻¹ * coord x y) • x = x := by
    rw [mul_smul, hc.2, ← hvy, inv_smul_smul]
  have h2 : v⁻¹ * coord x y = 1 :=
    hfree _ (U.mul_mem (U.inv_mem hv) hc.1) h1
  calc coord x y = v * (v⁻¹ * coord x y) := by group
    _ = v * 1 := by rw [h2]
    _ = v := mul_one v

theorem kap_compl_atom (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) :
    F.kap n x (atom (F.m (F.chose n x)) x)ᶜ = 0 := by
  have h1 : F.kap n x (atom (F.m (F.chose n x)) x) = 1 :=
    h.atom_one _ x hx (F.chose_mem_Z h hx n)
  have h2 : F.kap n x Set.univ = 1 := by
    simp only [kap]
    exact measure_univ
  rw [MeasureTheory.measure_compl (F.atom_meas _ x) (by rw [h1]; exact ENNReal.one_ne_top),
    h2, h1, tsub_self]

/-- The conditional measure of the chosen flower does not see the difference between two sets
that agree outside the atom. -/
theorem kap_congr (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) {s t : Set X3}
    (h1 : s ⊆ t ∪ (atom (F.m (F.chose n x)) x)ᶜ)
    (h2 : t ⊆ s ∪ (atom (F.m (F.chose n x)) x)ᶜ) :
    F.kap n x s = F.kap n x t := by
  refine le_antisymm ?_ ?_
  · calc F.kap n x s ≤ F.kap n x (t ∪ (atom (F.m (F.chose n x)) x)ᶜ) := measure_mono h1
      _ ≤ F.kap n x t + F.kap n x ((atom (F.m (F.chose n x)) x)ᶜ) := measure_union_le _ _
      _ = F.kap n x t := by rw [F.kap_compl_atom h hx n, add_zero]
  · calc F.kap n x t ≤ F.kap n x (s ∪ (atom (F.m (F.chose n x)) x)ᶜ) := measure_mono h2
      _ ≤ F.kap n x s + F.kap n x ((atom (F.m (F.chose n x)) x)ᶜ) := measure_union_le _ _
      _ = F.kap n x s := by rw [F.kap_compl_atom h hx n, add_zero]

/-- **Transport identity** (Pisa 6.3(iv), the set-theoretic part): for a set `D` of elements of
`U`, the push-forward of the conditional measure along the leaf coordinate is the measure of the
plaque: `(prp n x) D = κ_n (D • x)`. -/
theorem prp_apply (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    {x : X3}
    (hcoord : ∀ y ∈ (fun u : SL3 => u • x) '' (U : Set SL3),
      coord x y ∈ U ∧ coord x y • x = y)
    (hx : x ∈ X') (n : ℕ) {D : Set SL3} (hD : MeasurableSet D)
    (hDU : D ⊆ (U : Set SL3)) :
    F.prp coord n x D = F.kap n x ((fun u : SL3 => u • x) '' D) := by
  have hfix := h.free x hx
  have hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := free_of_fix hfix
  have hm : Measurable (fun y => coord x y) :=
    hcoordm.comp (measurable_const.prodMk measurable_id)
  have hZ : x ∈ F.Z (F.chose n x) := F.chose_mem_Z h hx n
  have hatom : atom (F.m (F.chose n x)) x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
    F.atom_subset_orbit (F.chose n x) hZ
  have hone : F.prp coord n x D = F.kap n x ((coord x) ⁻¹' D) := by
    rw [prp, Measure.map_apply hm hD]
  rw [hone]
  have hkey : F.kap n x ((coord x) ⁻¹' D)
      = F.kap n x ((fun u : SL3 => u • x) '' D) := by
    refine F.kap_congr h hx n ?_ ?_
    · intro y hy
      by_cases ha : y ∈ atom (F.m (F.chose n x)) x
      · obtain ⟨v, hv, hvy⟩ := hatom ha
        have hcv : coord x y = v := coord_eq_of_mem coord hcoord hfix hv hvy ⟨v, hv, hvy⟩
        have hyD : coord x y ∈ D := hy
        have himg : y ∈ (fun u : SL3 => u • x) '' D := by
          refine ⟨coord x y, hyD, ?_⟩
          exact (hcoord y ⟨v, hv, hvy⟩).2
        exact Set.mem_union_left _ himg
      · exact Set.mem_union_right _ ha
    · rintro y ⟨u, huD, rfl⟩
      by_cases ha : u • x ∈ atom (F.m (F.chose n x)) x
      · obtain ⟨v, hv, hvy⟩ := hatom ha
        have hcu : coord x (u • x) = u :=
          coord_eq_of_mem coord hcoord hfix (hDU huD) rfl ⟨v, hv, hvy⟩
        have hmem : (fun u : SL3 => u • x) u ∈ (coord x) ⁻¹' D := by
          show coord x (u • x) ∈ D
          rw [hcu]; exact huD
        exact Set.mem_union_left _ hmem
      · exact Set.mem_union_right _ ha
  rw [hkey]

/-- The push-forward measure gives zero mass to sets of group elements disjoint from `U`. -/
theorem prp_eq_zero (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    {x : X3}
    (hcoord : ∀ y ∈ (fun u : SL3 => u • x) '' (U : Set SL3),
      coord x y ∈ U ∧ coord x y • x = y)
    (hx : x ∈ X') (n : ℕ) {D : Set SL3} (hD : MeasurableSet D)
    (hDU : Disjoint D (U : Set SL3)) : F.prp coord n x D = 0 := by
  have hfix := h.free x hx
  have hm : Measurable (fun y => coord x y) :=
    hcoordm.comp (measurable_const.prodMk measurable_id)
  have hZ : x ∈ F.Z (F.chose n x) := F.chose_mem_Z h hx n
  have hatom : atom (F.m (F.chose n x)) x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
    F.atom_subset_orbit (F.chose n x) hZ
  have hpre : (coord x) ⁻¹' D ⊆ (atom (F.m (F.chose n x)) x)ᶜ := by
    intro y hy ha
    obtain ⟨v, hv, hvy⟩ := hatom ha
    have hcv : coord x y = v :=
      coord_eq_of_mem coord hcoord hfix hv hvy ⟨v, hv, hvy⟩
    have hyD : coord x y ∈ D := hy
    rw [hcv] at hyD
    exact Set.disjoint_left.mp hDU hyD hv
  have hone : F.prp coord n x D = F.kap n x ((coord x) ⁻¹' D) := by
    rw [prp, Measure.map_apply hm hD]
  rw [hone]
  exact measure_mono_null hpre (F.kap_compl_atom h hx n)

end Work.EKLC7.FlowerFam

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3}

/-- A compact subset of `SL₃(ℝ)` intersected with `U` is contained in a ball of `U`. -/
theorem exists_blk_of_isCompact (U : Subgroup SL3) (K : Set SL3) (hK : IsCompact K) :
    ∃ N : ℕ, K ∩ (U : Set SL3) ⊆ Blk U N := by
  classical
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g ∈ K,
      (∑ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) ≤ C := by
    have hcont : ContinuousOn (fun g : SL3 =>
        ∑ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) K := by
      refine Continuous.continuousOn ?_
      fun_prop
    obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
    exact ⟨C, fun g hgK => hC ⟨g, hgK, rfl⟩⟩
  refine ⟨Nat.ceil C + 1, ?_⟩
  rintro g ⟨hgK, hgU⟩
  refine ⟨hgU, fun i j => ?_⟩
  have h1 : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ ∑ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| :=
    Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 =>
      |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (fun p _ => abs_nonneg _)
      (Finset.mem_univ (i, j))
  have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  have h3 := Nat.le_ceil C
  have h4 : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| + 1 := by
    have h := abs_sub_le ((g : Matrix (Fin 3) (Fin 3) ℝ) i j) (0 : ℝ)
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
    rw [sub_zero, zero_sub, abs_neg] at h
    linarith [h2]
  push_cast
  linarith [hC g hgK]

theorem measurableSet_Box1 (hcl : IsClosed (U : Set SL3)) : MeasurableSet (Box1 U) := by
  rw [Box1_eq_Ucl, Ucl]
  rw [show {g : SL3 | g ∈ U ∧ ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}
      = (U : Set SL3) ∩ ⋂ i, ⋂ j, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} from by ext g; simp]
  refine hcl.measurableSet.inter ?_
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  exact measurableSet_Iic.preimage ((by fun_prop : Continuous fun g : SL3 =>
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|)).measurable

end Work.EKLC7

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

variable (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
  (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
  (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
    y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
  {X' : Set X3} (hX' : F.Good X')

include F hU coord hcoordm hcsub hX'

/-- The leaf coordinate restricted to a point of the good set. -/
theorem coord_at {x : X3} (hx : x ∈ X') :
    ∀ y ∈ (fun u : SL3 => u • x) '' (U : Set SL3), coord x y ∈ U ∧ coord x y • x = y :=
  fun y hy => hcsub x y (free_of_fix (hX'.free x hx)) hy

/-- `ν x` is finite on compact sets (Pisa 6.3: the leafwise measures are Radon measures). -/
theorem radon {x : X3} (hx : x ∈ X') : IsFiniteMeasureOnCompacts (F.nu coord X' x) := by
  rw [F.nu_of_mem hx]
  refine ⟨fun K hK => ?_⟩
  obtain ⟨N, hN⟩ := exists_blk_of_isCompact U K hK
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hterm : ∀ n : ℕ, (F.trm coord n x) K ≤ if n ≤ N then (F.dd n x)⁻¹ else 0 := by
    intro n
    by_cases hn : n ≤ N
    · rw [if_pos hn]
      have h1 : (F.trm coord n x) K = (F.dd n x)⁻¹ * ((F.prp coord n x).restrict (Ann U n) K) := by
        rw [trm, Measure.smul_apply, smul_eq_mul]
      rw [h1]
      refine le_trans (mul_le_mul_right ?_ _) (le_of_eq (mul_one _))
      calc (F.prp coord n x).restrict (Ann U n) K ≤ (F.prp coord n x) Set.univ := by
            rw [Measure.restrict_apply hKmeas]
            exact measure_mono (Set.subset_univ _)
        _ = 1 := by
            have hm : Measurable (fun y => coord x y) :=
              hcoordm.comp (measurable_const.prodMk measurable_id)
            rw [prp, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
            haveI : IsProbabilityMeasure (F.kap n x) := by
              rw [kap]; infer_instance
            exact measure_univ
    · have hn' : N + 1 ≤ n := Nat.lt_of_not_le hn
      have hdisj : K ∩ Ann U n = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
        have hy1 : y ∈ Blk U N := hN ⟨hy.1, Ann_subset_U U n hy.2⟩
        have hy2 : y ∈ Blk U (n - 1) := Blk_mono U (by omega) hy1
        exact (Set.disjoint_left.mp (Ann_disjoint_Blk U (by omega : n - 1 < n)) hy.2) hy2
      have h1 : (F.trm coord n x) K = (F.dd n x)⁻¹ * ((F.prp coord n x).restrict (Ann U n) K) := by
        rw [trm, Measure.smul_apply, smul_eq_mul]
      rw [if_neg hn, h1, Measure.restrict_apply hKmeas, hdisj, measure_empty, mul_zero]
  have hsum : (F.raw coord x) K = ∑' n, (F.trm coord n x) K := by
    rw [raw, Measure.sum_apply _ hKmeas]
  rw [hsum]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [if_neg (by omega)])]
  refine ENNReal.sum_lt_top.mpr fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [if_pos (Nat.le_of_lt_succ hn)]
  exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (F.dd_ne_zero hX' hx n))

/-- `ν x` is carried by `U` (Pisa 6.3). -/
theorem carried {x : X3} (hx : x ∈ X') : F.nu coord X' x ((U : Set SL3)ᶜ) = 0 := by
  rw [F.nu_of_mem hx]
  show (Measure.sum (fun n => F.trm coord n x)) ((U : Set SL3)ᶜ) = 0
  rw [Measure.sum_apply _ hU.1.measurableSet.compl]
  refine ENNReal.tsum_eq_zero.mpr fun n => ?_
  have hmeas : MeasurableSet (Ann U n) := Work.EKLC7.measurableSet_Ann hU.1 n
  have h1 : F.trm coord n x ((U : Set SL3)ᶜ)
      = (F.dd n x)⁻¹ * ((F.prp coord n x).restrict (Ann U n) ((U : Set SL3)ᶜ)) := by
    rw [trm, Measure.smul_apply, smul_eq_mul]
  rw [h1, Measure.restrict_apply hU.1.measurableSet.compl]
  have hdisj : Disjoint ((U : Set SL3)ᶜ ∩ Ann U n) (U : Set SL3) :=
    Set.disjoint_left.mpr fun y hy => hy.1
  rw [F.prp_eq_zero hX' coord hcoordm (F.coord_at hU coord hcoordm hcsub hX' hx) hx n
    (hU.1.measurableSet.compl.inter hmeas) hdisj, mul_zero]

/-- `ν x` is normalised by the set `B₁ᵁ` (Pisa 6.3). -/
theorem normalised {x : X3} (hx : x ∈ X') : F.nu coord X' x (Box1 U) = 1 := by
  rw [F.nu_of_mem hx]
  show (Measure.sum (fun n => F.trm coord n x)) (Box1 U) = 1
  have hBmeas : MeasurableSet (Box1 U) := Work.EKLC7.measurableSet_Box1 hU.1
  rw [Measure.sum_apply _ hBmeas, tsum_eq_single 0]
  · have h1 : F.trm coord 0 x (Box1 U)
        = (F.dd 0 x)⁻¹ * ((F.prp coord 0 x).restrict (Ann U 0) (Box1 U)) := by
      rw [trm, Measure.smul_apply, smul_eq_mul]
    rw [h1, Measure.restrict_apply hBmeas, Set.inter_eq_left.mpr (box1_subset_Ann_zero U),
      F.prp_apply hX' coord hcoordm (F.coord_at hU coord hcoordm hcsub hX' hx) hx 0 hBmeas
        (fun g hg => hg.1), F.dd_eq_ddAt]
    exact ENNReal.inv_mul_cancel (F.dd_ne_zero hX' hx 0) (F.dd_ne_top hX' hx 0)
  · intro n hn
    have hmeas : MeasurableSet (Ann U n) := Work.EKLC7.measurableSet_Ann hU.1 n
    have h1 : F.trm coord n x (Box1 U)
        = (F.dd n x)⁻¹ * ((F.prp coord n x).restrict (Ann U n) (Box1 U)) := by
      rw [trm, Measure.smul_apply, smul_eq_mul]
    rw [h1, Measure.restrict_apply hBmeas]
    have hempty : Box1 U ∩ Ann U n = ∅ := by
      rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
      exact Set.disjoint_iff_inter_eq_empty.mp (box1_disjoint_Ann_succ U m)
    rw [hempty, measure_empty, mul_zero]

/-- The identity is in the support of `ν x` (Pisa 6.3(v)). -/
theorem pos {x : X3} (hx : x ∈ X') {δ : ℝ} (hδ : 0 < δ) :
    0 < F.nu coord X' x (V δ) := by
  set q : ℝ := min (δ / 2) (1 / 2) with hq_def
  have hq : 0 < q := lt_min (by linarith) (by norm_num)
  have hqδ : q < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hq2 : q ≤ 2 := by
    rw [hq_def]
    have := min_le_right (δ / 2) (1 / 2)
    linarith
  have hsub : Uball U q ⊆ V δ := fun g hg i j => lt_trans (hg.2 i j) hqδ
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [F.nu_of_mem hx]
  show 0 < (Measure.sum (fun n => F.trm coord n x)) (Uball U q)
  have hBmeas : MeasurableSet (Uball U q) := by
    rw [Uball_eq_inter]
    exact hU.1.measurableSet.inter (isOpen_UballOpen q).measurableSet
  rw [Measure.sum_apply _ hBmeas, tsum_eq_single 0]
  · have h1 : F.trm coord 0 x (Uball U q)
        = (F.dd 0 x)⁻¹ * ((F.prp coord 0 x).restrict (Ann U 0) (Uball U q)) := by
      rw [trm, Measure.smul_apply, smul_eq_mul]
    rw [h1, Measure.restrict_apply hBmeas]
    have hinter : Uball U q ∩ Ann U 0 = Uball U q := by
      rw [Work.EKLC7.ann_zero]
      exact Set.inter_eq_left.mpr fun g hg => Uball_mono hq2 hg
    rw [hinter,
      F.prp_apply hX' coord hcoordm (F.coord_at hU coord hcoordm hcsub hX' hx) hx 0 hBmeas
        (fun g hg => hg.1)]
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (F.dd_ne_top hX' hx 0)) ?_
    rw [F.kap_eq_kappa]
    exact ne_of_gt (hX'.pos _ x hx (F.chose_mem_Z hX' hx 0) q hq)
  · intro n hn
    have hmeas : MeasurableSet (Ann U n) := Work.EKLC7.measurableSet_Ann hU.1 n
    have h1 : F.trm coord n x (Uball U q)
        = (F.dd n x)⁻¹ * ((F.prp coord n x).restrict (Ann U n) (Uball U q)) := by
      rw [trm, Measure.smul_apply, smul_eq_mul]
    rw [h1, Measure.restrict_apply hBmeas]
    have hempty : Uball U q ∩ Ann U n = ∅ := by
      rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
      rw [Ann_succ]
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      exact hy.2.2 (Blk_mono U (Nat.zero_le m) (by
        rw [Work.EKLC7.blk_zero]; exact Uball_mono hq2 hy.1))
    rw [hempty, measure_empty, mul_zero]

end Work.EKLC7.FlowerFam
