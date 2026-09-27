import Mathlib
import Submission.Work.EKLC7.LeafNuDefs
import Submission.Work.EKLC7.LeafNuFields
import Submission.Work.EKLC7.LeafNuGood
import Submission.Work.EKLC7.LeafNuMaster
import Submission.Work.EKLC7.LeafNuCondExp
import Submission.Work.EKLComp.U_generated_by_Uball
import Submission.Work.EKLC7.FlowerFamExists
import Submission.Work.EKLComp.LeafAux

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-! ## 1. Elementary bounds -/

theorem orbit_ball_bound (U : Subgroup SL3) {u : SL3} (hu : u ∈ U) :
    ∃ M : ℕ, u ∈ Uball U M ∧ (fun h : SL3 => h * u) '' (Box1 U) ⊆ Uball U M := by
  obtain ⟨n, hn⟩ := blk_mem_of_mem U u hu
  rw [Blk] at hn
  refine ⟨2 + 7 * (n + 2), ?_, ?_⟩
  · refine Uball_mono ?_ hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith
  · rintro g ⟨h, hh, rfl⟩
    have hh2 : h ∈ Uball U (2 : ℝ) := Ucl_subset_Uball (U := U) (r := (1:ℝ)) (r' := (2:ℝ)) (by norm_num) hh
    have hb := Uball_mul (U := U) (a := (2 : ℝ)) (b := (n : ℝ) + 2) (by norm_num) (by positivity)
      h hh2 u hn
    refine Uball_mono ?_ hb
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith

/-! ## 2. Positivity and finiteness of the normalising constants `ddAt` -/

theorem ddAt_ne_zero (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (j : ℕ) (hxZ : x ∈ F.Z j) : F.ddAt j x ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le (h.pos j x hx hxZ (1 / 2) (by norm_num)) ?_)
  exact measure_mono (Set.image_mono (fun g hg =>
    ⟨hg.1, fun i j => le_of_lt (lt_trans (hg.2 i j) (by norm_num))⟩))

theorem ddAt_ne_top (F : FlowerFam U μ) [IsProbabilityMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (j : ℕ) : F.ddAt j x ≠ ⊤ := by
  have h1 : F.ddAt j x ≤ F.kappa j x Set.univ := measure_mono (Set.subset_univ _)
  have h2 : F.kappa j x Set.univ = 1 := by
    simp only [FlowerFam.kappa]
    exact measure_univ
  rw [h2] at h1
  exact ne_of_lt (lt_of_le_of_lt h1 (by norm_num))

/-! ## 3. A set-theoretic identity for the orbit images -/

theorem orbImg_box_mul_right {u : SL3} {x y : X3} (hy : y = u • x) :
    (fun g : SL3 => g • y) '' (Box1 U) =
      (fun g : SL3 => g • x) '' ((fun h : SL3 => h * u) '' (Box1 U)) := by
  subst hy
  ext z; constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * u, ⟨g, hg, rfl⟩, by simp only [mul_smul]⟩
  · rintro ⟨h, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, by simp only [mul_smul]⟩

/-! ## 4. The key identity on a large plaque -/

theorem nu_eq_const_mul_map (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
      y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set X3} (hX' : F.Good X') {x y : X3} (hx : x ∈ X') (hy : y ∈ X')
    {u : SL3} (hu : u ∈ U) (hyx : y = u • x)
    (j : ℕ) (hxE : x ∈ F.E j) (hR2 : (2 : ℝ) ≤ F.R j) (huB : u ∈ Uball U (F.R j))
    (hBu : (fun h : SL3 => h * u) '' (Box1 U) ⊆ Uball U (F.R j))
    {D : Set SL3} (hD : MeasurableSet D) (hDU : D ⊆ (U : Set SL3))
    (hDB : D ⊆ Uball U (F.R j)) :
    F.nu coord X' x D
      = (F.ddAt j y / F.ddAt j x) * ((F.nu coord X' y).map (fun g => g * u)) D := by
  have hZx : x ∈ F.Z j := (F.big j).2.1 hxE
  have hy_atom : y ∈ atom (F.m j) x := by
    rw [hyx]
    exact (F.big j).2.2 x hxE (mem_Upla_iff.mpr ⟨u, huB, rfl⟩)
  have hZy : y ∈ F.Z j := ((F.big j).1.2.2.2 x hZx).1 hy_atom
  have hatom : atom (F.m j) y = atom (F.m j) x := atom_eq_of_mem (F.m j) hy_atom
  have hker : F.kappa j y = F.kappa j x :=
    (Work.EKLComp.kernel_atom_const (μ := μ.restrict (F.Z j)) ⟨F.m j⟩ hy_atom).symm
  have hpropx : ∀ n : ℕ, ProporOn (F.kap n x)
      (ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) x)
      (atom (F.m (F.chose n x)) x ∩ atom (F.m j) x) := fun n =>
    hX'.propor (F.chose n x) j x hx ⟨F.chose_mem_Z hX' hx n, hZx⟩
  have hpropy : ∀ n : ℕ, ProporOn (F.kap n y)
      (ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) y)
      (atom (F.m (F.chose n y)) y ∩ atom (F.m j) y) := fun n =>
    hX'.propor (F.chose n y) j y hy ⟨F.chose_mem_Z hX' hy n, hZy⟩
  have hBx : (fun g : SL3 => g • x) '' (Box1 U) ⊆ atom (F.m j) x := by
    rw [Set.image_subset_iff]
    intro h hh
    exact (F.big j).2.2 x hxE
      (mem_Upla_iff.mpr ⟨h, Uball_mono hR2 (Ucl_subset_Uball (U := U) (r := (1:ℝ)) (r' := (2:ℝ)) (by norm_num) hh), rfl⟩)
  have hDatx : (fun g : SL3 => g • x) '' D ⊆ atom (F.m j) x := by
    rw [Set.image_subset_iff]
    intro d hd
    exact (F.big j).2.2 x hxE (mem_Upla_iff.mpr ⟨d, hDB hd, rfl⟩)
  have hset2 := orbImg_box_mul_right (U := U) (u := u) (x := x) (y := y) hyx
  set D' : Set SL3 := (fun g : SL3 => g * u) ⁻¹' D with hD'def
  have hD'meas : MeasurableSet D' := hD.preimage (measurable_mul_const u)
  have hD'U : D' ⊆ (U : Set SL3) := by
    intro z hz
    have h2 : (z * u) * u⁻¹ ∈ U := U.mul_mem (hDU hz) (U.inv_mem hu)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  have hset1 : (fun g : SL3 => g • y) '' D' = (fun g : SL3 => g • x) '' D := by
    ext z; constructor
    · rintro ⟨g, hg, hgz⟩
      refine ⟨g * u, hg, ?_⟩
      show (g * u) • x = z
      rw [← hgz]
      simp only [mul_smul, hyx]
    · rintro ⟨d, hd, hdz⟩
      refine ⟨d * u⁻¹, ?_, ?_⟩
      · show (d * u⁻¹) * u ∈ D
        rwa [mul_assoc, inv_mul_cancel, mul_one]
      · show (d * u⁻¹) • y = z
        simp only [mul_smul, inv_smul_smul, hyx]
        simpa using hdz
  have hrawx : F.raw coord x D
      = ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) x ((fun g : SL3 => g • x) '' D)
        / F.ddAt j x :=
    F.raw_eq_ratio hU coord hcoordm hcsub hX' hx ⟨F.m j⟩ (F.big j).1 hZx hBx hpropx hD hDU hDatx
  have hrawy : F.raw coord y D'
      = ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) y ((fun g : SL3 => g • y) '' D')
        / F.ddAt j y :=
    F.raw_eq_ratio hU coord hcoordm hcsub hX' hy ⟨F.m j⟩ (F.big j).1 hZy
      (by
        rw [hatom, hset2, Set.image_subset_iff]
        intro a ha
        obtain ⟨g, hg, rfl⟩ := ha
        exact (F.big j).2.2 x hxE (mem_Upla_iff.mpr ⟨g * u, hBu ⟨g, hg, rfl⟩, rfl⟩))
      hpropy hD'meas hD'U
      (by rw [hatom, hset1]; exact hDatx)
  have hAy : ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) y
        ((fun g : SL3 => g • y) '' D')
      = ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) x ((fun g : SL3 => g • x) '' D) := by
    rw [hset1]
    exact congrArg (fun ν : Measure X3 => ν ((fun g : SL3 => g • x) '' D)) hker
  have hmapD : ((F.nu coord X' y).map (fun g => g * u)) D = F.nu coord X' y D' :=
    Measure.map_apply (measurable_mul_const u) hD
  rw [F.nu_of_mem hx, hmapD, F.nu_of_mem hy, hrawx, hrawy, hAy]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [show (F.ddAt j x)⁻¹ * F.ddAt j y * ((F.ddAt j y)⁻¹
        * (ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) x ((fun g : SL3 => g • x) '' D)))
      = (F.ddAt j x)⁻¹ * (F.ddAt j y * (F.ddAt j y)⁻¹)
        * (ProbabilityTheory.condExpKernel (μ.restrict (F.Z j)) (F.m j) x ((fun g : SL3 => g • x) '' D))
      from by ac_rfl]
  rw [ENNReal.mul_inv_cancel (ddAt_ne_zero F hX' hy j hZy) (ddAt_ne_top F hX' hy j), mul_one]


/-! ## 5. The equivariance statement for `F.nu` -/

theorem nu_equivariant {U : Subgroup Work.EKLContract.SL3} {mu : MeasureTheory.Measure Work.EKLContract.X3}
    (F : Work.EKLC7.FlowerFam U mu) [MeasureTheory.IsProbabilityMeasure mu]
    (hU : Work.EKLContract.IsHoro U)
    (coord : Work.EKLContract.X3 → Work.EKLContract.X3 → Work.EKLContract.SL3)
    (hcoordm : Measurable (fun p : Work.EKLContract.X3 × Work.EKLContract.X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u1 ∈ U, ∀ u2 ∈ U, u1 • x = u2 • x → u1 = u2) →
      y ∈ (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3) →
        coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set Work.EKLContract.X3} (hX' : F.Good X') :
    ∀ x ∈ X', ∀ u ∈ U, u • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        F.nu coord X' x = c • (F.nu coord X' (u • x)).map (fun g => g * u) := by
  intro x hx u hu hux
  set y : X3 := u • x with hy_def
  have hy : y ∈ X' := hux
  have hyx : y = u • x := hy_def
  obtain ⟨M, huM, hBuM⟩ := orbit_ball_bound U hu
  have hflower : ∀ n : ℕ, ∃ j : ℕ, x ∈ F.E j ∧ ((n : ℝ) + 2 ≤ F.R j) ∧
      u ∈ Uball U (F.R j) ∧ (fun h : SL3 => h * u) '' (Box1 U) ⊆ Uball U (F.R j) := by
    intro n
    obtain ⟨j, hle, hxE⟩ := hX'.cover (max n M) x hx
    refine ⟨j, hxE, ?_, ?_, ?_⟩
    · have hn : (n : ℝ) ≤ ((max n M : ℕ) : ℝ) := by exact_mod_cast le_max_left n M
      linarith
    · refine Uball_mono ?_ huM
      have hM : (M : ℝ) ≤ ((max n M : ℕ) : ℝ) := by exact_mod_cast le_max_right n M
      linarith
    · refine Set.Subset.trans hBuM (Uball_mono ?_)
      have hM : (M : ℝ) ≤ ((max n M : ℕ) : ℝ) := by exact_mod_cast le_max_right n M
      linarith
  have hBox1meas : MeasurableSet (Box1 U) := measurableSet_Box1 hU.1
  have hBox1U : Box1 U ⊆ (U : Set SL3) := fun g hg => hg.1
  obtain ⟨j0, hj0E, hj0R, hj0u, hj0B⟩ := hflower 0
  have hj0R2 : (2 : ℝ) ≤ F.R j0 := by simpa using hj0R
  have hnormalised : F.nu coord X' x (Box1 U) = 1 := F.normalised hU coord hcoordm hcsub hX' hx
  have hBox1_sub_j0 : Box1 U ⊆ Uball U (F.R j0) :=
    Set.Subset.trans (Ucl_subset_Uball (U := U) (r := (1:ℝ)) (r' := (2:ℝ)) (by norm_num))
      (Uball_mono hj0R2)
  have hBox1_id : F.nu coord X' x (Box1 U)
      = (F.ddAt j0 y / F.ddAt j0 x) * ((F.nu coord X' y).map (fun g => g * u)) (Box1 U) :=
    nu_eq_const_mul_map F hU coord hcoordm hcsub hX' hx hy hu hyx j0 hj0E hj0R2 hj0u hj0B
      hBox1meas hBox1U hBox1_sub_j0
  have hc0T : (F.ddAt j0 y / F.ddAt j0 x) * ((F.nu coord X' y).map (fun g => g * u)) (Box1 U) = 1 := by
    rw [← hBox1_id, hnormalised]
  have hT0 : ((F.nu coord X' y).map (fun g => g * u)) (Box1 U) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hc0T; exact one_ne_zero hc0T.symm
  have hc00 : F.ddAt j0 y / F.ddAt j0 x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc0T; exact one_ne_zero hc0T.symm
  have hc0top : F.ddAt j0 y / F.ddAt j0 x ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hT0] at hc0T; exact ENNReal.one_ne_top hc0T.symm
  have hTtop : ((F.nu coord X' y).map (fun g => g * u)) (Box1 U) ≠ ⊤ := by
    intro hT; rw [hT, ENNReal.mul_top hc00] at hc0T; exact ENNReal.one_ne_top hc0T.symm
  have hconst_eq : ∀ K : ℝ≥0∞, K * ((F.nu coord X' y).map (fun g => g * u)) (Box1 U) = 1 →
      K = F.ddAt j0 y / F.ddAt j0 x := by
    intro K hK
    have h1 : K = (((F.nu coord X' y).map (fun g => g * u)) (Box1 U))⁻¹ := by
      have hcong := congrArg (fun w : ℝ≥0∞ =>
        w * (((F.nu coord X' y).map (fun g => g * u)) (Box1 U))⁻¹) hK
      rw [mul_assoc, ENNReal.mul_inv_cancel hT0 (hTtop), mul_one, one_mul] at hcong
      exact hcong
    have h2 : F.ddAt j0 y / F.ddAt j0 x = (((F.nu coord X' y).map (fun g => g * u)) (Box1 U))⁻¹ := by
      have hcong := congrArg (fun w : ℝ≥0∞ =>
        w * (((F.nu coord X' y).map (fun g => g * u)) (Box1 U))⁻¹) hc0T
      rw [mul_assoc, ENNReal.mul_inv_cancel hT0 (hTtop), mul_one, one_mul] at hcong
      exact hcong
    rw [h1, h2]
  have hstep : ∀ n : ℕ, ∀ D : Set SL3, MeasurableSet D →
      F.nu coord X' x (D ∩ Blk U n)
        = (F.ddAt j0 y / F.ddAt j0 x) * ((F.nu coord X' y).map (fun g => g * u)) (D ∩ Blk U n) := by
    intro n D hD
    obtain ⟨j, hxE, hR, huB, hBu⟩ := hflower n
    have hR2 : (2 : ℝ) ≤ F.R j := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hDBn : D ∩ Blk U n ⊆ Uball U (F.R j) :=
      Set.Subset.trans Set.inter_subset_right (Uball_mono hR)
    have hDUbn : D ∩ Blk U n ⊆ (U : Set SL3) :=
      Set.Subset.trans Set.inter_subset_right (Blk_subset_U U n)
    have hmeas : MeasurableSet (D ∩ Blk U n) := hD.inter (measurableSet_Blk hU.1 n)
    have hmain := nu_eq_const_mul_map F hU coord hcoordm hcsub hX' hx hy hu hyx j hxE hR2 huB hBu
      hmeas hDUbn hDBn
    have hKj : F.ddAt j y / F.ddAt j x = F.ddAt j0 y / F.ddAt j0 x := by
      refine hconst_eq _ ?_
      have hBoxj : Box1 U ⊆ Uball U (F.R j) :=
        Set.Subset.trans (Ucl_subset_Uball (U := U) (r := (1:ℝ)) (r' := (2:ℝ)) (by norm_num))
          (Uball_mono hR2)
      have hid := nu_eq_const_mul_map F hU coord hcoordm hcsub hX' hx hy hu hyx j hxE hR2 huB hBu
        hBox1meas hBox1U hBoxj
      rw [hnormalised] at hid
      exact hid.symm
    rw [hmain, hKj]
  refine ⟨F.ddAt j0 y / F.ddAt j0 x, hc00, hc0top, ?_⟩
  refine Measure.ext fun D hD => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  have hcarriedx : (F.nu coord X' x) ((U : Set SL3)ᶜ) = 0 :=
    F.carried hU coord hcoordm hcsub hX' hx
  have hcarriedy : (F.nu coord X' y) ((U : Set SL3)ᶜ) = 0 :=
    F.carried hU coord hcoordm hcsub hX' hy
  have hcarriedeta : ((F.nu coord X' y).map (fun g => g * u)) ((U : Set SL3)ᶜ) = 0 := by
    rw [Measure.map_apply (measurable_mul_const u) hU.1.measurableSet.compl]
    have hpre : (fun g : SL3 => g * u) ⁻¹' ((U : Set SL3)ᶜ) = (U : Set SL3)ᶜ := by
      ext z; simp only [Set.mem_preimage, Set.mem_compl_iff]
      constructor
      · intro h hz; exact h (U.mul_mem hz hu)
      · intro h hz
        have h2 : (z * u) * u⁻¹ ∈ U := U.mul_mem hz (U.inv_mem hu)
        rw [mul_assoc, mul_inv_cancel, mul_one] at h2
        exact h h2
    rw [hpre, hcarriedy]
  have hcomplx : (F.nu coord X' x) (D ∩ (U : Set SL3)ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hcarriedx
  have hcompleta : ((F.nu coord X' y).map (fun g => g * u)) (D ∩ (U : Set SL3)ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hcarriedeta
  have hmono : Monotone (fun n : ℕ => D ∩ Blk U n) :=
    fun n m hnm => Set.inter_subset_inter (Set.Subset.refl D) (Blk_mono U hnm)
  have hii : (⋃ n, D ∩ Blk U n) = D ∩ (U : Set SL3) := by
    rw [← Set.inter_iUnion, iUnion_Blk]
  have hlimx : (F.nu coord X' x) D = ⨆ n, (F.nu coord X' x) (D ∩ Blk U n) := by
    have hDU0 : (F.nu coord X' x) D = (F.nu coord X' x) (D ∩ (U : Set SL3)) := by
      refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
      calc (F.nu coord X' x) D
            = (F.nu coord X' x) (D ∩ (U : Set SL3) ∪ D ∩ (U : Set SL3)ᶜ) := by
              congr 1
              rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
        _ ≤ (F.nu coord X' x) (D ∩ (U : Set SL3)) + (F.nu coord X' x) (D ∩ (U : Set SL3)ᶜ) :=
              measure_union_le _ _
        _ = (F.nu coord X' x) (D ∩ (U : Set SL3)) := by rw [hcomplx, add_zero]
    rw [hDU0, ← hii]
    exact hmono.measure_iUnion
  have hlima : ((F.nu coord X' y).map (fun g => g * u)) D
      = ⨆ n, ((F.nu coord X' y).map (fun g => g * u)) (D ∩ Blk U n) := by
    have hDU0 : ((F.nu coord X' y).map (fun g => g * u)) D
        = ((F.nu coord X' y).map (fun g => g * u)) (D ∩ (U : Set SL3)) := by
      refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
      calc ((F.nu coord X' y).map (fun g => g * u)) D
            = ((F.nu coord X' y).map (fun g => g * u))
                (D ∩ (U : Set SL3) ∪ D ∩ (U : Set SL3)ᶜ) := by
              congr 1
              rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
        _ ≤ ((F.nu coord X' y).map (fun g => g * u)) (D ∩ (U : Set SL3))
              + ((F.nu coord X' y).map (fun g => g * u)) (D ∩ (U : Set SL3)ᶜ) :=
              measure_union_le _ _
        _ = ((F.nu coord X' y).map (fun g => g * u)) (D ∩ (U : Set SL3)) := by
              rw [hcompleta, add_zero]
    rw [hDU0, ← hii]
    exact hmono.measure_iUnion
  rw [hlimx, hlima, ENNReal.mul_iSup]
  exact iSup_congr fun n => hstep n D hD

end Work.EKLC7
