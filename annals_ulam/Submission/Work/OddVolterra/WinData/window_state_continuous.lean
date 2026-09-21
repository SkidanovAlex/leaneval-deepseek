import Mathlib
import Submission.Work.OddVolterra.WinData.Specs
import Submission.Work.OddVolterra.WinData.window_solution_accurate
import Submission.Work.OddVolterra.WinData.LowClamp
import Submission.Work.OddVolterra.WinData.LowSource
import Submission.Work.OddVolterra.WinData.LowData
import Submission.Work.OddVolterra.WinData.frozen_tail_close_low
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.WinData.manifest_locality_low
import Submission.Work.OddCurveB.Engine.volterra_long_exists_ball
import Submission.Work.OddCurveB.Est.exists_linearization
import Submission.Work.OddVolterra.Window.volterra_unique
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.WinData.deriv_row_of_identity
import Submission.Work.OddVolterra.WinData.lc_low_piece

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-! ## Helpers -/

lemma integral_apply_zero {f : ℝ → St} {a b : ℝ} (hi : IntervalIntegrable f volume a b) :
    (∫ σ in a..b, f σ) 0 = ∫ σ in a..b, (f σ) 0 := by
  have hcc := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (ContinuousLinearMap.proj (0 : Fin 4)) hi
  simpa [ContinuousLinearMap.proj_apply] using hcc.symm

lemma integral_apply_one {f : ℝ → St} {a b : ℝ} (hi : IntervalIntegrable f volume a b) :
    (∫ σ in a..b, f σ) 1 = ∫ σ in a..b, (f σ) 1 := by
  have hcc := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (ContinuousLinearMap.proj (1 : Fin 4)) hi
  simpa [ContinuousLinearMap.proj_apply] using hcc.symm

lemma theta_intervalIntegrable (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s a b : ℝ} (hs : (1 / 4 : ℝ) ≤ s) (hs1 : s ≤ 1) (hsa : s ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {Z : ℝ → St} (hZc : ContinuousOn Z (Set.Icc a b))
    (hZb : ∀ σ ∈ Set.Icc a b, ‖Z σ - baseState σ‖ ≤ 1 / 2) :
    IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume a b := by
  obtain ⟨L, hL, C, hC, hLip, hBd, hCont⟩ :=
    Existence.theta_lipschitz_state_ball n hn hh hsupp hsmall2 (b := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
  have hsb : s ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨hs, hs1⟩
  have hopen : ContinuousOn (fun σ : ℝ => Theta n h s σ (Z σ)) (Set.Ioo a b) := by
    refine ContinuousOn.comp (g := fun p : ℝ × St => Theta n h s p.1 p.2)
      (f := fun σ : ℝ => (σ, Z σ)) (hCont s hsb) ?_ ?_
    · intro σ hσ
      refine ContinuousWithinAt.prodMk continuousWithinAt_id ?_
      exact (hZc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).continuousWithinAt hσ
    · intro σ hσ
      exact ⟨⟨lt_of_le_of_lt hsa hσ.1, lt_of_lt_of_le hσ.2 hb⟩, hZb σ ⟨hσ.1.le, hσ.2.le⟩⟩
  have hmeas_open : AEStronglyMeasurable (fun σ : ℝ => Theta n h s σ (Z σ))
      (volume.restrict (Set.Ioo a b)) :=
    hopen.aestronglyMeasurable isOpen_Ioo.measurableSet
  have hset : Set.Ioo a b =ᵐ[(volume : Measure ℝ)] Set.Ioc a b := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hempty : Set.Ioo a b \ Set.Ioc a b = ∅ := by
        rw [Set.sdiff_eq_empty.mpr]
        intro x hx
        exact ⟨hx.1, hx.2.le⟩
      rw [hempty]
      exact measure_empty
    · refine measure_mono_null (t := ({b} : Set ℝ)) ?_ (Real.volume_singleton (a := b))
      intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hxb
      exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hxb⟩
  have hmeas : AEStronglyMeasurable (fun σ : ℝ => Theta n h s σ (Z σ))
      (volume.restrict (Set.Ioc a b)) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact hmeas_open
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Ioc a b)),
      ‖Theta n h s σ (Z σ)‖ ≤ max C 0 := by
    have hbad : (volume : Measure ℝ)
        {σ : ℝ | σ ∈ Set.Ioc a b ∧ ¬ (‖Theta n h s σ (Z σ)‖ ≤ max C 0)} = 0 := by
      refine measure_mono_null (t := ({b} : Set ℝ)) ?_ (Real.volume_singleton (a := b))
      intro σ hσ
      rw [Set.mem_singleton_iff]
      by_contra hσb
      refine hσ.2 (le_trans (hBd s hsb σ
        ⟨lt_of_le_of_lt hsa hσ.1.1, lt_of_lt_of_le (lt_of_le_of_ne hσ.1.2 hσb) hb⟩ (Z σ) ?_)
        (le_max_left _ _))
      rw [Metric.mem_closedBall]
      exact hZb σ ⟨hσ.1.1.le, hσ.1.2⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hbad
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact Classical.not_imp.mp hx
  refine intervalIntegrable_iff.mpr ?_
  rw [Set.uIoc_of_le hab]
  exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas (max C 0) hbound

theorem window_state_continuous (n : ℕ) (hn : 1 ≤ n)
    (hL1 : Work.OddVolterra.WinData.ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ))
    (hL4 : Work.OddVolterra.WinData.FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ)) :
    ∀ ρ : ℝ, 0 < ρ → ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η₀ → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1) ∧
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) ∧
        (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) ∧
        (∀ s ∈ Set.Icc (1 / 4 : ℝ) 1, dist (Z s) (Work.OddVolterra.baseState s) ≤ ρ) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) := by
  intro ρ hρ
  -- the closeness demanded of the two pieces
  obtain ⟨ν, hνpos, hν100, hνρ⟩ : ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1 / 100 ∧ ν ≤ ρ :=
    ⟨min ρ (1 / 100), lt_min hρ (by norm_num), min_le_right _ _, min_le_left _ _⟩
  -- the low piece
  obtain ⟨εl, hεlpos, hεl100, θ, hθpos, hθhalf, Hl⟩ := lc_low_piece n hn ν hνpos hν100 hL1 hL4
  have hηpos : 0 < min ν θ := lt_min hνpos hθpos
  have hην : min ν θ ≤ ν := min_le_left _ _
  have hηθ : min ν θ ≤ θ := min_le_right _ _
  -- the middle piece
  obtain ⟨εm, hεmpos, Hm⟩ := window_solution_accurate n hn (min ν θ) hηpos
  refine ⟨min (min εm εl) (1 / 100), lt_min (lt_min hεmpos hεlpos) (by norm_num), ?_⟩
  intro h hh hsupp hflat hsmall h0 hne
  have hsmall_m : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εm :=
    fun k hk s => le_trans (hsmall k hk s) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hsmall_l : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εl :=
    fun k hk s => le_trans (hsmall k hk s) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hsmall100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hsmall k hk s) (min_le_right _ _)
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall100 k (by omega) s
  obtain ⟨ZM, hZMc, hZMeq, hZMtail, hZMd⟩ := Hm h hh hsupp hflat hsmall_m h0 hne
  have hZMdθ : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (ZM s) (baseState s) ≤ θ :=
    fun s hs => le_trans (hZMd s hs) hηθ
  obtain ⟨ZL, hZLc, hZLeq, hZLd⟩ :=
    Hl h hh hsupp hflat hsmall_l h0 hne ZM hZMc hZMeq hZMtail hZMdθ
  -- the two pieces agree at `7/10`, by injectivity of `Godd` on the state ball
  have hglue : ZL (7 / 10) = ZM (7 / 10) := by
    obtain ⟨c, hc, hInj⟩ :=
      Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsmall2
        (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
    have hμ : (7 / 10 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (7 / 10) := ⟨by norm_num, le_rfl⟩
    have hM70 : (7 / 10 : ℝ) ∈ Set.Icc (7 / 10 : ℝ) (9 / 10) := ⟨le_rfl, by norm_num⟩
    have hM71 : (7 / 10 : ℝ) ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hL70 := hZLeq (7 / 10) hμ
    have hM70e := hZMeq (7 / 10) hM70
    rw [intervalIntegral.integral_same, zero_add] at hL70
    have heq : Godd n h (7 / 10) (ZL (7 / 10)) = Godd n h (7 / 10) (ZM (7 / 10)) := by
      rw [hL70, hM70e]
    have hb1 : ZL (7 / 10) ∈ Metric.closedBall (baseState (7 / 10)) (1 / 2) := by
      rw [Metric.mem_closedBall]
      exact le_trans (hZLd (7 / 10) hμ) (le_trans hν100 (by norm_num))
    have hb2 : ZM (7 / 10) ∈ Metric.closedBall (baseState (7 / 10)) (1 / 2) := by
      rw [Metric.mem_closedBall]
      exact le_trans (le_trans (hZMd (7 / 10) hM71) hηθ) hθhalf
    have h3 := hInj (7 / 10) ⟨by norm_num, by norm_num⟩ (ZL (7 / 10)) hb1 (ZM (7 / 10)) hb2
    rw [heq, sub_self, norm_zero] at h3
    have h4 : ‖ZL (7 / 10) - ZM (7 / 10)‖ = 0 :=
      le_antisymm (by nlinarith [hc, norm_nonneg (ZL (7 / 10) - ZM (7 / 10)), h3]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  -- the compound curve on `[1/4,1]`
  let Zc : ℝ → St := fun u => if u ≤ (7 / 10 : ℝ) then ZL u else ZM u
  have hZcL : ∀ u : ℝ, u ≤ (7 / 10 : ℝ) → Zc u = ZL u := fun u hu => by
    show (if u ≤ (7 / 10 : ℝ) then ZL u else ZM u) = ZL u
    rw [if_pos hu]
  have hZcM : ∀ u : ℝ, (7 / 10 : ℝ) < u → Zc u = ZM u := fun u hu => by
    show (if u ≤ (7 / 10 : ℝ) then ZL u else ZM u) = ZM u
    rw [if_neg (not_le.mpr hu)]
  have hZc70 : Zc (7 / 10) = ZL (7 / 10) := hZcL _ le_rfl
  have hZc70M : Zc (7 / 10) = ZM (7 / 10) := by rw [hZc70, hglue]
  have hZcc : ContinuousOn Zc (Set.Icc (1 / 4 : ℝ) 1) := by
    have h1 : ContinuousOn Zc (Set.Icc (1 / 4 : ℝ) (7 / 10)) :=
      hZLc.congr (fun u hu => hZcL u hu.2)
    have h2 : ContinuousOn Zc (Set.Icc (7 / 10 : ℝ) 1) :=
      hZMc.congr (fun u hu => by
        rcases lt_or_eq_of_le hu.1 with hlt | heq
        · exact hZcM u hlt
        · rw [← heq]; exact hZc70M)
    have hu := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by norm_num : (1 / 4 : ℝ) ≤ 7 / 10)
      (by norm_num : (7 / 10 : ℝ) ≤ 1)] at hu
  have hZcb : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1, ‖Zc s - baseState s‖ ≤ 1 / 2 := by
    intro s hs
    rw [← dist_eq_norm]
    rcases le_or_gt s (7 / 10) with hlt | hgt
    · rw [hZcL s hlt]
      exact le_trans (hZLd s ⟨hs.1, hlt⟩) (by linarith)
    · rw [hZcM s hgt]
      exact le_trans (hZMd s ⟨le_of_lt hgt, hs.2⟩) (le_trans hηθ hθhalf)
  -- the equation satisfied by `Zc`
  have hZc_eq_Icc : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (9 / 10),
      Godd n h s (Zc s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zc σ)) + Xi n h s := by
    intro s hs
    rcases le_or_gt s (7 / 10) with hs7 | hs7
    · -- the low piece
      have hL := hZLeq s ⟨hs.1, hs7⟩
      have hZs : Zc s = ZL s := hZcL s hs7
      have hZc_l : ContinuousOn Zc (Set.Icc s (7 / 10)) :=
        hZcc.mono (Set.Icc_subset_Icc hs.1 (by norm_num))
      have hZc_r : ContinuousOn Zc (Set.Icc (7 / 10 : ℝ) 1) :=
        hZcc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
      have i1 : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zc σ)) volume s (7 / 10) :=
        theta_intervalIntegrable n hn hh hsupp hsmall2 hs.1 (le_trans hs7 (by norm_num)) le_rfl hs7
          (by norm_num) hZc_l (fun σ hσ => hZcb σ ⟨le_trans hs.1 hσ.1, by linarith [hσ.2]⟩)
      have i2 : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zc σ)) volume (7 / 10) 1 :=
        theta_intervalIntegrable n hn hh hsupp hsmall2 hs.1 (le_trans hs7 (by norm_num)) hs7
          (by norm_num) le_rfl hZc_r (fun σ hσ => hZcb σ ⟨by linarith [hσ.1], hσ.2⟩)
      have hsplit := (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
      have hseg1 : (∫ σ in s..(7 / 10), Theta n h s σ (Zc σ))
          = ∫ σ in s..(7 / 10), Theta n h s σ (ZL σ) :=
        intervalIntegral.integral_congr (fun σ hσ => by
          rw [Set.uIcc_of_le hs7] at hσ
          rw [hZcL σ hσ.2])
      have hseg2 : (∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Theta n h s σ (Zc σ))
          = ∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Theta n h s σ (ZM σ) :=
        intervalIntegral.integral_congr (fun σ hσ => by
          rw [Set.uIcc_of_le (by norm_num : (7 / 10 : ℝ) ≤ 1)] at hσ
          rcases lt_or_eq_of_le hσ.1 with hlt | heq
          · rw [hZcM σ hlt]
          · rw [← heq, hZc70M])
      rw [hZs, hL, hsplit, hseg1, hseg2]
    · -- the middle piece
      have hZs : Zc s = ZM s := hZcM s hs7
      have hseg : (∫ σ in s..(1 : ℝ), Theta n h s σ (Zc σ))
          = ∫ σ in s..(1 : ℝ), Theta n h s σ (ZM σ) :=
        intervalIntegral.integral_congr (fun σ hσ => by
          rw [Set.uIcc_of_le (le_trans hs.2 (by norm_num))] at hσ
          rw [hZcM σ (by linarith [hσ.1])])
      rw [hZs, hZMeq s ⟨le_of_lt hs7, hs.2⟩, hseg]
  have hZc_eq_tail : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) 1,
      Godd n h s (Zc s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zc σ)) + Xi n h s := by
    intro s hs
    have h9 : (1 : ℝ) - tau = 9 / 10 := by norm_num [tau]
    have hbase := Window.base_volterra_right n hn hsupp (s := s) (by rw [h9]; exact hs.1) hs.2
    have hs70 : (7 / 10 : ℝ) < s := by linarith [hs.1]
    have hs9 : (9 / 10 : ℝ) ≤ s := le_of_lt hs.1
    have hZs : Zc s = baseState s := by
      rw [hZcM s hs70, hZMtail s hs9]
    have hseg : (∫ σ in s..(1 : ℝ), Theta n h s σ (Zc σ))
        = ∫ σ in s..(1 : ℝ), Theta n h s σ (baseState σ) :=
      intervalIntegral.integral_congr (fun σ hσ => by
        rw [Set.uIcc_of_le hs.2.le] at hσ
        have hσ70 : (7 / 10 : ℝ) < σ := by linarith [hσ.1, hs.1]
        have hσ9 : (9 / 10 : ℝ) ≤ σ := by linarith [hσ.1]
        rw [hZcM σ hσ70, hZMtail σ hσ9])
    rw [hZs, hbase, hseg]
  -- the curve of the answer, extended below `1/4`
  let Z₂ : ℝ → ℝ := fun u => if u < (1 / 4 : ℝ) then Zc (1 / 4) 2 else Zc u 2
  let Z₃ : ℝ → ℝ := fun u => if u < (1 / 4 : ℝ) then Zc (1 / 4) 3 else Zc u 3
  let Zf0 : ℝ → ℝ := fun u =>
    if u < (1 / 4 : ℝ) then Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₂ σ else Zc u 0
  let Zf1 : ℝ → ℝ := fun u =>
    if u < (1 / 4 : ℝ) then Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₃ σ else Zc u 1
  let Z : ℝ → St := fun u => ![Zf0 u, Zf1 u, Z₂ u, Z₃ u]
  have hZ_Zc : ∀ u : ℝ, (1 / 4 : ℝ) ≤ u → Z u = Zc u := by
    intro u hu
    funext i
    fin_cases i
    · show (if u < (1 / 4 : ℝ) then
          Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₂ σ else Zc u 0) = Zc u 0
      rw [if_neg (not_lt.mpr hu)]
    · show (if u < (1 / 4 : ℝ) then
          Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₃ σ else Zc u 1) = Zc u 1
      rw [if_neg (not_lt.mpr hu)]
    · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 2 else Zc u 2) = Zc u 2
      rw [if_neg (not_lt.mpr hu)]
    · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 3 else Zc u 3) = Zc u 3
      rw [if_neg (not_lt.mpr hu)]
  have hZ_2 : ∀ u : ℝ, (Z u) 2 = Z₂ u := fun u => by simp [Z]
  have hZ_3 : ∀ u : ℝ, (Z u) 3 = Z₃ u := fun u => by simp [Z]
  have hZ_0 : ∀ u : ℝ, (Z u) 0 = Zf0 u := fun u => by simp [Z]
  have hZ_1 : ∀ u : ℝ, (Z u) 1 = Zf1 u := fun u => by simp [Z]
  have hZf0_lt : ∀ u : ℝ, u < (1 / 4 : ℝ) →
      (Z u) 0 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₂ σ := by
    intro u hu
    rw [hZ_0 u]
    show (if u < (1 / 4 : ℝ) then
      Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₂ σ else Zc u 0) = _
    rw [if_pos hu]
  have hZf1_lt : ∀ u : ℝ, u < (1 / 4 : ℝ) →
      (Z u) 1 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₃ σ := by
    intro u hu
    rw [hZ_1 u]
    show (if u < (1 / 4 : ℝ) then
      Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z₃ σ else Zc u 1) = _
    rw [if_pos hu]
  -- continuity of the two new components near `[1/4,1)`
  have hZ₂_cont : ContinuousOn (fun u : ℝ => Z u 2) (Set.Ioo (1 / 4 - 1 / 8) 1) := by
    have hconst : ContinuousOn Z₂ (Set.Icc (1 / 4 - 1 / 8) (1 / 4)) :=
      continuousOn_const.congr (fun u hu => by
        rcases lt_or_eq_of_le hu.2 with hlt | heq
        · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 2 else Zc u 2) = Zc (1 / 4) 2
          rw [if_pos hlt]
        · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 2 else Zc u 2) = Zc (1 / 4) 2
          rw [heq, if_neg (lt_irrefl _)])
    have htail : ContinuousOn Z₂ (Set.Icc (1 / 4 : ℝ) 1) :=
      ((continuous_apply (2 : Fin 4)).comp_continuousOn hZcc).congr (fun u hu => by
        show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 2 else Zc u 2) = Zc u 2
        rw [if_neg (not_lt.mpr hu.1)])
    have hu := hconst.union_of_isClosed htail isClosed_Icc isClosed_Icc
    rw [Set.Icc_union_Icc_eq_Icc (by norm_num : (1 / 4 - 1 / 8 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)] at hu
    exact (hu.mono (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)).congr (fun u _ => hZ_2 u)
  have hZ₃_cont : ContinuousOn (fun u : ℝ => Z u 3) (Set.Ioo (1 / 4 - 1 / 8) 1) := by
    have hconst : ContinuousOn Z₃ (Set.Icc (1 / 4 - 1 / 8) (1 / 4)) :=
      continuousOn_const.congr (fun u hu => by
        rcases lt_or_eq_of_le hu.2 with hlt | heq
        · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 3 else Zc u 3) = Zc (1 / 4) 3
          rw [if_pos hlt]
        · show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 3 else Zc u 3) = Zc (1 / 4) 3
          rw [heq, if_neg (lt_irrefl _)])
    have htail : ContinuousOn Z₃ (Set.Icc (1 / 4 : ℝ) 1) :=
      ((continuous_apply (3 : Fin 4)).comp_continuousOn hZcc).congr (fun u hu => by
        show (if u < (1 / 4 : ℝ) then Zc (1 / 4) 3 else Zc u 3) = Zc u 3
        rw [if_neg (not_lt.mpr hu.1)])
    have hu := hconst.union_of_isClosed htail isClosed_Icc isClosed_Icc
    rw [Set.Icc_union_Icc_eq_Icc (by norm_num : (1 / 4 - 1 / 8 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)] at hu
    exact (hu.mono (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)).congr (fun u _ => hZ_3 u)
  -- the row identities
  have hident0 : ∀ u : ℝ, u < 1 →
      (Z u) 0 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ 2 := by
    intro u hu
    rcases lt_or_ge u (1 / 4) with hlt | hge
    · rw [hZf0_lt u hlt]
      rw [show (∫ σ in u..(1 : ℝ), Z₂ σ) = ∫ σ in u..(1 : ℝ), Z σ 2 from
        intervalIntegral.integral_congr (fun σ _ => (hZ_2 σ).symm)]
    · have hZs : Z u = Zc u := hZ_Zc u hge
      have heq : Godd n h u (Zc u) = (∫ σ in u..(1 : ℝ), Theta n h u σ (Zc σ)) + Xi n h u := by
        rcases le_or_gt u (9 / 10) with h9 | h9
        · exact hZc_eq_Icc u ⟨hge, h9⟩
        · exact hZc_eq_tail u ⟨h9, hu⟩
      have hint : IntervalIntegrable (fun σ : ℝ => Theta n h u σ (Zc σ)) volume u 1 :=
        theta_intervalIntegrable n hn hh hsupp hsmall2 hge hu.le le_rfl hu.le le_rfl
          (hZcc.mono (Set.Icc_subset_Icc hge le_rfl))
          (fun σ hσ => hZcb σ ⟨le_trans hge hσ.1, hσ.2⟩)
      have hrow : (Zc u) 0
          = (∫ σ in u..(1 : ℝ), (Theta n h u σ (Zc σ)) 0) + Commons.Geometry.Ulam.profileX 1 := by
        have h := congrFun heq 0
        rw [Pi.add_apply, integral_apply_zero hint] at h
        simpa [Godd, Xi] using h
      have hrow' : (Zc u) 0
          = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), (Zc σ) 2 := by
        rw [hrow]
        have h2 : (∫ σ in u..(1 : ℝ), (Theta n h u σ (Zc σ)) 0)
            = ∫ σ in u..(1 : ℝ), -((Zc σ) 2) :=
          intervalIntegral.integral_congr (fun σ _ => by simp [Theta])
        rw [h2, intervalIntegral.integral_neg]
        ring
      rw [hZs, hrow']
      rw [show (∫ σ in u..(1 : ℝ), (Zc σ) 2) = ∫ σ in u..(1 : ℝ), Z σ 2 from
        intervalIntegral.integral_congr (fun σ hσ => by
          rw [Set.uIcc_of_le hu.le] at hσ
          exact (congrArg (fun w : St => w 2) (hZ_Zc σ (le_trans hge hσ.1))).symm)]
  have hident1 : ∀ u : ℝ, u < 1 →
      (Z u) 1 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ 3 := by
    intro u hu
    rcases lt_or_ge u (1 / 4) with hlt | hge
    · rw [hZf1_lt u hlt]
      rw [show (∫ σ in u..(1 : ℝ), Z₃ σ) = ∫ σ in u..(1 : ℝ), Z σ 3 from
        intervalIntegral.integral_congr (fun σ _ => (hZ_3 σ).symm)]
    · have hZs : Z u = Zc u := hZ_Zc u hge
      have heq : Godd n h u (Zc u) = (∫ σ in u..(1 : ℝ), Theta n h u σ (Zc σ)) + Xi n h u := by
        rcases le_or_gt u (9 / 10) with h9 | h9
        · exact hZc_eq_Icc u ⟨hge, h9⟩
        · exact hZc_eq_tail u ⟨h9, hu⟩
      have hint : IntervalIntegrable (fun σ : ℝ => Theta n h u σ (Zc σ)) volume u 1 :=
        theta_intervalIntegrable n hn hh hsupp hsmall2 hge hu.le le_rfl hu.le le_rfl
          (hZcc.mono (Set.Icc_subset_Icc hge le_rfl))
          (fun σ hσ => hZcb σ ⟨le_trans hge hσ.1, hσ.2⟩)
      have hrow : (Zc u) 1
          = (∫ σ in u..(1 : ℝ), (Theta n h u σ (Zc σ)) 1) + Commons.Geometry.Ulam.profileX 1 := by
        have h := congrFun heq 1
        rw [Pi.add_apply, integral_apply_one hint] at h
        simpa [Godd, Xi] using h
      have hrow' : (Zc u) 1
          = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), (Zc σ) 3 := by
        rw [hrow]
        have h2 : (∫ σ in u..(1 : ℝ), (Theta n h u σ (Zc σ)) 1)
            = ∫ σ in u..(1 : ℝ), -((Zc σ) 3) :=
          intervalIntegral.integral_congr (fun σ _ => by simp [Theta])
        rw [h2, intervalIntegral.integral_neg]
        ring
      rw [hZs, hrow']
      rw [show (∫ σ in u..(1 : ℝ), (Zc σ) 3) = ∫ σ in u..(1 : ℝ), Z σ 3 from
        intervalIntegral.integral_congr (fun σ hσ => by
          rw [Set.uIcc_of_le hu.le] at hσ
          exact (congrArg (fun w : St => w 3) (hZ_Zc σ (le_trans hge hσ.1))).symm)]
  -- the derivative rows
  have hrows : ∀ s : ℝ, 1 / 4 ≤ s →
      deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3 := by
    intro s hs
    rcases le_or_gt s (9 / 10) with hs9 | hs9
    · have hs1 : s < 1 := by linarith
      have hsmem : s ∈ Set.Ioo (1 / 4 - 1 / 8) 1 := ⟨by linarith, hs1⟩
      have hev0 : ∀ᶠ u in 𝓝 s,
          Z u 0 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ 2 :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hs1) (fun u hu => hident0 u hu)
      have hev1 : ∀ᶠ u in 𝓝 s,
          Z u 1 = Commons.Geometry.Ulam.profileX 1 - ∫ σ in u..(1 : ℝ), Z σ 3 :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hs1) (fun u hu => hident1 u hu)
      have hcont2 : ContinuousAt (fun σ : ℝ => Z σ 2) s :=
        hZ₂_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
      have hcont3 : ContinuousAt (fun σ : ℝ => Z σ 3) s :=
        hZ₃_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
      have hmeas2 : StronglyMeasurableAtFilter (fun σ : ℝ => Z σ 2) (𝓝 s) volume :=
        hZ₂_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
      have hmeas3 : StronglyMeasurableAtFilter (fun σ : ℝ => Z σ 3) (𝓝 s) volume :=
        hZ₃_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
      have hint2 : IntervalIntegrable (fun σ : ℝ => Z σ 2) volume s 1 := by
        have hc : ContinuousOn (fun σ : ℝ => Zc σ 2) (Set.Icc s 1) :=
          (continuous_apply (2 : Fin 4)).comp_continuousOn
            (hZcc.mono (Set.Icc_subset_Icc hs le_rfl))
        have hc' : ContinuousOn (fun σ : ℝ => Z σ 2) (Set.uIcc s 1) := by
          rw [Set.uIcc_of_le (by linarith)]
          exact hc.congr (fun u hu => congrArg (fun w : St => w 2) (hZ_Zc u (le_trans hs hu.1)))
        exact hc'.intervalIntegrable
      have hint3 : IntervalIntegrable (fun σ : ℝ => Z σ 3) volume s 1 := by
        have hc : ContinuousOn (fun σ : ℝ => Zc σ 3) (Set.Icc s 1) :=
          (continuous_apply (3 : Fin 4)).comp_continuousOn
            (hZcc.mono (Set.Icc_subset_Icc hs le_rfl))
        have hc' : ContinuousOn (fun σ : ℝ => Z σ 3) (Set.uIcc s 1) := by
          rw [Set.uIcc_of_le (by linarith)]
          exact hc.congr (fun u hu => congrArg (fun w : St => w 3) (hZ_Zc u (le_trans hs hu.1)))
        exact hc'.intervalIntegrable
      exact ⟨deriv_row_of_identity hev0 hint2 hmeas2 hcont2,
        deriv_row_of_identity hev1 hint3 hmeas3 hcont3⟩
    · have hZs : Z s = baseState s := by
        rw [hZ_Zc s (by linarith), hZcM s (by linarith), hZMtail s (by linarith)]
      have hnear0 : (fun u : ℝ => Z u 0) =ᶠ[𝓝 s] (fun u : ℝ => baseState u 0) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs9) (fun u hu => by
          have hu9 : (9 / 10 : ℝ) < u := hu
          show Z u 0 = baseState u 0
          rw [hZ_Zc u (by linarith), hZcM u (by linarith), hZMtail u (le_of_lt hu9)])
      have hnear1 : (fun u : ℝ => Z u 1) =ᶠ[𝓝 s] (fun u : ℝ => baseState u 1) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs9) (fun u hu => by
          have hu9 : (9 / 10 : ℝ) < u := hu
          show Z u 1 = baseState u 1
          rw [hZ_Zc u (by linarith), hZcM u (by linarith), hZMtail u (le_of_lt hu9)])
      refine ⟨?_, ?_⟩
      · rw [hnear0.deriv_eq, hZs]
        simp [baseState]
      · rw [hnear1.deriv_eq, hZs]
        simp [baseState]
  -- conclusion
  have hZcont : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1) :=
    hZcc.congr (fun u hu => hZ_Zc u hu.1)
  have hZeq : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Godd n h s (Z s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) + Xi n h s := by
    intro s hs
    have hseg : (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ))
        = ∫ σ in s..(1 : ℝ), Theta n h s σ (Zc σ) :=
      intervalIntegral.integral_congr (fun σ hσ => by
        rw [Set.uIcc_of_le hs.2.le] at hσ
        exact congrArg (fun w : St => Theta n h s σ w) (hZ_Zc σ (le_trans hs.1.le hσ.1)))
    rw [hZ_Zc s hs.1.le, hseg]
    rcases le_or_gt s (9 / 10) with h9 | h9
    · exact hZc_eq_Icc s ⟨hs.1.le, h9⟩
    · exact hZc_eq_tail s ⟨h9, hs.2⟩
  have hZtail : ∀ s : ℝ, 1 - tau ≤ s → Z s = baseState s := by
    intro s hs
    have h9 : (1 : ℝ) - tau = 9 / 10 := by norm_num [tau]
    have hs9 : (9 / 10 : ℝ) ≤ s := by rw [← h9]; exact hs
    rw [hZ_Zc s (by linarith), hZcM s (by linarith), hZMtail s hs9]
  have hZdist : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1, dist (Z s) (baseState s) ≤ ρ := by
    intro s hs
    rw [hZ_Zc s hs.1]
    rcases le_or_gt s (7 / 10) with hlt | hgt
    · rw [hZcL s hlt]
      exact le_trans (hZLd s ⟨hs.1, hlt⟩) hνρ
    · rw [hZcM s hgt]
      exact le_trans (le_trans (hZMd s ⟨le_of_lt hgt, hs.2⟩) hην) hνρ
  exact ⟨Z, hZcont, hZeq, hZtail, hZdist, hrows⟩

end

end Work.OddVolterra.WinData
