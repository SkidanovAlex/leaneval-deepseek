import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.TW_regular
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.Anchor.ThetaM_contDiffOn_wide
import Submission.Work.OddVolterra.Window.TW2_defs
import Submission.Work.OddVolterra.Window.TW2_kvecM_state_unif
import Submission.Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## The region on which the cut-off `chiT2` may be non-zero -/

/-- The open region on which the smooth cut-off `chiT2` may be non-vanishing. -/
def tw2Region : Set (ℝ × ℝ × St) :=
  {p | 3 / 5 < p.1 ∧ p.1 < 1 ∧ 3 / 5 < p.2.1 ∧ p.2.1 < 1 ∧ wsq p.2.1 p.2.2 < 4 / 25}

lemma tw2_continuous_wsq : Continuous (fun p : ℝ × ℝ × St => wsq p.2.1 p.2.2) := by
  have hbase : Continuous (fun p : ℝ × ℝ × St => baseState p.2.1) :=
    Work.OddVolterra.Existence.contDiff_baseState_comp.continuous.comp continuous_snd
  have h : (fun p : ℝ × ℝ × St => wsq p.2.1 p.2.2)
      = fun p => ∑ i : Fin 4, (p.2.2 i - baseState p.2.1 i) ^ 2 := by
    funext p; rfl
  rw [h]
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).sub
      ((continuous_apply i).comp hbase)).pow 2

lemma tw2_isOpen_tw2Region : IsOpen tw2Region := by
  have h1 : Continuous (fun p : ℝ × ℝ × St => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × ℝ × St => p.2.1) := continuous_fst.comp continuous_snd
  have h : tw2Region = (fun p : ℝ × ℝ × St => p.1) ⁻¹' Set.Ioo (3 / 5) 1 ∩
      (((fun p : ℝ × ℝ × St => p.2.1) ⁻¹' Set.Ioo (3 / 5) 1) ∩
       ((fun p : ℝ × ℝ × St => wsq p.2.1 p.2.2) ⁻¹' Set.Iio (4 / 25))) := by
    ext p; simp [tw2Region, Set.mem_Ioo, Set.mem_Iio, and_assoc]
  rw [h]
  exact (isOpen_Ioo.preimage h1).inter ((isOpen_Ioo.preimage h2).inter
    (isOpen_Iio.preimage tw2_continuous_wsq))

lemma tw2_chiT2_eq_zero {p : ℝ × ℝ × St} (hp : p ∉ tw2Region) :
    chiT2 p.1 p.2.1 p.2.2 = 0 := by
  by_contra h
  have h1 : (cs : ℝ → ℝ) p.1 ≠ 0 := fun h0 => h (by simp [chiT2, h0])
  have h2 : (cs : ℝ → ℝ) p.2.1 ≠ 0 := fun h0 => h (by simp [chiT2, h0])
  have h3 : (cz2 : ℝ → ℝ) (wsq p.2.1 p.2.2) ≠ 0 := fun h0 => h (by simp [chiT2, h0])
  have hs1 : 3 / 5 < p.1 := tw_cs_ne_zero_lower h1
  have hs2 : p.1 < 1 := tw_cs_ne_zero_upper h1
  have ht1 : 3 / 5 < p.2.1 := tw_cs_ne_zero_lower h2
  have ht2 : p.2.1 < 1 := tw_cs_ne_zero_upper h2
  have hw : wsq p.2.1 p.2.2 < 4 / 25 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact h3 (cz2_eq_zero_of_le hcon)
  exact hp ⟨hs1, hs2, ht1, ht2, hw⟩

/-- A state in the region of a slope `σ ∈ (3/5, 1)` has its first two coordinates at least
`1/4`. -/
lemma tw2_quarter_le_of_region {σ : ℝ} (hσ : 3 / 5 < σ) (hσ1 : σ < 1) {z : St}
    (hw : wsq σ z < 4 / 25) : 1 / 4 ≤ z 0 ∧ 1 / 4 ≤ z 1 := by
  have hnorm : ‖z - baseState σ‖ < 2 / 5 := by
    have h6 : ‖z - baseState σ‖ ^ 2 ≤ wsq σ z := sq_norm_le_wsq σ z
    have h7 : ‖z - baseState σ‖ ^ 2 < (2 / 5 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (z - baseState σ)]
    nlinarith [norm_nonneg (z - baseState σ)]
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ :=
    seven_tenths_le_profileX (by linarith) (by linarith)
  have key : ∀ i : Fin 4, baseState σ i = Commons.Geometry.Ulam.profileX σ → 1 / 4 ≤ z i := by
    intro i hi
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    rw [hi] at h
    linarith [(abs_lt.mp (lt_of_le_of_lt h hnorm)).1]
  refine ⟨key 0 (by simp [Work.OddVolterra.baseState]),
    key 1 (by simp [Work.OddVolterra.baseState])⟩

/-- `tw2Region` is mapped into the region of smoothness of the manifest `Θ`-data. -/
lemma tw2_mapsTo_good {p : ℝ × ℝ × St} (hp : p ∈ tw2Region) :
    (p.1, p.2.1, p.2.2) ∈ Work.Anchor.Good := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hnorm : ‖p.2.2 - baseState p.2.1‖ < 2 / 5 := by
    have h6 : ‖p.2.2 - baseState p.2.1‖ ^ 2 ≤ wsq p.2.1 p.2.2 := sq_norm_le_wsq _ _
    have h7 : ‖p.2.2 - baseState p.2.1‖ ^ 2 < (2 / 5 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (p.2.2 - baseState p.2.1)]
    nlinarith [norm_nonneg (p.2.2 - baseState p.2.1)]
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX p.2.1 :=
    seven_tenths_le_profileX (by linarith) (by linarith)
  have key : ∀ i : Fin 4, baseState p.2.1 i = Commons.Geometry.Ulam.profileX p.2.1 →
      1 / 5 < |p.2.2 i| := by
    intro i hi
    have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    rw [hi] at h
    have hgt : (1 / 5 : ℝ) < p.2.2 i := by
      linarith [(abs_lt.mp (lt_of_le_of_lt h hnorm)).1]
    rwa [abs_of_pos (by linarith)]
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    key 0 (by simp [Work.OddVolterra.baseState]), key 1 (by simp [Work.OddVolterra.baseState])⟩

/-- On `tw2Region` the clamped `Θ`-datum of `TW2` is the manifest one. -/
lemma tw2_thetac_eq (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : 3 / 5 ≤ s) (hσ : 3 / 5 ≤ σ) {z : St}
    (hz0 : 1 / 5 ≤ z 0) (hz1 : 1 / 5 ≤ z 1) :
    (if s < σ then Theta n h s σ z else KernelExt.ThetaM n h s σ z)
      = KernelExt.ThetaM n h s σ z := by
  by_cases hlt : s < σ
  · rw [if_pos hlt]
    refine (ThetaM_eq_Theta n hn hh hlt (δ := 1 / 10) (by norm_num) z
      (fun a ha => ?_) (fun a ha => ?_)).symm
    · refine krad_pos_of_region hsmall1 (by linarith [ha.1, ha.2, hσ]) ?_
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    · refine krad_pos_of_region hsmall1 (by linarith [ha.1, ha.2, hσ]) ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
  · rw [if_neg hlt]

/-- The global manifest form of `TW2`. -/
lemma tw2_TW2_eq_manifest (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (p : ℝ × ℝ × St) :
    TW2 n h p.1 p.2.1 p.2.2
      = chiT2 p.1 p.2.1 p.2.2 • KernelExt.ThetaM n h p.1 p.2.1 p.2.2 := by
  rw [TW2]
  by_cases hp : p ∈ tw2Region
  · obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
    obtain ⟨hz0, hz1⟩ := tw2_quarter_le_of_region hp3 hp4 hp5
    rw [tw2_thetac_eq n hn hh hsmall1 (le_of_lt hp1) (le_of_lt hp3) (by linarith) (by linarith)]
  · rw [tw2_chiT2_eq_zero hp, zero_smul, zero_smul]

lemma tw2_continuous_chiT2 : Continuous (fun p : ℝ × ℝ × St => chiT2 p.1 p.2.1 p.2.2) := by
  have hcs1 : Continuous (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff cs (n := ⊤)).continuous.comp continuous_fst
  have hcs2 : Continuous (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.2.1) :=
    (ContDiffBump.contDiff cs (n := ⊤)).continuous.comp (continuous_fst.comp continuous_snd)
  have hcz2 : Continuous (fun p : ℝ × ℝ × St => (cz2 : ℝ → ℝ) (wsq p.2.1 p.2.2)) :=
    (ContDiffBump.contDiff cz2 (n := ⊤)).continuous.comp tw2_continuous_wsq
  rw [show (fun p : ℝ × ℝ × St => chiT2 p.1 p.2.1 p.2.2)
      = fun p => (cs : ℝ → ℝ) p.1 * ((cs : ℝ → ℝ) p.2.1 *
          (cz2 : ℝ → ℝ) (wsq p.2.1 p.2.2)) from by
    funext p; rw [chiT2]; ring]
  exact hcs1.mul (hcs2.mul hcz2)

/-! ## Lipschitz data of the smooth state cut-off -/

/-- On the window the smooth cut-off `chiT2` is the state bump alone. -/
lemma chiT2_eq_cz2_of_mem {s σ : ℝ} (hs : s ∈ Set.Icc wLeft wRight)
    (hσ : σ ∈ Set.Icc wLeft wRight) (z : St) :
    chiT2 s σ z = (cz2 : ℝ → ℝ) (wsq σ z) := by
  rw [chiT2, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ, one_mul, one_mul]

/-- The squared Euclidean distance to the base state is Lipschitz on the ball of radius `9/20`. -/
lemma tw2_wsq_lipschitz {σ : ℝ} {z z' : St}
    (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20))
    (hz' : z' ∈ Metric.closedBall (baseState σ) (9 / 20)) :
    |wsq σ z - wsq σ z'| ≤ (18 / 5) * ‖z - z'‖ := by
  have hcoord : ∀ i : Fin 4, |z i - z' i| ≤ ‖z - z'‖ := by
    intro i
    have h := norm_le_pi_norm (z - z') i
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have hb : ∀ i : Fin 4, |z i + z' i - 2 * baseState σ i| ≤ 9 / 10 := by
    intro i
    have h1 : |z i - baseState σ i| ≤ 9 / 20 := by
      have h := norm_le_pi_norm (z - baseState σ) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h (Metric.mem_closedBall.mp hz)
    have h2 : |z' i - baseState σ i| ≤ 9 / 20 := by
      have h := norm_le_pi_norm (z' - baseState σ) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h (Metric.mem_closedBall.mp hz')
    have hsplit : z i + z' i - 2 * baseState σ i
        = (z i - baseState σ i) + (z' i - baseState σ i) := by ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (by linarith)
  have hterm : ∀ i : Fin 4,
      |(z i - baseState σ i) ^ 2 - (z' i - baseState σ i) ^ 2|
        ≤ ‖z - z'‖ * (9 / 10) := by
    intro i
    have hfac : (z i - baseState σ i) ^ 2 - (z' i - baseState σ i) ^ 2
        = (z i - z' i) * (z i + z' i - 2 * baseState σ i) := by ring
    rw [hfac, abs_mul]
    exact mul_le_mul (hcoord i) (hb i) (abs_nonneg _) (norm_nonneg _)
  have hsum : wsq σ z - wsq σ z'
      = ∑ i : Fin 4, ((z i - baseState σ i) ^ 2 - (z' i - baseState σ i) ^ 2) := by
    rw [wsq, wsq, Finset.sum_sub_distrib]
  rw [hsum]
  calc |∑ i : Fin 4, ((z i - baseState σ i) ^ 2 - (z' i - baseState σ i) ^ 2)|
      ≤ ∑ i : Fin 4, |(z i - baseState σ i) ^ 2 - (z' i - baseState σ i) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, ‖z - z'‖ * (9 / 10) := Finset.sum_le_sum fun i _ => hterm i
    _ = (18 / 5) * ‖z - z'‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The state cut-off `cz2 ∘ wsq σ` of `TW2` is Lipschitz on the ball of radius `9/20`, with a
constant independent of `σ`. -/
lemma tw2_exists_cz2_wsq_lipschitz :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
        |(cz2 : ℝ → ℝ) (wsq σ z) - (cz2 : ℝ → ℝ) (wsq σ z')| ≤ K * ‖z - z'‖ := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (ContDiffBump.hasCompactSupport cz2) (ContDiffBump.contDiff cz2 (n := ⊤)) (by simp)
  refine ⟨(L : ℝ) * (18 / 5), by positivity, ?_⟩
  intro σ z hz z' hz'
  have hw := tw2_wsq_lipschitz (σ := σ) hz hz'
  have h1 := hL.dist_le_mul (wsq σ z) (wsq σ z')
  rw [Real.dist_eq] at h1
  calc |(cz2 : ℝ → ℝ) (wsq σ z) - (cz2 : ℝ → ℝ) (wsq σ z')|
      ≤ (L : ℝ) * |wsq σ z - wsq σ z'| := h1
    _ ≤ (L : ℝ) * ((18 / 5) * ‖z - z'‖) :=
        mul_le_mul_of_nonneg_left hw L.coe_nonneg
    _ = ((L : ℝ) * (18 / 5)) * ‖z - z'‖ := by ring

/-! ## The two conclusions -/

theorem TW2_regular (n : ℕ) (hn : 1 ≤ n) :
    (∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      Continuous (fun p : ℝ × ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.Window.TW2 n h p.1 p.2.1 p.2.2)) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ σ ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
        ‖Work.OddVolterra.Window.TW2 n h s σ z - Work.OddVolterra.Window.TW2 n h s σ z'‖
          ≤ L * ‖z - z'‖) := by
  refine ⟨?_, ?_⟩
  · -- continuity of the clamped `Θ`-datum
    intro h hh hsupp hsmall
    have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
      fun k hk s => hsmall k (by omega) s
    have hΘ : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ × St => KernelExt.ThetaM n h q.1 q.2.1 q.2.2) Work.Anchor.Good :=
      Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall1
    have hψ : ContinuousOn (fun p : ℝ × ℝ × St =>
        KernelExt.ThetaM n h p.1 p.2.1 p.2.2) tw2Region :=
      hΘ.continuousOn.comp (by fun_prop) (fun p hp => tw2_mapsTo_good hp)
    have hbd : ∀ p : ℝ × ℝ × St, ∃ C : ℝ, ∃ V ∈ 𝓝 p, ∀ q ∈ V, q ∈ tw2Region →
        ‖KernelExt.ThetaM n h q.1 q.2.1 q.2.2‖ ≤ C := by
      intro p
      obtain ⟨C, hC⟩ := tw_twBox_bound n hh hsmall1
        (max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1)
      refine ⟨max C 0, Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
      intro q hq hqreg
      obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hqreg
      have hqnorm : ‖q - p‖ < 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hq; exact hq
      have hcoord : ∀ i : Fin 4, |q.2.2 i| ≤
          max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1 := by
        intro i
        have h1 : |q.2.2 i - p.2.2 i| ≤ 1 := by
          have h : ‖q.2.2 i - p.2.2 i‖ ≤ ‖q - p‖ := by
            calc ‖q.2.2 i - p.2.2 i‖ ≤ ‖q.2.2 - p.2.2‖ := norm_le_pi_norm (q.2.2 - p.2.2) i
              _ ≤ ‖(q - p).2.2‖ := by rw [show (q - p).2.2 = q.2.2 - p.2.2 from rfl]
              _ ≤ ‖(q - p).2‖ := norm_snd_le _
              _ ≤ ‖q - p‖ := norm_snd_le _
          rw [← Real.norm_eq_abs]
          exact le_trans h hqnorm.le
        have h2 : |p.2.2 i| ≤ max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| := by
          fin_cases i
          · exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))
          · exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_refl _)))
          · exact le_max_of_le_left (le_max_of_le_right (le_refl _))
          · exact le_max_of_le_right (le_refl _)
        calc |q.2.2 i| = |(q.2.2 i - p.2.2 i) + p.2.2 i| := by ring_nf
          _ ≤ |q.2.2 i - p.2.2 i| + |p.2.2 i| := abs_add_le _ _
          _ ≤ 1 + max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| := add_le_add h1 h2
          _ = max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1 := by ring
      refine le_trans (hC (q.1, q.2.1, q.2.2) ?_) (le_max_left _ _)
      obtain ⟨hz0, hz1⟩ := tw2_quarter_le_of_region hq3 hq4 hq5
      exact ⟨⟨le_of_lt hq1, le_of_lt hq2⟩, ⟨le_of_lt hq3, le_of_lt hq4⟩, hz0, hz1, hcoord⟩
    rw [show (fun p : ℝ × ℝ × St => TW2 n h p.1 p.2.1 p.2.2)
        = fun p => chiT2 p.1 p.2.1 p.2.2 • KernelExt.ThetaM n h p.1 p.2.1 p.2.2
        from funext fun p => tw2_TW2_eq_manifest n hn hh hsmall1 p]
    exact tw_continuous_smul_of_continuous_of_continuousOn tw2_isOpen_tw2Region
      tw2_continuous_chiT2 (fun p hp => tw2_chiT2_eq_zero hp) hψ hbd
  · -- uniform Lipschitz in the state
    obtain ⟨Mk, Ck, hMk0, hCk0, hkvec⟩ := TW2_kvecM_state_unif n hn
    obtain ⟨M, B, hM0, hB0, hdata⟩ :=
      TW2_thetaM_state_unif_of_kvec n hn Mk Ck hMk0 hCk0 hkvec
    obtain ⟨Lcz, hLcz0, hcz⟩ := tw2_exists_cz2_wsq_lipschitz
    refine ⟨1 * M + Lcz * B, add_nonneg (mul_nonneg zero_le_one hM0)
      (mul_nonneg hLcz0 hB0), ?_⟩
    intro h hh hsupp hsmall s hs σ hσ z hz z' hz'
    have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
      fun k hk s => hsmall k (by omega) s
    have hinner : ∀ x ∈ Metric.closedBall (baseState σ) (9 / 20),
        ∀ y ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖TW2 n h s σ x - TW2 n h s σ y‖ ≤ (1 * M + Lcz * B) * ‖x - y‖ := by
      intro x hx y hy
      have h1 : TW2 n h s σ x = (cz2 : ℝ → ℝ) (wsq σ x) • KernelExt.ThetaM n h s σ x := by
        rw [tw2_TW2_eq_manifest n hn hh hsmall1 (s, σ, x), chiT2_eq_cz2_of_mem hs hσ x]
      have h2 : TW2 n h s σ y = (cz2 : ℝ → ℝ) (wsq σ y) • KernelExt.ThetaM n h s σ y := by
        rw [tw2_TW2_eq_manifest n hn hh hsmall1 (s, σ, y), chiT2_eq_cz2_of_mem hs hσ y]
      rw [h1, h2]
      exact tw_lipschitz_smul_of_lipschitz_of_bounded (Mf := 1) (Mg := B) (Kf := Lcz) (Kg := M)
        (fun x _ => abs_cz2_le_one _)
        (fun x hx => (hdata h hh hsupp hsmall s hs σ hσ x hx).1)
        (fun x hx y hy => hcz σ x hx y hy)
        (fun x hx y hy => (hdata h hh hsupp hsmall s hs σ hσ x hx).2 y hy)
        x hx y hy
    have hsupp2 : ∀ x : St, 2 / 5 ≤ ‖x - baseState σ‖ → TW2 n h s σ x = 0 := by
      intro x hx
      rw [tw2_TW2_eq_manifest n hn hh hsmall1 (s, σ, x), chiT2_eq_cz2_of_mem hs hσ x]
      have hwsq : 4 / 25 ≤ wsq σ x := by
        have h := sq_norm_le_wsq σ x
        nlinarith [norm_nonneg (x - baseState σ)]
      rw [cz2_eq_zero_of_le hwsq, zero_smul]
    exact tw_lipschitz_of_support_subset_of_lipschitz_on_closedBall (c := baseState σ)
      (r := 2 / 5) (R := 9 / 20) (M := 1 * M + Lcz * B) (by norm_num)
      (add_nonneg (mul_nonneg zero_le_one hM0) (mul_nonneg hLcz0 hB0)) hsupp2 hinner z z'

end

end Work.OddVolterra.Window
