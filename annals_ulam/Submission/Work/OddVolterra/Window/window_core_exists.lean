import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Window.Theta_close_window
import Submission.Work.OddVolterra.Window.Xi_close_window
import Submission.Work.OddVolterra.Window.TW_regular
import Submission.Work.OddVolterra.Window.XW_continuous
import Submission.Work.OddVolterra.Window.TW2_regular
import Submission.Work.OddVolterra.Window.GW2_fderiv_close_unif
import Submission.Work.OddCurveB.Existence.Box
import Submission.Work.OddVolterra.Window.window_data_regular
import Submission.Work.Anchor.ThetaM_close
import Submission.Work.Anchor.anchor_transfer
import Submission.Work.VolterraLong.Main
import Submission.Work.OddVolterra.Existence.odd_linearization
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero

/-!
# The window core of the odd transition-slope construction
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## Elementary facts about the ball's state -/

lemma wc_baseState_zero (s : ℝ) : baseState s 0 = Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma wc_baseState_one (s : ℝ) : baseState s 1 = Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma wc_baseState_two (s : ℝ) : baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma wc_baseState_three (s : ℝ) : baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma wc_norm_baseState_le_two {s : ℝ} (_hs : s ∈ Set.Icc wLeft wRight) : ‖baseState s‖ ≤ 2 := by
  have hpx : |Commons.Geometry.Ulam.profileX s| ≤ 2 := by
    have h := Commons.Geometry.Ulam.profileX_mem_Icc s
    linarith [abs_le.mpr h]
  have hd : |deriv Commons.Geometry.Ulam.profileX s| ≤ 2 := by
    have h := Commons.Geometry.Ulam.abs_deriv_profileX_le s
    linarith
  refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr (fun i => ?_)
  fin_cases i <;>
    · simp only [baseState, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons]
      first
        | exact hpx
        | exact hd

lemma wc_mem_half_one {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) : s ∈ Set.Icc (1 / 2 : ℝ) 1 :=
  ⟨le_trans (by norm_num [wLeft]) hs.1, le_trans hs.2 wRight_lt_one.le⟩

lemma wc_mem_theta {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) : s ∈ Set.Icc (7 / 10 : ℝ) 1 :=
  ⟨le_trans (by norm_num [wLeft]) hs.1, le_trans hs.2 wRight_lt_one.le⟩

lemma wc_mem_ball12 {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) :
    (19 / 20 : ℝ) ∈ Set.Icc wLeft wRight :=
  ⟨by norm_num [wLeft, wRight], by norm_num [wRight]⟩

/-! ## Uniform closeness of the `𝐆`-data -/

/-- The perturbed `𝐆`-row is uniformly close to the unperturbed one on the window. -/
lemma Godd_unif_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ τ > 0, ∃ γ > 0, ∀ h : ℝ → ℝ, ∀ s ∈ Set.Icc wLeft wRight,
      |h s| ≤ γ → |deriv h s| ≤ γ → ∀ z : St, ‖z‖ ≤ 3 →
        dist (Godd n h s z) (Godd n 0 s z) < τ := by
  intro τ hτ
  have hKc : IsCompact ((Set.Icc wLeft wRight ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
      ×ˢ Metric.closedBall (0 : St) 3) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_closedBall 0 3)
  obtain ⟨γ, hγ, hunif⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hKc.uniformContinuousOn_of_continuous
      (Work.OddCurveB.Est.continuous_GoddDiag n hn).continuousOn) (τ / 2) (by linarith)
  refine ⟨min 1 γ, lt_min one_pos hγ, ?_⟩
  intro h s hs h1 h2 z hz
  have h1' : |h s| ≤ 1 := le_trans h1 (min_le_left (1 : ℝ) γ)
  have h2' : |deriv h s| ≤ 1 := le_trans h2 (min_le_left (1 : ℝ) γ)
  have h3 : |h s| ≤ γ := le_trans h1 (min_le_right (1 : ℝ) γ)
  have h4 : |deriv h s| ≤ γ := le_trans h2 (min_le_right (1 : ℝ) γ)
  have hmem : (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) ∈
      (Set.Icc wLeft wRight ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
        ×ˢ Metric.closedBall (0 : St) 3 :=
    ⟨⟨hs, ⟨(abs_le.mp h1').1, (abs_le.mp h1').2⟩, ⟨(abs_le.mp h2').1, (abs_le.mp h2').2⟩⟩,
      Metric.mem_closedBall.mpr (by simpa using hz)⟩
  have hmem0 : (((s, (0 : ℝ), (0 : ℝ)) : ℝ × ℝ × ℝ), z) ∈
      (Set.Icc wLeft wRight ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
        ×ˢ Metric.closedBall (0 : St) 3 :=
    ⟨⟨hs, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩,
      Metric.mem_closedBall.mpr (by simpa using hz)⟩
  have hdist : dist (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z)
      (((s, (0 : ℝ), (0 : ℝ)) : ℝ × ℝ × ℝ), z) ≤ γ := by
    rw [dist_prod_same_right, dist_prod_same_left, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
      sub_zero, sub_zero]
    exact max_le h3 h4
  have hfinal := hunif _ hmem _ hmem0 hdist
  rw [Work.OddCurveB.Existence.Godd_eq_GoddDiag, Work.OddCurveB.Existence.Godd_zero_eq]
  exact lt_of_le_of_lt hfinal (by linarith)


/-! ## Regularity of the smooth-cut-off state data -/

lemma wc_chiG2_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => chiG2 p.1 p.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff cs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => wsq p.1 p.2) := by
    simp only [wsq]
    refine ContDiff.sum (fun i _ => ?_)
    exact (((contDiff_apply ℝ ℝ i).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ i).comp (wdr_contDiff_baseState.comp contDiff_fst))).pow 2
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (cz2 : ℝ → ℝ) (wsq p.1 p.2)) :=
    (ContDiffBump.contDiff cz2).comp h2
  simpa only [chiG2] using h1.mul h3

lemma wc_chiG2_eq_zero_of_not_mem {s : ℝ} {z : St}
    (h : ¬ (|s - wCenter| ≤ 4 / 25 ∧ ‖z - baseState s‖ ≤ 2 / 5)) : chiG2 s z = 0 := by
  rw [chiG2]
  by_cases h1 : |s - wCenter| ≤ 4 / 25
  · have h2 : ¬ (‖z - baseState s‖ ≤ 2 / 5) := fun h2 => h ⟨h1, h2⟩
    have h3 : 4 / 25 ≤ wsq s z := by
      have := sq_norm_le_wsq s z
      nlinarith [le_of_not_ge h2, norm_nonneg (z - baseState s)]
    rw [cz2_eq_zero_of_le h3, mul_zero]
  · rw [cs_eq_zero (le_of_not_ge h1), zero_mul]

lemma wc_tsupport_chiG2_subset :
    tsupport (fun p : ℝ × St => chiG2 p.1 p.2) ⊆
      {p : ℝ × St | |p.1 - wCenter| ≤ 4 / 25 ∧ ‖p.2 - baseState p.1‖ ≤ 2 / 5} := by
  refine closure_minimal (fun p hp => ?_) ?_
  · by_contra h
    exact hp (wc_chiG2_eq_zero_of_not_mem h)
  · exact IsClosed.inter
      (isClosed_le (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const)
      (isClosed_le
        ((continuous_snd.sub (wdr_contDiff_baseState.continuous.comp continuous_fst)).norm)
        continuous_const)

lemma wc_tsupport_chiG2_subset_awGood :
    tsupport (fun p : ℝ × St => chiG2 p.1 p.2) ⊆ Existence.awGood := by
  intro p hp
  obtain ⟨h1, h2⟩ := wc_tsupport_chiG2_subset hp
  have h21 : |p.1| ≤ 21 / 20 := by
    have h := abs_le.mp h1
    rw [wCenter] at h
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX p.1 := wdr_profileX_ge_17_25 h21
  have h1a : 9 / 20 < p.1 := by
    have h := abs_le.mp h1; rw [wCenter] at h; linarith [h.1]
  have h1b : p.1 < 21 / 20 := by
    have h := abs_le.mp h1; rw [wCenter] at h; linarith [h.2]
  refine ⟨h1a, h1b, ?_, ?_⟩
  · have hb : |p.2 0 - baseState p.1 0| ≤ ‖p.2 - baseState p.1‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (p.2 - baseState p.1) 0
    have hb' : |p.2 0 - baseState p.1 0| ≤ 2 / 5 := le_trans hb h2
    rw [wc_baseState_zero] at hb'
    have hle : Commons.Geometry.Ulam.profileX p.1 - 2 / 5 ≤ p.2 0 := by
      linarith [(abs_le.mp hb').1]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hb : |p.2 1 - baseState p.1 1| ≤ ‖p.2 - baseState p.1‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (p.2 - baseState p.1) 1
    have hb' : |p.2 1 - baseState p.1 1| ≤ 2 / 5 := le_trans hb h2
    rw [wc_baseState_one] at hb'
    have hle : Commons.Geometry.Ulam.profileX p.1 - 2 / 5 ≤ p.2 1 := by
      linarith [(abs_le.mp hb').1]
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The smooth-cut-off state data is `C^∞` (hence continuous and differentiable in the state). -/
lemma wc_GW2_contDiff (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => GW2 n h p.1 p.2) := by
  have hg := wdr_contDiffOn_godd n hh hsupp hsm1
  have h := wdr_contDiff_smul_of_contDiffOn (X := ℝ × St) (E := St) Existence.isOpen_awGood
    wc_chiG2_contDiff hg wc_tsupport_chiG2_subset_awGood
  simpa only [GW2] using h

/-! ## Closeness of the smooth-cut-off data -/

lemma wc_GW2_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
        dist (GW2 n h s z) (GW2 n 0 s z) < ε := by
  intro ε hε
  obtain ⟨γ, hγ, hGodd⟩ := Godd_unif_close n hn (ε / 2) (by linarith)
  refine ⟨γ, hγ, ?_⟩
  intro h hh hsupp hsmall s hs z hz
  have h1 : |h s| ≤ γ := by simpa using hsmall 0 (by omega) s
  have h2 : |deriv h s| ≤ γ := by simpa [iteratedDeriv_one] using hsmall 1 (by omega) s
  by_cases hfar : (2 / 5 : ℝ) ≤ ‖z - baseState s‖
  · rw [show GW2 n h s z = 0 from by rw [GW2, chiG2_eq_zero_of_far hfar, zero_smul],
      show GW2 n 0 s z = 0 from by rw [GW2, chiG2_eq_zero_of_far hfar, zero_smul], dist_self]
    exact hε
  · push_neg at hfar
    have hz3 : ‖z‖ ≤ 3 := by
      have h := wc_norm_baseState_le_two hs
      calc ‖z‖ = ‖(z - baseState s) + baseState s‖ := by ring_nf
        _ ≤ ‖z - baseState s‖ + ‖baseState s‖ := norm_add_le _ _
        _ ≤ 3 := by linarith
    have hclose := hGodd h s hs h1 h2 z hz3
    rw [dist_eq_norm] at hclose ⊢
    rw [GW2, GW2, ← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |chiG2 s z| * ‖Godd n h s z - Godd n 0 s z‖
        ≤ 1 * ‖Godd n h s z - Godd n 0 s z‖ :=
          mul_le_mul_of_nonneg_right (abs_chiG2_le_one s z) (norm_nonneg _)
      _ < ε := by rw [one_mul]; linarith

lemma wc_TW2_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) 1,
        dist (TW2 n h s σ z) (TW2 n 0 s σ z) < ε := by
  intro ε hε
  obtain ⟨CΘM, hCΘM, hΘM⟩ := Work.Anchor.ThetaM_close n hn
  obtain ⟨δΘ, hδΘ, hΘ⟩ := Theta_close_window n hn (ε / 2) (by linarith)
  set δt : ℝ := min (1 / 100) (min δΘ (ε / (2 * (CΘM + 1)))) with hδt
  have hδt_pos : 0 < δt := lt_min (by norm_num) (lt_min hδΘ (div_pos hε (by linarith)))
  have hδt100 : δt ≤ 1 / 100 := min_le_left _ _
  have hδtΘ : δt ≤ δΘ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδtM : δt ≤ ε / (2 * (CΘM + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δt, hδt_pos, ?_⟩
  intro h hh hsupp hsmall s hs σ hσ z hz
  have hsm100 : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 := fun k hk t =>
    le_trans (hsmall k hk t) hδt100
  have hsmΘ : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ δΘ := fun k hk t =>
    le_trans (hsmall k hk t) hδtΘ
  by_cases hfar : (2 / 5 : ℝ) ≤ ‖z - baseState σ‖
  · rw [TW2, TW2, chiT2_eq_zero_of_far hfar, zero_smul, zero_smul, dist_self]
    exact hε
  push_neg at hfar
  have hth : ‖(if s < σ then Theta n h s σ z else KernelExt.ThetaM n h s σ z) -
      (if s < σ then Theta n 0 s σ z else KernelExt.ThetaM n 0 s σ z)‖ ≤ ε / 2 := by
    by_cases hlt : s < σ
    · rw [if_pos hlt, if_pos hlt]
      have hz' : ‖z - baseState σ‖ ≤ 2 / 5 := le_of_lt hfar
      exact le_of_lt (hΘ h hh hsupp hsmΘ s hs σ (wc_mem_theta hσ) z hz')
    · rw [if_neg hlt, if_neg hlt]
      have hz2 : ‖z - baseState σ‖ ≤ 1 / 2 := le_trans (le_of_lt hfar) (by norm_num)
      have hb := hΘM h hh hsupp δt hδt_pos hδt100 hsmall s (wc_mem_half_one hs)
        σ (wc_mem_half_one hσ) z hz2
      have hle : CΘM * δt ≤ ε / 2 := by
        calc CΘM * δt ≤ CΘM * (ε / (2 * (CΘM + 1))) := mul_le_mul_of_nonneg_left hδtM hCΘM.le
          _ = ε * (CΘM / (2 * (CΘM + 1))) := by ring
          _ ≤ ε * (1 / 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hε.le
              rw [div_le_iff₀ (by linarith)]
              linarith
          _ = ε / 2 := by ring
      linarith
  calc dist (TW2 n h s σ z) (TW2 n 0 s σ z)
        = |chiT2 s σ z| * ‖(if s < σ then Theta n h s σ z else KernelExt.ThetaM n h s σ z) -
            (if s < σ then Theta n 0 s σ z else KernelExt.ThetaM n 0 s σ z)‖ := by
          rw [TW2, TW2, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (ε / 2) :=
          mul_le_mul (abs_chiT2_le_one s σ z) hth (norm_nonneg _) (by norm_num)
      _ < ε := by linarith

/-- Closeness of the cut-off source at level `ε`. -/
lemma wc_XW_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc wLeft wRight, dist (XW n h s) (XW n 0 s) < ε := by
  intro ε hε
  obtain ⟨δΞ, hδΞ, hΞ⟩ := Xi_close_window n hn (ε / 2) (by linarith)
  obtain ⟨δΘ, hδΘ, hΘ⟩ := Theta_close_window n hn (ε / 4) (by linarith)
  set δt : ℝ := min δΞ (min δΘ (1 / 100)) with hδt
  have hδt_pos : 0 < δt := lt_min hδΞ (lt_min hδΘ (by norm_num))
  have hδtΞ : δt ≤ δΞ := min_le_left _ _
  have hδtΘ : δt ≤ δΘ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδt100 : δt ≤ 1 / 100 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δt, hδt_pos, ?_⟩
  intro h hh hsupp hsmall s hs
  have hsmΞ : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ δΞ := fun k hk t =>
    le_trans (hsmall k hk t) hδtΞ
  have hsmΘ : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ δΘ := fun k hk t =>
    le_trans (hsmall k hk t) hδtΘ
  have hsm100 : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 := fun k hk t =>
    le_trans (hsmall k hk t) hδt100
  have hsm1 : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 :=
    fun k hk t => hsm100 k (le_trans hk (by omega)) t
  have hs1 : s ∈ Set.Icc (1 / 2 : ℝ) 1 := wc_mem_half_one hs
  have hs1' : s ≤ 1 := le_trans hs.2 wRight_lt_one.le
  have hsub_iv : Set.uIcc wRight 1 ⊆ Set.uIcc s 1 := by
    simp only [Set.uIcc_of_le (le_of_lt wRight_lt_one), Set.uIcc_of_le hs1']
    exact Set.Icc_subset_Icc hs.2 le_rfl
  have hI_h : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (baseState σ)) volume wRight 1 :=
    (Work.Anchor.intervalIntegrable_Theta_base (n := n) hn hh hsupp hsm1 hs1 hs1' le_rfl).mono_set
      hsub_iv
  have hI_0 : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume wRight 1 :=
    (Work.Anchor.intervalIntegrable_Theta_base (n := n) hn contDiff_const
      (fun x hx => absurd rfl hx) (fun k hk t => by simp) hs1 hs1' le_rfl).mono_set hsub_iv
  have hint_h : IntervalIntegrable (fun σ : ℝ => thetac n h s σ (baseState σ)) volume wRight 1 :=
    hI_h.congr (fun σ hσ => by
      rw [Set.uIoc_of_le (le_of_lt wRight_lt_one)] at hσ
      rw [thetac, if_pos (lt_of_le_of_lt hs.2 hσ.1)])
  have hint_0 : IntervalIntegrable (fun σ : ℝ => thetac n 0 s σ (baseState σ)) volume wRight 1 :=
    hI_0.congr (fun σ hσ => by
      rw [Set.uIoc_of_le (le_of_lt wRight_lt_one)] at hσ
      rw [thetac, if_pos (lt_of_le_of_lt hs.2 hσ.1)])
  have hbnd : ∀ σ ∈ Set.uIoc wRight 1,
      ‖thetac n h s σ (baseState σ) - thetac n 0 s σ (baseState σ)‖ ≤ ε / 4 := by
    intro σ hσ
    rw [Set.uIoc_of_le (le_of_lt wRight_lt_one)] at hσ
    have hsσ : s < σ := lt_of_le_of_lt hs.2 hσ.1
    have hσΘ : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := by
      refine ⟨?_, hσ.2⟩
      have h1 : (7 / 10 : ℝ) ≤ wRight := by norm_num [wRight]
      linarith [h1, hσ.1]
    rw [thetac, if_pos hsσ, thetac, if_pos hsσ]
    have h2 : ‖baseState σ - baseState σ‖ ≤ 2 / 5 := by
      rw [sub_self, norm_zero]; norm_num
    have h := hΘ h hh hsupp hsmΘ s hs σ hσΘ (baseState σ) h2
    linarith
  have htail : ‖(∫ σ in wRight..(1 : ℝ), thetac n h s σ (baseState σ)) -
      ∫ σ in wRight..(1 : ℝ), thetac n 0 s σ (baseState σ)‖ ≤ ε / 4 := by
    rw [← intervalIntegral.integral_sub hint_h hint_0]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (a := wRight) (b := 1)
      (C := ε / 4) hbnd) ?_
    rw [abs_of_nonneg (by linarith [wRight_lt_one])]
    have h20 : (1 : ℝ) - wRight = 1 / 20 := by norm_num [wRight]
    rw [h20]
    linarith
  have hxi : ‖Xi n h s - Xi n 0 s‖ < ε / 2 := hΞ h hh hsupp hsmΞ s hs
  have hsub : XW n h s - XW n 0 s = (cs : ℝ → ℝ) s •
      ((Xi n h s - Xi n 0 s) + ((∫ σ in wRight..(1 : ℝ), thetac n h s σ (baseState σ)) -
        ∫ σ in wRight..(1 : ℝ), thetac n 0 s σ (baseState σ))) := by
    rw [XW, XW, ← smul_sub]
    congr 1
    abel
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  calc |(cs : ℝ → ℝ) s| * _ ≤ 1 * _ :=
        mul_le_mul_of_nonneg_right (abs_cs_le_one s) (norm_nonneg _)
    _ < ε := by
        rw [one_mul]
        refine lt_of_le_of_lt (norm_add_le _ _) ?_
        linarith


lemma wsq_self (s : ℝ) : wsq s (baseState s) = 0 := by
  simp [wsq]

/-- The base identity for the cut-off data. -/
lemma wc_base_identity (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Icc wLeft wRight,
      GW2 n 0 s (baseState s) =
        (∫ σ in s..wRight, TW2 n 0 s σ (baseState σ)) + XW n 0 s := by
  intro s hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num [wLeft]) hs.1, lt_of_le_of_lt hs.2 wRight_lt_one⟩
  have hbase : Godd n 0 s (baseState s) =
      (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) + Xi n 0 s := by
    exact Work.OddVolterra.Existence.base_volterra n hn s hs01
  have hs1 : s ∈ Set.Icc (1 / 2 : ℝ) 1 := wc_mem_half_one hs
  have hsm1 : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) t| ≤ 1 / 100 :=
    fun k hk t => by simp
  have hint1 : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume s wRight :=
    Work.Anchor.intervalIntegrable_Theta_base (n := n) hn contDiff_const (fun x hx => absurd rfl hx)
      hsm1 hs1 hs.2 (le_of_lt wRight_lt_one)
  have hint2 : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume wRight 1 :=
    (Work.Anchor.intervalIntegrable_Theta_base (n := n) hn contDiff_const
      (fun x hx => absurd rfl hx) hsm1 hs1 hs1.2 le_rfl).mono_set
      (by
        simp only [Set.uIcc_of_le (le_of_lt wRight_lt_one),
          Set.uIcc_of_le (le_trans hs.2 wRight_lt_one.le : s ≤ 1)]
        exact Set.Icc_subset_Icc hs.2 le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hGW : GW2 n 0 s (baseState s) = Godd n 0 s (baseState s) := by
    rw [GW2, chiG2, cs_eq_one_of_mem hs, wsq_self, cz2_eq_one_of_le (by norm_num) le_rfl,
      one_mul, one_smul]
  have hTW : (∫ σ in s..wRight, TW2 n 0 s σ (baseState σ)) =
      ∫ σ in s..wRight, Theta n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le hs.2] at hσ
    have hsσ : s < σ := hσ.1
    have hσw : σ ∈ Set.Icc wLeft wRight := ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
    rw [TW2, if_pos hsσ, chiT2, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσw,
      wsq_self (σ), cz2_eq_one_of_le (by norm_num) le_rfl, one_mul, one_mul, one_smul]
  have hXW : XW n 0 s = Xi n 0 s + ∫ σ in wRight..(1 : ℝ), Theta n 0 s σ (baseState σ) := by
    rw [XW, cs_eq_one_of_mem hs, one_smul]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le (le_of_lt wRight_lt_one)] at hσ
    rw [thetac, if_pos (lt_of_le_of_lt hs.2 hσ.1)]
  rw [hGW, hbase, ← hsplit, hTW, hXW]
  ring

/-! ## Conversion of the cut-off data back to the paper's data -/

/-- On the window the smooth cut-off `chiG2` is `1` as soon as the state is within `1/100`. -/
lemma wc_GW2_eq_Godd_of_close (n : ℕ) {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Set.Icc wLeft wRight) {z : St} (hz : ‖z - baseState s‖ ≤ 1 / 100) :
    GW2 n h s z = Godd n h s z := by
  have h0 : 0 ≤ wsq s z := wsq_nonneg s z
  have h1 : wsq s z ≤ 1 / 100 := by
    refine le_trans (wsq_le_four_mul_sq_norm s z) ?_
    nlinarith [norm_nonneg (z - baseState s), hz]
  simp only [GW2, chiG2, cs_eq_one_of_mem hs, cz2_eq_one_of_le h1 h0, mul_one, one_smul]

/-- On the window the smooth cut-off `chiG2` is `1` on a neighbourhood of the base state. -/
lemma wc_eventuallyEq_GW2_Godd (n : ℕ) {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Set.Icc wLeft wRight) :
    (fun z => GW2 n h s z) =ᶠ[𝓝 (baseState s)] (fun z => Godd n h s z) := by
  filter_upwards [Metric.closedBall_mem_nhds (baseState s) (by norm_num : (0 : ℝ) < 1 / 100)]
    with z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  exact wc_GW2_eq_Godd_of_close n hs hz

/-- On the window, on the triangle `s < σ`, the smooth cut-off `chiT2` is `1` for states within
`1/100` of the base state, so `TW2` is the paper's `Theta` there. -/
lemma wc_TW2_eq_Theta_of_close (n : ℕ) {h : ℝ → ℝ} {s σ : ℝ}
    (hs : s ∈ Set.Icc wLeft wRight) (hσ : σ ∈ Set.Icc wLeft wRight) {z : St}
    (hsσ : s < σ) (hz : ‖z - baseState σ‖ ≤ 1 / 100) :
    TW2 n h s σ z = Theta n h s σ z := by
  have h0 : 0 ≤ wsq σ z := wsq_nonneg σ z
  have h1 : wsq σ z ≤ 1 / 100 := by
    refine le_trans (wsq_le_four_mul_sq_norm σ z) ?_
    nlinarith [norm_nonneg (z - baseState σ), hz]
  simp only [TW2, if_pos hsσ, chiT2, cs_eq_one_of_mem hs, cs_eq_one_of_mem hσ,
    cz2_eq_one_of_le h1 h0, mul_one, one_smul]

/-- On the window the cut-off source `XW` is the paper's source plus the frozen tail. -/
lemma wc_XW_eq (n : ℕ) {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) :
    XW n h s = Xi n h s + ∫ σ in wRight..(1 : ℝ), Theta n h s σ (baseState σ) := by
  rw [XW, cs_eq_one_of_mem hs, one_smul]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with σ hσ
  rw [Set.uIoc_of_le (le_of_lt wRight_lt_one)] at hσ
  rw [thetac, if_pos (lt_of_le_of_lt hs.2 hσ.1)]

/-- Right of the perturbation window the perturbed data agree with the unperturbed ones, so the
base identity holds for `h` as well. -/
lemma wc_base_volterra_right (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    Godd n h wRight (baseState wRight) =
      (∫ σ in wRight..(1 : ℝ), Theta n h wRight σ (baseState σ)) + Xi n h wRight := by
  have hz : ∀ x : ℝ, 1 - tau < x → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp hne
    have h9 : (1 : ℝ) - tau = 9 / 10 := by norm_num [tau]
    rw [h9] at hx hmem
    linarith [hmem.2]
  have hgt : 1 - tau < wRight := one_sub_tau_lt_wRight
  have hbase := Work.OddVolterra.Existence.base_volterra n hn wRight
    ⟨by norm_num [wRight], wRight_lt_one⟩
  have h1 := Work.OddVolterra.Existence.Godd_eq_of_gt n hz hgt (baseState wRight)
  have h2 := Work.OddVolterra.Existence.Xi_eq_of_gt n hz hgt
  have h3 : (∫ σ in wRight..(1 : ℝ), Theta n h wRight σ (baseState σ))
      = ∫ σ in wRight..(1 : ℝ), Theta n 0 wRight σ (baseState σ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    rw [Set.uIoc_of_le wRight_lt_one.le] at hσ
    exact Work.OddVolterra.Existence.Theta_eq_of_gt n hz hgt (lt_trans hgt hσ.1) (baseState σ)
  rw [h1, h2, h3]
  exact hbase

/-! ## The theorem -/

/-- **The truncated odd Volterra system on the window `[7/10, 19/20]`.**

For every `h` which is `C^∞` and `C^{n+2}`-small on the transition window
`[1 - 2τ, 1 - τ]` there is a continuous state curve `Z` on `[7/10, 19/20]`,
within `1/100` of the unperturbed state and equal to it at the right end, solving the
truncated odd Volterra equation. -/
theorem window_core_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(19 / 20 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              (Work.OddVolterra.Xi n h s +
                ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
                  Work.OddVolterra.Theta n h s σ (Work.OddVolterra.baseState σ))) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 100) ∧
        Z (19 / 20 : ℝ) = Work.OddVolterra.baseState (19 / 20 : ℝ) := by
  classical
  obtain ⟨hΘcont, L, hL0, hΘlip⟩ := TW2_regular n hn
  obtain ⟨Cg, C₃, hCg0, hC₃0, hdcl⟩ := GW2_fderiv_close_unif n hn
  obtain ⟨A, B, hB, hAspec, hAcont, hAb⟩ :=
    Work.OddVolterra.Existence.odd_linearization n hn wLeft wRight wLeft_pos wLeft_le_wRight
      (le_of_lt wRight_lt_one)
  set M₀ : ℝ := 2 + (wRight - wLeft) with hM₀def
  set lam : ℝ := 4 * B * L + 1 with hlamdef
  set EE : ℝ := Real.exp (lam * (wRight - wLeft)) with hEEdef
  have hEEpos : 0 < EE := by rw [hEEdef]; exact Real.exp_pos _
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; linarith [wLeft_le_wRight]
  have hden1 : 0 < 200 * B * M₀ * EE := by positivity
  have hden2 : 0 < 8 * B * (2 * B * Cg * M₀ * EE + 1) := by positivity
  set εeng : ℝ := min (1 / 100) (min (1 / (200 * B * M₀ * EE))
    (1 / (8 * B * (2 * B * Cg * M₀ * EE + 1)))) with hεengdef
  have hεengpos : 0 < εeng := by
    rw [hεengdef]
    exact lt_min (by norm_num) (lt_min (div_pos one_pos hden1) (div_pos one_pos hden2))
  obtain ⟨γ, hγ0, hγc⟩ := wc_GW2_close n hn εeng hεengpos
  obtain ⟨δΘ, hδΘ0, hδΘc⟩ := wc_TW2_close n hn εeng hεengpos
  obtain ⟨δΞ, hδΞ0, hδΞc⟩ := wc_XW_close n hn εeng hεengpos
  set δ₃ : ℝ := εeng / (C₃ + 1) with hδ₃def
  have hδ₃0 : 0 < δ₃ := by rw [hδ₃def]; positivity
  set e0 : ℝ := min (1 / 100) (min γ (min δΘ (min δΞ δ₃))) with he0def
  have he0pos : 0 < e0 := by
    rw [he0def]
    exact lt_min (by norm_num) (lt_min hγ0 (lt_min hδΘ0 (lt_min hδΞ0 hδ₃0)))
  have he0_100 : e0 ≤ 1 / 100 := by rw [he0def]; exact min_le_left _ _
  have he0_γ : e0 ≤ γ := by
    rw [he0def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have he0_δΘ : e0 ≤ δΘ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have he0_δΞ : e0 ≤ δΞ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have he0_δ₃ : e0 ≤ δ₃ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨e0, he0pos, ?_⟩
  intro h hh hsupp _hη hsmall _h0 _hne
  have hsm100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hsmall k hk s) he0_100
  have hsmγ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ γ :=
    fun k hk s => le_trans (hsmall k hk s) he0_γ
  have hsmδΘ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δΘ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δΘ
  have hsmδΞ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δΞ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δΞ
  have hsmδ₃ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ₃ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δ₃
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsm100 k (by omega) s
  have hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsm100 k (by omega) s
  -- the engine thresholds
  have hpos2 : 0 < 2 * B * M₀ * EE := by positivity
  have hεe100 : εeng ≤ 1 / 100 := min_le_left _ _
  have hεeden1 : εeng ≤ 1 / (200 * B * M₀ * EE) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hεeden2 : εeng ≤ 1 / (8 * B * (2 * B * Cg * M₀ * EE + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hε1 : εeng < 1 := by linarith [hεe100]
  have hε2 : εeng < 1 / (2 * B * M₀ * EE) :=
    lt_of_le_of_lt hεeden1 (by
      refine one_div_lt_one_div_of_lt hpos2 ?_
      nlinarith [hpos2])
  have hε3 : εeng < 1 / (4 * B * (2 * B * Cg * M₀ * EE + 1)) :=
    lt_of_le_of_lt hεeden2 (by
      have hpos : 0 < 4 * B * (2 * B * Cg * M₀ * EE + 1) := by positivity
      refine one_div_lt_one_div_of_lt hpos ?_
      nlinarith [hpos])
  -- engine hypotheses
  have hAspec' : ∀ s ∈ Set.Icc wLeft wRight,
      (A s : St →L[ℝ] St) = fderiv ℝ (fun z => GW2 n 0 s z) (baseState s) := by
    intro s hs
    rw [hAspec s hs]
    exact (wc_eventuallyEq_GW2_Godd (h := fun _ : ℝ => (0 : ℝ)) n hs).fderiv_eq.symm
  have hGcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => GW2 n h p.1 p.2) :=
    wc_GW2_contDiff n hh hsupp hsm1
  have hGcont : Continuous (fun p : ℝ × St => GW2 n h p.1 p.2) := hGcd.continuous
  have hΞcont : Continuous (XW n h) := XW_continuous n hn hh hsupp hsm100
  have hZ₀cont : ContinuousOn baseState (Set.Icc wLeft wRight) :=
    wdr_contDiff_baseState.continuous.continuousOn
  have hΘ0cont : Continuous (fun p : ℝ × ℝ × St => TW2 n 0 p.1 p.2.1 p.2.2) :=
    hΘcont (fun _ : ℝ => (0 : ℝ)) contDiff_const (fun x hx => absurd rfl hx)
      (fun k hk s => by simp)
  have hbase : ∀ s ∈ Set.Icc wLeft wRight,
      GW2 n 0 s (baseState s) =
        (∫ σ in s..wRight, TW2 n 0 s σ (baseState σ)) + XW n 0 s := wc_base_identity n hn
  have hΘcontinst : Continuous (fun p : ℝ × ℝ × St => TW2 n h p.1 p.2.1 p.2.2) :=
    hΘcont h hh hsupp hsm100
  have hΘlip' : ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) 1, ∀ z' ∈ Metric.closedBall (baseState σ) 1,
      ‖TW2 n h s σ z - TW2 n h s σ z'‖ ≤ L * ‖z - z'‖ :=
    hΘlip h hh hsupp hsm100
  have hdiff : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      DifferentiableAt ℝ (fun w => GW2 n h s w) z := by
    intro s hs z _hz
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => (s, w)) z := by fun_prop
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => GW2 n h s w) z := by
      have hc := (hGcd.contDiffAt).comp z h1
      have h' : (fun p : ℝ × St => GW2 n h p.1 p.2) ∘ (fun w : St => (s, w)) =
          fun w : St => GW2 n h s w := by funext w; rfl
      rwa [h'] at hc
    exact h2.differentiableAt (by simp)
  have hΞc : ∀ s ∈ Set.Icc wLeft wRight, dist (XW n h s) (XW n 0 s) < εeng :=
    hδΞc h hh hsupp hsmδΞ
  have hGc : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      dist (GW2 n h s z) (GW2 n 0 s z) < εeng := hγc h hh hsupp hsmγ
  have hΘc : ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) 1,
      dist (TW2 n h s σ z) (TW2 n 0 s σ z) < εeng := hδΘc h hh hsupp hsmδΘ
  have hδ₃_le : δ₃ ≤ 1 / 100 := by
    rw [hδ₃def]
    refine le_trans (div_le_self hεengpos.le (by linarith [hC₃0])) ?_
    exact hεe100
  have hder : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      ‖fderiv ℝ (fun w => GW2 n h s w) z - (A s : St →L[ℝ] St)‖
        ≤ Cg * ‖z - baseState s‖ + εeng := by
    intro s hs z hz
    have h1 := hdcl δ₃ hδ₃0 hδ₃_le h hh hsupp hsmδ₃ s hs z hz
    rw [hAspec' s hs]
    have hle : C₃ * δ₃ ≤ εeng := by
      have hC3p : (0 : ℝ) < C₃ + 1 := by linarith [hC₃0]
      have h2 : (C₃ + 1) * δ₃ = εeng := by
        rw [hδ₃def, mul_comm, div_mul_cancel₀ _ (ne_of_gt hC3p)]
      have hmono : C₃ * δ₃ ≤ (C₃ + 1) * δ₃ :=
        mul_le_mul_of_nonneg_right (by linarith [hC₃0]) hδ₃0.le
      linarith [hmono, h2]
    linarith
  obtain ⟨Z, hZc, hZsolve, hZd⟩ :=
    Work.VolterraLong.volterra_long_exists_eps (E := St) (a := wLeft) (b := wRight)
      wLeft_le_wRight A (fun s z => GW2 n 0 s z) (fun s z => GW2 n h s z)
      (fun s σ z => TW2 n 0 s σ z) (fun s σ z => TW2 n h s σ z)
      (XW n 0) (XW n h) baseState
      hB hL0 hCg0 hAspec' hAcont hAb hGcont hΘcontinst hΞcont hZ₀cont hΘ0cont hbase hΘlip'
      hdiff lam M₀ EE hlamdef hM₀def hEEdef
      hεengpos hε1 hε2 hε3 hΞc hGc hΘc hder
  -- the conclusion
  have hZd' : ∀ s ∈ Set.Icc wLeft wRight, dist (Z s) (baseState s) ≤ 1 / 100 := by
    intro s hs
    have hk : (2 * B * M₀ * EE) * (1 / (200 * B * M₀ * EE)) = 1 / 100 := by
      have hne : (200 * B * M₀ * EE) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    calc dist (Z s) (baseState s) ≤ 2 * B * M₀ * EE * εeng := hZd s hs
      _ ≤ (2 * B * M₀ * EE) * (1 / (200 * B * M₀ * EE)) :=
          mul_le_mul_of_nonneg_left hεeden1 hpos2.le
      _ = 1 / 100 := hk
  have hZdist : ∀ s ∈ Set.Icc wLeft wRight, ‖Z s - baseState s‖ ≤ 1 / 100 := by
    intro s hs
    rw [← dist_eq_norm]
    exact hZd' s hs
  have hZeq : ∀ s ∈ Set.Icc wLeft wRight,
      Godd n h s (Z s) = (∫ σ in s..wRight, Theta n h s σ (Z σ)) +
        (Xi n h s + ∫ σ in wRight..(1 : ℝ), Theta n h s σ (baseState σ)) := by
    intro s hs
    have hZs := hZsolve s hs
    dsimp only at hZs
    rw [wc_GW2_eq_Godd_of_close n hs (hZdist s hs), wc_XW_eq n hs] at hZs
    have hint : (∫ σ in s..wRight, TW2 n h s σ (Z σ))
        = ∫ σ in s..wRight, Theta n h s σ (Z σ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with σ hσ
      rw [Set.uIoc_of_le hs.2] at hσ
      have hσw : σ ∈ Set.Icc wLeft wRight := ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
      exact wc_TW2_eq_Theta_of_close n hs hσw hσ.1 (hZdist σ hσw)
    rw [hint] at hZs
    exact hZs
  have hend : Z wRight = baseState wRight := by
    have hwmem : wRight ∈ Set.Icc wLeft wRight := ⟨wLeft_le_wRight, le_rfl⟩
    have h1 := hZeq wRight hwmem
    rw [intervalIntegral.integral_same, zero_add] at h1
    have h2 : Xi n h wRight + (∫ σ in wRight..(1 : ℝ), Theta n h wRight σ (baseState σ))
        = Godd n h wRight (baseState wRight) :=
      (add_comm _ _).trans (wc_base_volterra_right n hn hsupp).symm
    rw [h2] at h1
    obtain ⟨c, hc0, hcinj⟩ :=
      Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsm2
        wRight_pos (le_of_lt wRight_lt_one)
    have hZin : Z wRight ∈ Metric.closedBall (baseState wRight) (1 / 2) := by
      rw [Metric.mem_closedBall]
      exact le_trans (hZd' wRight hwmem) (by norm_num)
    have hBin : baseState wRight ∈ Metric.closedBall (baseState wRight) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_self]; norm_num
    have h3 := hcinj wRight ⟨le_refl wRight, le_of_lt wRight_lt_one⟩ (Z wRight) hZin
      (baseState wRight) hBin
    rw [h1, sub_self, norm_zero] at h3
    have h4 : ‖Z wRight - baseState wRight‖ = 0 :=
      le_antisymm (by nlinarith [hc0, norm_nonneg (Z wRight - baseState wRight), h3])
        (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  exact ⟨Z, hZc, hZeq, hZd', hend⟩

end

end Work.OddVolterra.Window
