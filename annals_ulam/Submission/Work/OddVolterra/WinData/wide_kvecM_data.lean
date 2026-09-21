import Mathlib
import Submission.Work.OddVolterra.WinData.wide_defs
import Submission.Work.OddVolterra.WinData.kjet_mem_boxW_deriv
import Submission.Work.OddVolterra.WinData.wide_kjet_lipschitz
import Submission.Work.OddVolterra.WinData.state_ball_bounds
import Submission.Work.OddVolterra.Window.KvecJet_smooth
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.Window.fed_kvecM_defs

/-!
# The wide state data of the manifest kernel vector `KvecM`

`KvecMDataW n M C` (the wide analogue of `Work.Window.fedKvecMData`: the same four inequalities,
but on the square `a, σ ∈ [1/4, 19/20]` instead of `[7/10, 19/20]`) holds for suitable constants.

The proof is the proof of `Work.Window.fed_kvecM_data` with the narrow jet box `KJbox` replaced by
the wide box `KJboxW`, the narrow radicand data by `krad_jets_ext` (inside
`WinData.kjet_mem_boxW_deriv`) and the narrow state-Lipschitz of the jet curve by
`WinData.kjet_state_lipschitz_wide`.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra
open Work.OddVolterra.Window

noncomputable section

/-- **Uniform (in `h`) value, state-Lipschitz and first-slot-derivative data of `KvecM` on the
wide slope square.** -/
theorem kvecM_data_wide (n : ℕ) (hn : 1 ≤ n) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ KvecMDataW n M C := by
  have _ : 1 ≤ n := hn
  obtain ⟨Kj, hKjnn, hKj⟩ := kjet_state_lipschitz_wide n hn
  obtain ⟨C1, hC1nn, hC1⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => KF1 n v) (isOpen_KJopen n)
    (convex_KJboxW n (KJbz n)) (isCompact_KJboxW n (KJbz n)) (KJboxW_subset_KJopen n (KJbz n))
    (KvecJet_smooth n).1 (KJbz_nonneg n)
  obtain ⟨C2, hC2nn, hC2⟩ := JetCurve_box (E := KJIx n → ℝ) (fun v => fedPhi2 n v) (isOpen_KJopen n)
    (convex_KJboxW n (KJbz n)) (isCompact_KJboxW n (KJbz n)) (KJboxW_subset_KJopen n (KJbz n))
    (fed_contDiffOn_Phi2 n) (KJbz_nonneg n)
  have hCn : 0 ≤ max C1 C2 := le_max_of_le_left hC1nn
  have hKF1diff : ∀ v ∈ KJboxW n (KJbz n),
      DifferentiableAt ℝ (fun v : KJIx n → ℝ => KF1 n v) v :=
    fun v hv => ((KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJboxW_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  have hPhi2diff : ∀ v ∈ KJboxW n (KJbz n),
      DifferentiableAt ℝ (fun v : KJIx n → ℝ => fedPhi2 n v) v :=
    fun v hv => ((fed_contDiffOn_Phi2 n).contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJboxW_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  refine ⟨max C1 C2 * Kj, max C1 C2, by positivity, hCn, ?_⟩
  intro h hh hsupp hjet a ha σ hσ z hz z' hz'
  -- ## the state data of the two points
  obtain ⟨hz0, hz1, hz2⟩ := state_ball_bounds (a := 1 / 4) (b := 1) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (⟨hσ.1, by linarith [hσ.2]⟩ : σ ∈ Set.Icc (1 / 4 : ℝ) 1) hz
  obtain ⟨hz'0, hz'1, hz'2⟩ := state_ball_bounds (a := 1 / 4) (b := 1) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (⟨hσ.1, by linarith [hσ.2]⟩ : σ ∈ Set.Icc (1 / 4 : ℝ) 1) hz'
  have ha9 : a ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hσ9 : σ ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨hσ.1, by linarith [hσ.2]⟩
  have hjet' : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hjet k hk s
  -- ## the jet data, for an arbitrary state of the ball
  have jetdata : ∀ w : St, (1 / 5 : ℝ) ≤ w 0 → (1 / 5 : ℝ) ≤ w 1 →
      (∀ i : Fin 4, |w i| ≤ 2) →
      KJet n h σ w a ∈ KJboxW n (KJbz n) ∧
      ‖deriv (fun u : ℝ => KJet n h σ w u) a‖ ≤ KJbz n :=
    fun w hw0 hw1 hw => kjet_mem_boxW_deriv n hh hsupp hjet' hσ hw0 hw1 hw ha
  obtain ⟨hmemZ, hderZ⟩ := jetdata z hz0 hz1 hz2
  obtain ⟨hmemZ', hderZ'⟩ := jetdata z' hz'0 hz'1 hz'2
  -- ## the jet curves and their state-Lipschitz data
  have hcdZ : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := contDiff_KJet n hh σ z
  have hcdZ' : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z' u) := contDiff_KJet n hh σ z'
  have hlip := hKj h hh hjet' σ hσ9 z z' hz0 hz1 hz2 hz'0 hz'1 hz'2 a ha9
  have hδnn : 0 ≤ Kj * ‖z - z'‖ := mul_nonneg hKjnn (norm_nonneg _)
  -- ## `JetCurve_box` for the two components of the jet vector
  have hJ1 := hC1 (fun u : ℝ => KJet n h σ z u) (fun u : ℝ => KJet n h σ z' u) a
    (Kj * ‖z - z'‖) hδnn hcdZ hcdZ' hmemZ hmemZ' hderZ hderZ' hlip.1 hlip.2
  have hJ2 := hC2 (fun u : ℝ => KJet n h σ z u) (fun u : ℝ => KJet n h σ z' u) a
    (Kj * ‖z - z'‖) hδnn hcdZ hcdZ' hmemZ hmemZ' hderZ hderZ' hlip.1 hlip.2
  obtain ⟨hA1, -, hE1, -, hG1, hH1⟩ := hJ1
  obtain ⟨hA2, -, hE2, -, hG2, hH2⟩ := hJ2
  -- ## constants
  have hC1le : C1 ≤ max C1 C2 := le_max_left _ _
  have hC2le : C2 ≤ max C1 C2 := le_max_right _ _
  have hM1 : C1 * (Kj * ‖z - z'‖) ≤ (max C1 C2 * Kj) * ‖z - z'‖ := by
    calc C1 * (Kj * ‖z - z'‖) = (C1 * Kj) * ‖z - z'‖ := by ring
      _ ≤ (max C1 C2 * Kj) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hKjnn) (norm_nonneg _)
  have hM2 : C2 * (Kj * ‖z - z'‖) ≤ (max C1 C2 * Kj) * ‖z - z'‖ := by
    calc C2 * (Kj * ‖z - z'‖) = (C2 * Kj) * ‖z - z'‖ := by ring
      _ ≤ (max C1 C2 * Kj) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hKjnn) (norm_nonneg _)
  -- ## differentiability of the two rows along the two jet curves
  have hdiffZ : ∀ i : Fin 2, DifferentiableAt ℝ (fun u : ℝ => fedKJrow n h σ z u i) a := by
    intro i
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0]
      exact (hKF1diff _ hmemZ).comp a ((hcdZ.differentiable (by simp)).differentiableAt)
    · rw [h1]
      exact (hPhi2diff _ hmemZ).comp a ((hcdZ.differentiable (by simp)).differentiableAt)
  have hdiffZ' : ∀ i : Fin 2, DifferentiableAt ℝ (fun u : ℝ => fedKJrow n h σ z' u i) a := by
    intro i
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0]
      exact (hKF1diff _ hmemZ').comp a ((hcdZ'.differentiable (by simp)).differentiableAt)
    · rw [h1]
      exact (hPhi2diff _ hmemZ').comp a ((hcdZ'.differentiable (by simp)).differentiableAt)
  have hderZrow : deriv (fun u : ℝ => fedKJrow n h σ z u) a
      = fun i => deriv (fun u : ℝ => fedKJrow n h σ z u i) a :=
    deriv_pi (𝕜 := ℝ) (x := a) (φ := fun u : ℝ => fedKJrow n h σ z u) hdiffZ
  have hderZ'row : deriv (fun u : ℝ => fedKJrow n h σ z' u) a
      = fun i => deriv (fun u : ℝ => fedKJrow n h σ z' u i) a :=
    deriv_pi (𝕜 := ℝ) (x := a) (φ := fun u : ℝ => fedKJrow n h σ z' u) hdiffZ'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the value bound
    rw [pi_norm_le_iff_of_nonneg hCn]
    intro i
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0, fedKvecM_row0 n hh a σ z, Real.norm_eq_abs]
      exact le_trans hA1 hC1le
    · rw [h1, fedKvecM_row1 n hh a σ z, Real.norm_eq_abs]
      exact le_trans hA2 hC2le
  · -- the value Lipschitz bound
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0, Pi.sub_apply, fedKvecM_row0 n hh a σ z, fedKvecM_row0 n hh a σ z', Real.norm_eq_abs]
      exact le_trans hG1 hM1
    · rw [h1, Pi.sub_apply, fedKvecM_row1 n hh a σ z, fedKvecM_row1 n hh a σ z', Real.norm_eq_abs]
      exact le_trans hG2 hM2
  · -- the `a`-derivative bound
    rw [fedKvecM_eq_row n hh σ z, pi_norm_le_iff_of_nonneg hCn]
    intro i
    rw [hderZrow]
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0, Real.norm_eq_abs]
      exact le_trans hE1 hC1le
    · rw [h1, Real.norm_eq_abs]
      exact le_trans hE2 hC2le
  · -- the `a`-derivative Lipschitz bound
    rw [fedKvecM_eq_row n hh σ z, fedKvecM_eq_row n hh σ z']
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply, hderZrow, hderZ'row]
    rcases fed_fin2_cases i with h0 | h1
    · rw [h0, Real.norm_eq_abs]
      exact le_trans hH1 hM1
    · rw [h1, Real.norm_eq_abs]
      exact le_trans hH2 hM2
  · -- the componentwise `a`-derivative bound
    intro j
    cases fed_fin2_cases j with
    | inl h0 =>
      subst h0
      have hrow : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 0)
          = fun u : ℝ => KF1 n (KJet n h σ z u) := funext fun u => fedKvecM_row0 n hh u σ z
      rw [hrow, Real.norm_eq_abs]
      exact le_trans hE1 hC1le
    | inr h1 =>
      subst h1
      have hrow : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 1)
          = fun u : ℝ => fedPhi2 n (KJet n h σ z u) := funext fun u => fedKvecM_row1 n hh u σ z
      rw [hrow, Real.norm_eq_abs]
      exact le_trans hE2 hC2le
  · -- the componentwise `a`-derivative state-Lipschitz bound
    intro j
    cases fed_fin2_cases j with
    | inl h0 =>
      subst h0
      have hrow : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 0)
          = fun u : ℝ => KF1 n (KJet n h σ z u) := funext fun u => fedKvecM_row0 n hh u σ z
      have hrow' : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0)
          = fun u : ℝ => KF1 n (KJet n h σ z' u) := funext fun u => fedKvecM_row0 n hh u σ z'
      rw [hrow, hrow', Real.norm_eq_abs]
      exact le_trans hH1 hM1
    | inr h1 =>
      subst h1
      have hrow : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 1)
          = fun u : ℝ => fedPhi2 n (KJet n h σ z u) := funext fun u => fedKvecM_row1 n hh u σ z
      have hrow' : (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1)
          = fun u : ℝ => fedPhi2 n (KJet n h σ z' u) := funext fun u => fedKvecM_row1 n hh u σ z'
      rw [hrow, hrow', Real.norm_eq_abs]
      exact le_trans hH2 hM2

end

end Work.OddVolterra.WinData
