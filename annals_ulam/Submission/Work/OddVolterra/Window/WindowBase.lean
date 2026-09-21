import Mathlib
import Submission.Work.OddVolterra.Window.WindowFed
import Submission.Work.OddVolterra.Existence.base_volterra

/-!
# The base identity for the cut-off window data

The unperturbed (ball) state `baseState` solves the *truncated* odd Volterra system of the window
core with the cut-off data `GoddW`, `ThetaW` and the frozen-tail source `XiW`: this is the
`hbase` hypothesis of the long-interval fixed point engine.

The proof compares the cut-off data with the paper's raw data: on the window the cut-offs are `1`,
the manifest kernel agrees with the paper's kernel for `σ > s` (`ThetaM_eq_Theta`, whose radicand
positivity holds on our region by `krad_pos_of_region`), and the paper's system is solved by
`baseState` on `(0,1)` (`Existence.base_volterra`).  The only points where the two integrands
differ are the diagonal points `σ = s`, which are negligible.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

set_option maxHeartbeats 1000000

/-- `profileX σ ≥ 7/10` on the window extended to `[wA, 1]`. -/
lemma seven_tenths_le_profileX_window {σ : ℝ}
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA 1) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ := by
  have hσ0 : 0 ≤ σ := le_trans (le_of_lt Work.OddVolterra.Existence.wA_pos) hσ.1
  exact seven_tenths_le_profileX hσ0 hσ.2

/-- States within `1/2` of `baseState σ` (`σ` in the window) have `z 0 ≥ 1/5`. -/
lemma one_fifth_le_of_close_base_wide {σ z0 : ℝ}
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA 1)
    (hz : |z0 - Commons.Geometry.Ulam.profileX σ| ≤ 1 / 2) :
    (1 / 5 : ℝ) ≤ z0 := by
  have h1 := seven_tenths_le_profileX_window hσ
  linarith [(abs_le.mp hz).1]

/-- Radicand positivity on the window, for the moving slot `a ∈ [s-1, σ]`. -/
lemma krad_pos_window {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ a t : ℝ} (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA 1)
    (ha : a ∈ Set.Icc (s - 1) σ) (ht : 1 / 5 ≤ |t|) :
    0 < Work.OddVolterra.krad h σ t a := by
  refine krad_pos_of_region hsmall ?_ ht
  have hs1 : (7 : ℝ) / 10 ≤ s := by
    have h := hs.1
    rw [Work.OddVolterra.Existence.wA_eq, Work.OddVolterra.tau] at h
    linarith
  have hσ1 : (7 : ℝ) / 10 ≤ σ := by
    have h := hσ.1
    rw [Work.OddVolterra.Existence.wA_eq, Work.OddVolterra.tau] at h
    linarith
  linarith [ha.1]

/-- On the window, `ThetaM` agrees with the paper's `Theta` for `σ > s`, for states in the ball
of radius `1/2` around `baseState σ`. -/
lemma ThetaM_eq_Theta_of_window {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC)
    (hσ : σ ∈ Set.Icc Work.OddVolterra.Existence.wA 1)
    (hlt : s < σ) {z : Work.OddVolterra.St}
    (hz : ‖z - Work.OddVolterra.baseState σ‖ ≤ 1 / 2) :
    Work.OddVolterra.KernelExt.ThetaM n h s σ z = Work.OddVolterra.Theta n h s σ z := by
  have hz0 : (1 / 5 : ℝ) ≤ z 0 := by
    have h2 : |z 0 - Commons.Geometry.Ulam.profileX σ| ≤ 1 / 2 := by
      have h := norm_le_pi_norm (z - Work.OddVolterra.baseState σ) 0
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      rw [show Work.OddVolterra.baseState σ 0 = Commons.Geometry.Ulam.profileX σ from rfl] at h
      linarith
    exact one_fifth_le_of_close_base_wide hσ h2
  have hz1 : (1 / 5 : ℝ) ≤ z 1 := by
    have h2 : |z 1 - Commons.Geometry.Ulam.profileX σ| ≤ 1 / 2 := by
      have h := norm_le_pi_norm (z - Work.OddVolterra.baseState σ) 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      rw [show Work.OddVolterra.baseState σ 1 = Commons.Geometry.Ulam.profileX σ from rfl] at h
      linarith
    exact one_fifth_le_of_close_base_wide hσ h2
  refine Work.OddVolterra.Window.ThetaM_eq_Theta n hn hh hlt (δ := 1) (by norm_num) z ?_ ?_
  · intro a ha
    refine krad_pos_window hsmall hs hσ ⟨by linarith [ha.1], ha.2⟩ ?_
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < z 0)]
    exact hz0
  · intro a ha
    refine krad_pos_window hsmall hs hσ ⟨by linarith [ha.1], ha.2⟩ ?_
    rw [abs_of_pos (by linarith : (0:ℝ) < z 1)]
    exact hz1

/-- **The base identity** of the truncated window system: the ball's state solves the system with
the cut-off data and the frozen-tail source. -/
theorem fed_base_identity (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Icc Work.OddVolterra.Existence.wA Work.OddVolterra.Existence.wC,
      Work.OddVolterra.Existence.GoddW n (fun _ : ℝ => 0) s (Work.OddVolterra.baseState s) =
        (∫ σ in s..Work.OddVolterra.Existence.wC,
            Work.OddVolterra.Existence.ThetaW n (fun _ : ℝ => 0) s σ
              (Work.OddVolterra.baseState σ)) +
          Work.OddVolterra.Existence.XiW n (fun _ : ℝ => 0) s := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le Work.OddVolterra.Existence.wA_pos hs.1
  have hsC : s ≤ Work.OddVolterra.Existence.wC := hs.2
  have hwC1 : Work.OddVolterra.Existence.wC ≤ 1 := le_of_lt Work.OddVolterra.Existence.wC_lt_one
  have hs1 : s < 1 := lt_of_le_of_lt hsC Work.OddVolterra.Existence.wC_lt_one
  have hsmallzf : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) s| ≤ 1 / 100 := by
    intro k hk s
    rw [iteratedDeriv_const]
    split_ifs <;> norm_num
  -- the paper's system at the base state
  have hraw : Work.OddVolterra.Godd n (fun _ : ℝ => 0) s (Work.OddVolterra.baseState s) =
      (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ
          (Work.OddVolterra.baseState σ)) + Work.OddVolterra.Xi n (fun _ : ℝ => 0) s :=
    Work.OddVolterra.Existence.base_volterra n hn s ⟨hs0, hs1⟩
  -- the left-hand side is the paper's `Godd`
  have hL : Work.OddVolterra.Existence.GoddW n (fun _ : ℝ => 0) s
        (Work.OddVolterra.baseState s)
      = Work.OddVolterra.Godd n (fun _ : ℝ => 0) s (Work.OddVolterra.baseState s) := by
    rw [Work.OddVolterra.Existence.GoddW]
    rw [chiG_eq_one_of_mem hs (by simp [Work.OddVolterra.baseState])]
    rw [one_smul, Work.OddVolterra.Window.GoddM_eq_Godd n contDiff_const s]
  -- integrability of the paper's `Θ`-integrand at the base state
  have hint := Work.OddVolterra.Existence.theta_integrable n hn contDiff_const
    Work.OddVolterra.Existence.isEnvelopeCurve_base
    (fun s hs hs1 => Work.OddVolterra.Existence.base_momentF n hs hs1)
    (fun s hs hs1 => Work.OddVolterra.Existence.base_momentH n hs hs1)
    Work.OddVolterra.Existence.base_close
  have hint1 : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ
        (Work.OddVolterra.baseState σ)) volume s 1 :=
    hint s ⟨hs0, hs1⟩
  have hsc : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ
        (Work.OddVolterra.baseState σ)) volume s Work.OddVolterra.Existence.wC :=
    hint1.mono_set (by
      rw [Set.uIcc_of_le hsC, Set.uIcc_of_le (le_trans hsC hwC1)]
      exact Set.Icc_subset_Icc le_rfl hwC1)
  have hc1 : IntervalIntegrable
      (fun σ : ℝ => Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ
        (Work.OddVolterra.baseState σ)) volume Work.OddVolterra.Existence.wC 1 :=
    hint1.mono_set (by
      rw [Set.uIcc_of_le hwC1, Set.uIcc_of_le (le_trans hsC hwC1)]
      exact Set.Icc_subset_Icc hsC le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hsc hc1
  -- the two `Θ`-integrals agree
  have hInt : (∫ σ in s..Work.OddVolterra.Existence.wC,
        Work.OddVolterra.Existence.ThetaW n (fun _ : ℝ => 0) s σ
          (Work.OddVolterra.baseState σ))
      = ∫ σ in s..Work.OddVolterra.Existence.wC,
          Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ (Work.OddVolterra.baseState σ) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hsC fun σ hσ => ?_
    have hlt : s < σ := hσ.1
    rw [Work.OddVolterra.Existence.ThetaW,
      chiT_eq_one_of_mem hs ⟨le_trans hs.1 (le_of_lt hσ.1), le_of_lt hσ.2⟩
        (by simp [Work.OddVolterra.baseState]), one_smul]
    exact ThetaM_eq_Theta_of_window (s := s) (σ := σ) hn contDiff_const hsmallzf hs
      ⟨le_trans hs.1 (le_of_lt hlt), le_of_lt (lt_of_lt_of_le hσ.2 hwC1)⟩ hlt
      (by simp [Work.OddVolterra.baseState])
  -- the sources agree
  have hXi : Work.OddVolterra.Existence.XiW n (fun _ : ℝ => 0) s
      = Work.OddVolterra.Xi n (fun _ : ℝ => 0) s +
        ∫ σ in Work.OddVolterra.Existence.wC..(1 : ℝ),
          Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ (Work.OddVolterra.baseState σ) := by
    rw [Work.OddVolterra.Existence.XiW,
      Work.OddVolterra.Existence.cs_one (abs_sub_wCenter_le_of_mem hs), one_smul]
    have hTail : (∫ σ in Work.OddVolterra.Existence.wC..(1 : ℝ),
          Work.OddVolterra.KernelExt.ThetaM n (fun _ : ℝ => 0) s σ
            (Work.OddVolterra.baseState σ))
        = ∫ σ in Work.OddVolterra.Existence.wC..(1 : ℝ),
            Work.OddVolterra.Theta n (fun _ : ℝ => 0) s σ (Work.OddVolterra.baseState σ) := by
      refine intervalIntegral.integral_congr_Ioo_of_le hwC1 fun σ hσ => ?_
      have hlt : s < σ := lt_of_le_of_lt hsC hσ.1
      exact ThetaM_eq_Theta_of_window (s := s) (σ := σ) hn contDiff_const hsmallzf hs
        ⟨le_trans hs.1 (le_of_lt hlt), le_of_lt hσ.2⟩ hlt
        (by simp [Work.OddVolterra.baseState])
    rw [hTail]
  rw [hL, hraw, hInt, hXi, ← hsplit]
  ring

end

end Work.OddVolterra.Window
