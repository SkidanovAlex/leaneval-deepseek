import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.wdc_aux
import Submission.Work.OddVolterra.WinData.deriv2_main
import Submission.Work.OddVolterra.WinData.deriv2_core
import Submission.Work.OddVolterra.WinData.deriv2_hkv
import Submission.Work.OddVolterra.WinData.thetaM_deriv_close_ext
import Submission.Work.Anchor.ThetaM_contDiffOn_wide
import Submission.Work.OddVolterra.WinData.xi_deriv_close
import Submission.Work.Anchor.Xi_close
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec
import Submission.Work.OddExistence.Manifest.thetaM_lipschitz
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.Existence.frozen_tail_lipschitz

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-!
# Closeness of the derivative of the clamped source

`XsCl n h s` is the `s`-derivative of the clamped source `WinData.Xcl n h`.  On the slope window
`[7/10, 19/20]` the clamp `wChiX = wCs` equals `1` and is locally constant, so

`XsCl n h s = ∂_s (Ξ n h + ∫_σ in 19/20..1, 𝚯M n h s σ (baseState σ))`.

The claim is the `O(δ)`-closeness of this derivative to its value at `h = 0`: the `Ξ` part is
`WinData.xi_deriv_close`, and the frozen-tail part is controlled by
`Existence.frozen_tail_lipschitz` (which uses `thetaM_deriv_close_ext` for the pointwise
`∂_u`-bound together with the mean value theorem).

The endpoint `s = 19/20` is handled by continuity of `XsCl`: the estimate is proved on the open
window `(7/10, 19/20)`, and the set where it holds is closed, hence contains its closure.
-/

/-- On the slope window `[7/10, 19/20]` the clamped source-derivative is that of the paper's
source plus the frozen tail. -/
private lemma xsCl_eq_frozen (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Ioo (7 / 10 : ℝ) (19 / 20)) :
    XsCl n h s = deriv (fun u : ℝ => Work.OddVolterra.Xi n h u +
      ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ)) s :=
  xsCl_eq hn hh hsupp h1 (show s ∈ Set.Ioo (1 / 4 : ℝ) (19 / 20) from
    ⟨by linarith [hs.1], hs.2⟩)

theorem xscl_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ CX : ℝ, 0 ≤ CX ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        ‖Work.OddVolterra.Existence.XsCl n h s - Work.OddVolterra.Existence.XsCl n 0 s‖ ≤ CX * δ := by
  obtain ⟨C1, hC1nn, hxi⟩ := Work.OddVolterra.WinData.xi_deriv_close n hn
  obtain ⟨C3, hC3nn, htail⟩ := frozen_tail_lipschitz n hn
  refine ⟨C1 + C3 + 1, by positivity, ?_⟩
  intro h δ hh hδpos hδ100 hjet hsupp
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 :=
    fun k hk t => le_trans (hjet k (by omega) t) hδ100
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) t| ≤ 1 / 100 := by
    intro k hk t
    have h0 : iteratedDeriv k (0 : ℝ → ℝ) t = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [h0, abs_zero]; norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx; rw [Function.mem_support] at hx; exact absurd rfl hx
  -- the estimate on the open window
  have hcore : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) (19 / 20),
      ‖XsCl n h s - XsCl n 0 s‖ ≤ (C1 + C3 + 1) * δ := by
    intro s hs
    have hs75 : (7 / 10 : ℝ) < s := hs.1
    have hs1920 : s < 19 / 20 := hs.2
    have hs14 : (1 / 4 : ℝ) < s := by linarith
    have hs8 : (1 / 8 : ℝ) < s := by linarith
    have hs1 : s < 1 := by linarith
    have hsIoo : s ∈ Set.Ioo (1 / 4 : ℝ) (19 / 20) := ⟨hs14, hs1920⟩
    have hsIcc : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := ⟨le_of_lt hs14, le_of_lt hs1920⟩
    have hmid : s ∈ Set.Ioo (1 / 8 : ℝ) (99 / 100) := ⟨hs8, by linarith⟩
    -- the two frozen tails
    set Th : ℝ → Work.OddVolterra.St := fun u : ℝ =>
      ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ) with hTh
    set T0 : ℝ → Work.OddVolterra.St := fun u : ℝ =>
      ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n 0 u σ (Work.OddVolterra.baseState σ) with hT0
    have hdTh : DifferentiableAt ℝ Th s := by
      rw [hTh]
      exact ((Work.OddVolterra.WinData.thetaM_tail_contDiffOn n hh hsupp hsmall1).contDiffAt
        (isOpen_Ioo.mem_nhds hmid)).differentiableAt (by simp)
    have hdT0 : DifferentiableAt ℝ T0 s := by
      rw [hT0]
      exact ((Work.OddVolterra.WinData.thetaM_tail_contDiffOn n contDiff_const hsupp0 hsmall0).contDiffAt
        (isOpen_Ioo.mem_nhds hmid)).differentiableAt (by simp)
    -- the `Ξ`-part
    have hdXh : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.Xi n h u) s :=
      differentiableAt_pi.mpr (fun i =>
        Work.OddVolterra.WinData.differentiableAt_Xi_component n hn hh hsupp hsmall1 hs8 hs1 i)
    have hdX0 : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s :=
      differentiableAt_pi.mpr (fun i =>
        Work.OddVolterra.WinData.differentiableAt_Xi_component n hn contDiff_const hsupp0 hsmall0
          hs8 hs1 i)
    -- the model identity for the clamped source
    have hXh : XsCl n h s = deriv (fun u : ℝ => Work.OddVolterra.Xi n h u + Th u) s := by
      rw [hTh]
      exact xsCl_eq_frozen n hn hh hsupp hsmall1 hs
    have hX0 : XsCl n 0 s = deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u + T0 u) s := by
      rw [hT0]
      exact xsCl_eq_frozen n hn contDiff_const hsupp0 hsmall0 hs
    have hsplit_h : deriv (fun u : ℝ => Work.OddVolterra.Xi n h u + Th u) s
        = deriv (fun u : ℝ => Work.OddVolterra.Xi n h u) s + deriv Th s :=
      deriv_add hdXh hdTh
    have hsplit_0 : deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u + T0 u) s
        = deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s + deriv T0 s :=
      deriv_add hdX0 hdT0
    have hkey : XsCl n h s - XsCl n 0 s
        = (deriv (fun u : ℝ => Work.OddVolterra.Xi n h u) s
            - deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s)
          + (deriv Th s - deriv T0 s) := by
      rw [hXh, hX0, hsplit_h, hsplit_0]
      abel
    -- the `Ξ`-bound
    have h1b : ‖deriv (fun u : ℝ => Work.OddVolterra.Xi n h u) s
        - deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s‖ ≤ C1 * δ :=
      hxi h δ hh hδpos hδ100 hjet hsupp s hsIcc
    -- the frozen-tail bound
    have h2b : ‖deriv Th s - deriv T0 s‖ ≤ C3 * δ := by
      have hsub : deriv (fun u : ℝ => Th u - T0 u) s = deriv Th s - deriv T0 s :=
        deriv_sub hdTh hdT0
      rw [← hsub]
      refine norm_deriv_le_of_lip' (C := C3 * δ) (by positivity) ?_
      filter_upwards [Icc_mem_nhds (by linarith : (7 / 10 : ℝ) < s) hs1920] with u hu
      have hb := htail h δ hh hδpos hδ100 hjet hsupp u hu s
        ⟨le_of_lt hs75, le_of_lt hs1920⟩
      have heq : (Th u - T0 u) - (Th s - T0 s)
          = ((∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
                Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ))
              - (∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
                Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ)))
            - ((∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
                Work.OddVolterra.KernelExt.ThetaM n 0 u σ (Work.OddVolterra.baseState σ))
              - (∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
                Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ))) := by
        simp only [hTh, hT0]
        abel
      rw [heq]
      simpa [Real.norm_eq_abs] using hb
    rw [hkey]
    refine le_trans (norm_add_le _ _) ?_
    have hfin : ‖deriv (fun u : ℝ => Work.OddVolterra.Xi n h u) s
          - deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s‖
        + ‖deriv Th s - deriv T0 s‖ ≤ (C1 + C3 + 1) * δ := by
      have hle : C1 * δ + C3 * δ ≤ (C1 + C3 + 1) * δ := by nlinarith
      linarith
    exact hfin
  -- extend to the closed window by continuity
  have hcont : Continuous (fun s : ℝ => ‖XsCl n h s - XsCl n 0 s‖) :=
    ((xsCl_continuous hn hh hsupp hsmall1).sub
      (xsCl_continuous hn contDiff_const hsupp0 hsmall0)).norm
  have hclosed : IsClosed {s : ℝ | ‖XsCl n h s - XsCl n 0 s‖ ≤ (C1 + C3 + 1) * δ} :=
    isClosed_Iic.preimage hcont
  have hcl := hclosed.closure_subset_iff.mpr hcore
  intro s hs
  exact hcl (by rw [closure_Ioo (by norm_num : (7 / 10 : ℝ) ≠ 19 / 20)]; exact hs)

end

end Work.OddVolterra.Existence
