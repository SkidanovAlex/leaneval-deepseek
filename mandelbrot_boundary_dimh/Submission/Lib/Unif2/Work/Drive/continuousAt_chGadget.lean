import Mathlib
import Submission.Lib.Unif2.Work.Drive.chartGadget
import Submission.Lib.Unif2.Work.Drive.continuousAt_gadget

/-!
# Continuity of the transfer gadget attached to a *chosen* chart family

This is the analogue of `Work.Drive.continuousAt_gadget` for the gadgets `Work.Drive.chGadget c a ρ i`
built in `Submission/Work/Drive/chartGadget.lean`, where the chart `chartAt ℂ (a i)` is replaced by
an arbitrary chart family `c` from the maximal atlas.

The proof is the same case analysis as in `continuousAt_gadget`: the gadget is the phase of the
ratio of the two chart differences inside the ball `‖(c i) x - chP‖ ≤ 2 ρ i`, the cut-off
exponential `exp (I * (chCut * (chArg).im))` in the annulus `2 ρ i < ‖·‖ < 8 ρ i`, and the constant
`1` outside the ball `‖·‖ < 8 ρ i`.  The only extra inputs are `a i ∈ (c i).source` and
`a (i+1) ∈ (c i).source`, needed to know that `c i` is injective on the two pivots.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open scoped Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

theorem continuousAt_chGadget {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hρ : 0 < ρ i)
    (hclose : ‖Work.Drive.chQ c a i - Work.Drive.chP c a i‖ < 2 * ρ i)
    (hP : a i ∈ (c i).source) (hQ : a (i + 1) ∈ (c i).source)
    (hwell : closure {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) :
    ContinuousAt (Work.Drive.chGadget c a ρ i) x := by
  classical
  set T : Set X := closure {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} with hT_def
  have hTsub : T ⊆ (c i).source := hwell
  by_cases hxT : x ∈ T
  · -- Case 1: `x` lies in the closure of the ball region.
    have hxsrc : x ∈ (c i).source := hTsub hxT
    have hci : ContinuousAt (fun y : X => (c i) y) x := (c i).continuousAt hxsrc
    have hcx_ne_p : (c i) x ≠ chP c a i := by
      intro h
      rw [chP] at h
      exact hx₁ ((c i).injOn hxsrc hP h)
    have hcx_ne_q : (c i) x ≠ chQ c a i := by
      intro h
      rw [chQ] at h
      exact hx₂ ((c i).injOn hxsrc hQ h)
    set R : ℝ := ‖(c i) x - chP c a i‖ with hR_def
    have hR_cont : Tendsto (fun y => ‖(c i) y - chP c a i‖) (𝓝 x) (𝓝 R) := by
      rw [hR_def]
      exact (hci.sub continuousAt_const).norm
    have hlt_ev : ∀ {s : ℝ}, R < s → ∀ᶠ y in 𝓝 x, ‖(c i) y - chP c a i‖ < s :=
      fun hs => hR_cont.eventually (eventually_lt_nhds hs)
    have hgt_ev : ∀ {s : ℝ}, s < R → ∀ᶠ y in 𝓝 x, s < ‖(c i) y - chP c a i‖ :=
      fun hs => hR_cont.eventually (eventually_gt_nhds hs)
    have hsrc_ev : ∀ᶠ y in 𝓝 x, y ∈ (c i).source :=
      (c i).open_source.eventually_mem hxsrc
    set A : Set X := {y : X | y ∈ (c i).source ∧ ‖(c i) y - chP c a i‖ ≤ 2 * ρ i}
      with hA_def
    set B : Set X := {y : X | y ∈ (c i).source ∧ ‖(c i) y - chP c a i‖ < 8 * ρ i}
      with hB_def
    set H1 : X → ℂ := fun y => phase (((c i) y - chP c a i) / ((c i) y - chQ c a i))
      with hH1_def
    set H2 : X → ℂ := fun y =>
      Complex.exp (Complex.I * ((chCut c a ρ i y : ℂ) * ((chArg c a i y).im : ℂ))) with hH2_def
    set G2 : X → ℂ := fun y => if y ∈ B then H2 y else 1 with hG2_def
    have hgad : chGadget c a ρ i = fun y => if y ∈ A then H1 y else G2 y := by
      funext y
      simp only [chGadget, hA_def, hB_def, hH1_def, hH2_def, hG2_def, Set.mem_ofPred_eq]
    have hH1cont : ContinuousAt H1 x := by
      rw [hH1_def]
      have hw : ((c i) x - chP c a i) / ((c i) x - chQ c a i) ≠ 0 :=
        div_ne_zero (sub_ne_zero.mpr hcx_ne_p) (sub_ne_zero.mpr hcx_ne_q)
      have hf : ContinuousAt (fun y => ((c i) y - chP c a i) / ((c i) y - chQ c a i)) x :=
        (hci.sub continuousAt_const).div (hci.sub continuousAt_const)
          (sub_ne_zero.mpr hcx_ne_q)
      exact (continuousAt_phase hw).comp (f := fun y => ((c i) y - chP c a i) /
        ((c i) y - chQ c a i)) hf
    -- continuity of the "middle" branch, whenever `x` is not strictly inside the inner ball
    have hH2cont_of : ‖chQ c a i - chP c a i‖ < R → ContinuousAt H2 x := by
      intro hRQ
      have hden : (c i) x - chP c a i ≠ 0 := sub_ne_zero.mpr hcx_ne_p
      have hu_lt : ‖(chQ c a i - chP c a i) / ((c i) x - chP c a i)‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
        rw [hR_def] at hRQ
        exact hRQ
      have hcut_cont : ContinuousAt (fun y => chCut c a ρ i y) x := by
        have hcont : Continuous (fun t : ℝ => max 0 (min 1 ((8 * ρ i - t) / (6 * ρ i)))) :=
          continuous_const.max (continuous_const.min
            (Continuous.div_const (continuous_const.sub continuous_id) _))
        simp only [chCut]
        exact hcont.continuousAt.comp (x := x) (f := fun y => ‖(c i) y - chP c a i‖)
          ((hci.sub continuousAt_const).norm)
      have harg_cont : ContinuousAt (fun y => chArg c a i y) x := by
        have hu_cont : ContinuousAt (fun y => (chQ c a i - chP c a i) / ((c i) y - chP c a i)) x :=
          continuousAt_const.div (hci.sub continuousAt_const) hden
        have hmem : (chQ c a i - chP c a i) / ((c i) x - chP c a i) ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero]
          exact hu_lt
        have hlog : ContinuousAt logSeries ((chQ c a i - chP c a i) / ((c i) x - chP c a i)) :=
          continuousOn_logSeries.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
        simp only [chArg]
        exact hlog.comp (f := fun y => (chQ c a i - chP c a i) / ((c i) y - chP c a i)) hu_cont
      rw [hH2_def]
      have h1 : ContinuousAt (fun y => ((chCut c a ρ i y : ℝ) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp hcut_cont
      have h2 : ContinuousAt (fun y => (((chArg c a i y).im : ℝ) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          (Complex.continuous_im.continuousAt.comp harg_cont)
      exact (Complex.continuous_exp.continuousAt).comp
        (f := fun y => Complex.I * ((chCut c a ρ i y : ℂ) * ((chArg c a i y).im : ℂ)))
        (continuousAt_const.mul (h1.mul h2))
    rcases lt_trichotomy R (2 * ρ i) with hlt2 | heq2 | hgt2
    · -- Case 1a: `x` is strictly inside the inner ball: the gadget is `H1` nearby.
      have hAev : ∀ᶠ y in 𝓝 x, y ∈ A := by
        rw [hA_def]
        filter_upwards [hsrc_ev, hlt_ev hlt2] with y hy1 hy2
        exact ⟨hy1, le_of_lt hy2⟩
      have heqF : chGadget c a ρ i =ᶠ[𝓝 x] H1 := by
        filter_upwards [hAev] with y hy
        simp only [hgad, if_pos hy]
      exact hH1cont.congr_of_eventuallyEq heqF
    · -- Case 1b: `x` lies on the sphere of radius `2 ρ i`: the two formulas agree at `x`.
      have hRx : ‖(c i) x - chP c a i‖ = 2 * ρ i := by rw [← hR_def]; exact heq2
      have hRQ : ‖chQ c a i - chP c a i‖ < R := by rw [heq2]; exact hclose
      have hH2cont : ContinuousAt H2 x := hH2cont_of hRQ
      have hcut1 : chCut c a ρ i x = 1 := by
        unfold chCut
        rw [hRx, show (8 * ρ i - 2 * ρ i) = 6 * ρ i by ring,
          div_self (by linarith : (6 * ρ i) ≠ 0), min_eq_left le_rfl, max_eq_right zero_le_one]
      have hkey := exp_im_logSeries_eq_phase_div (p := chP c a i) (q := chQ c a i)
        (w := (c i) x - chP c a i) (sub_ne_zero.mpr hcx_ne_p)
        (show ‖chQ c a i - chP c a i‖ < ‖(c i) x - chP c a i‖ from by rw [hRx]; exact hclose)
      have hH1x : H1 x = H2 x := by
        have hArgx : chArg c a i x = logSeries ((chQ c a i - chP c a i) / ((c i) x - chP c a i)) := by
          simp only [chArg]
        have hmid : phase (((c i) x - chP c a i) / ((c i) x - chQ c a i)) =
            Complex.exp (Complex.I *
              ((logSeries ((chQ c a i - chP c a i) / ((c i) x - chP c a i))).im : ℂ)) := by
          rw [hkey]
          congr 1
          ring
        rw [hH1_def, hH2_def]
        simp only [hArgx, hcut1, Complex.ofReal_one, one_mul]
        exact hmid
      have hxB : x ∈ B := by
        rw [hB_def]
        exact ⟨hxsrc, by rw [hRx]; linarith⟩
      have hG2x : G2 x = H2 x := by
        simp only [hG2_def, if_pos hxB]
      have hBev : ∀ᶠ y in 𝓝 x, y ∈ B := by
        have h8 : R < 8 * ρ i := by rw [heq2]; linarith
        rw [hB_def]
        filter_upwards [hsrc_ev, hlt_ev h8] with y hy1 hy2
        exact ⟨hy1, hy2⟩
      have hG2cont : ContinuousAt G2 x := by
        rw [hG2_def]
        refine hH2cont.congr_of_eventuallyEq ?_
        filter_upwards [hBev] with y hy
        simp only [if_pos hy]
      rw [hgad]
      exact continuousAt_ite_of A hH1cont hG2cont (hH1x.trans hG2x.symm)
    · -- Case 2: `x` is strictly outside the inner ball.
      have hRQ : ‖chQ c a i - chP c a i‖ < R := lt_trans hclose hgt2
      have hH2cont : ContinuousAt H2 x := hH2cont_of hRQ
      have hAnot : ∀ᶠ y in 𝓝 x, y ∉ A := by
        filter_upwards [hgt_ev hgt2] with y hy hcon
        rw [hA_def] at hcon
        exact absurd hcon.2 (not_le.mpr hy)
      rcases lt_trichotomy R (8 * ρ i) with hlt8 | heq8 | hgt8
      · -- Case 2a: `x` is in the open annulus `2 ρ i < ‖·‖ < 8 ρ i`: the gadget is `H2` nearby.
        have hBev : ∀ᶠ y in 𝓝 x, y ∈ B := by
          rw [hB_def]
          filter_upwards [hsrc_ev, hlt_ev hlt8] with y hy1 hy2
          exact ⟨hy1, hy2⟩
        have heqF : chGadget c a ρ i =ᶠ[𝓝 x] H2 := by
          filter_upwards [hAnot, hBev] with y hyA hyB
          simp only [hgad, hG2_def, if_neg hyA, if_pos hyB]
        exact hH2cont.congr_of_eventuallyEq heqF
      · -- Case 2b: `x` lies on the sphere of radius `8 ρ i`: the middle branch tends to `1`.
        have hRx8 : ‖(c i) x - chP c a i‖ = 8 * ρ i := by rw [← hR_def]; exact heq8
        have hcut0 : chCut c a ρ i x = 0 := by
          unfold chCut
          rw [hRx8, show (8 * ρ i - 8 * ρ i) = 0 by ring, zero_div,
            min_eq_right zero_le_one, max_self]
        have hH2x : H2 x = 1 := by
          simp only [hH2_def, hcut0, Complex.ofReal_zero, zero_mul, mul_zero,
            Complex.exp_zero]
        have hG2cont : ContinuousAt G2 x := by
          rw [hG2_def]
          exact continuousAt_ite_of B hH2cont (continuousAt_const :
            ContinuousAt (fun _ : X => (1 : ℂ)) x) hH2x
        have heqF : chGadget c a ρ i =ᶠ[𝓝 x] G2 := by
          filter_upwards [hAnot] with y hyA
          simp only [hgad, if_neg hyA]
        exact hG2cont.congr_of_eventuallyEq heqF
      · -- Case 2c: `x` is strictly outside the ball of radius `8 ρ i`: the gadget is `1`.
        have hBnot : ∀ᶠ y in 𝓝 x, y ∉ B := by
          filter_upwards [hgt_ev hgt8] with y hy hcon
          rw [hB_def] at hcon
          exact absurd hcon.2 (not_lt.mpr (le_of_lt hy))
        have heqF : chGadget c a ρ i =ᶠ[𝓝 x] (fun _ : X => (1 : ℂ)) := by
          filter_upwards [hAnot, hBnot] with y hyA hyB
          simp only [hgad, hG2_def, if_neg hyA, if_neg hyB]
        exact (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℂ)) x).congr_of_eventuallyEq
          heqF
  · -- Case 3: `x` is outside the closure of the ball region: the gadget is `1` near `x`.
    have hTn : Tᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxT
    have heqF : chGadget c a ρ i =ᶠ[𝓝 x] (fun _ : X => (1 : ℂ)) := by
      filter_upwards [hTn] with y hy
      by_contra hne
      refine hy (hT_def ▸ subset_closure ?_)
      have hmem := chGadget_ne_one_mem (c := c) (a := a) (ρ := ρ) (i := i) hρ hne
      exact ⟨hmem.1, by simpa [Metric.mem_ball, dist_eq_norm, chP] using hmem.2⟩
    exact (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℂ)) x).congr_of_eventuallyEq heqF

end Work.Drive
