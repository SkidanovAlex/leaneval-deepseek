import Mathlib
import Submission.Lib.Unif2.Work.Drive.phaseGadget

/-!
# Continuity of the transfer gadget away from its two pivots

The `i`-th transfer gadget `Work.Drive.gadget a ρ i` (see `Submission/Work/Drive/phaseGadget.lean`)
is built out of three pieces, according to the position of a point `y` in the chart at `a i`
(`c := chartAt ℂ (a i)`, `p := gP a i`, `q := gQ a i`):

* on the inner ball `‖c y - p‖ ≤ 2 * ρ i` it is the phase of the ratio of the two chart
  differences `(c y - p)/(c y - q)`;
* on the annulus `2 * ρ i < ‖c y - p‖ < 8 * ρ i` it is the cut-off exponential
  `exp (I * (gCut * (gArg).im))`;
* outside the ball of radius `8 * ρ i` it is the constant `1`.

This file proves that the gadget is continuous at every point `x` which is not one of the two
pivots `a i`, `a (i+1)`.

The interesting point is where the first two pieces meet, i.e. on the sphere
`‖c x - p‖ = 2 * ρ i`.  There the cut-off function `gCut` equals `1`, and the identity
`exp (I * (logSeries u).im) = phase ((1 - u)⁻¹)`, valid for `‖u‖ < 1` (proved below from the
classical formula `‖z‖ * exp (arg z * I) = z`), shows that the two formulas have the same value at
`x`.  Since both branches are continuous, and every point is either interior to one of the three
regions or a meeting point of two of them, a two-branch lemma for piecewise defined functions
(`continuousAt_ite_of`) finishes the proof.

The hypothesis `hwell` (the chart ball of radius `8 ρ i` is closed inside the chart source) is used
only to know that a point of the closure of the (open) ball region belongs to the chart source.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open scoped Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

/-! ## Elementary facts about `phase` and `logSeries` -/

/-- For `z ≠ 0` the imaginary part of the principal logarithm of `z` exponentiates to the phase
of `z`. -/
theorem exp_I_mul_log_im {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.I * ((Complex.log z).im : ℂ)) = phase z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have h1 : Complex.exp (Complex.I * ((Complex.log z).im : ℂ))
      = Complex.exp ((z.arg : ℂ) * Complex.I) := by
    rw [Complex.log_im, mul_comm]
  rw [h1, phase, eq_div_iff hn, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- The phase of the inverse of `z ≠ 0` is the conjugate of the phase of `z`. -/
theorem phase_inv_eq_conj {z : ℂ} (hz : z ≠ 0) :
    phase z⁻¹ = (starRingEnd ℂ) (phase z) := by
  have h2 : phase z * phase z⁻¹ = 1 := by
    rw [phase_mul hz (inv_ne_zero hz), mul_inv_cancel₀ hz]
    simp [phase]
  have h3 : (phase z)⁻¹ = phase z⁻¹ := (mul_eq_one_iff_inv_eq₀ (phase_ne_zero hz)).mp h2
  rw [← h3, Complex.inv_eq_conj (norm_phase hz)]

/-- `phase` is continuous at every non-zero complex number. -/
theorem continuousAt_phase {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h1 : ContinuousAt (fun w : ℂ => ((‖w‖⁻¹ : ℝ) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_norm.continuousAt.inv₀ hn)
  have h2 : ContinuousAt (fun w : ℂ => ((‖w‖⁻¹ : ℝ) : ℂ) * w) z := h1.mul continuousAt_id
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with w
  unfold phase
  rw [div_eq_mul_inv, Complex.ofReal_inv, mul_comm]

/-- The key identity: for `‖u‖ < 1`, `exp (I * (logSeries u).im)` is the phase of `(1 - u)⁻¹`. -/
theorem exp_I_mul_im_logSeries {u : ℂ} (hu : ‖u‖ < 1) :
    Complex.exp (Complex.I * ((logSeries u).im : ℂ)) = phase ((1 - u)⁻¹) := by
  have hu1 : (1 : ℂ) - u ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h] at hu
    simp at hu
  have hs : ((logSeries u).im : ℂ) = -(((Complex.log (1 - u)).im : ℂ)) := by
    rw [logSeries_of_norm_lt_one hu, Complex.neg_im, Complex.ofReal_neg]
  have key : (starRingEnd ℂ) (Complex.exp (Complex.I * ((logSeries u).im : ℂ)))
      = phase (1 - u) := by
    rw [hs, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
      neg_mul_neg]
    exact exp_I_mul_log_im hu1
  rw [phase_inv_eq_conj hu1, ← key, Complex.conj_conj]

/-- The form of the identity used by the gadget: with `u = (q - p)/w` and `‖u‖ < 1`, the cut-off
exponential equals the phase of `w/(w - (q - p))`. -/
theorem exp_im_logSeries_eq_phase_div {p q w : ℂ} (hw : w ≠ 0) (h : ‖q - p‖ < ‖w‖) :
    Complex.exp (Complex.I * ((logSeries ((q - p) / w)).im : ℂ))
      = phase (w / (w - (q - p))) := by
  set u : ℂ := (q - p) / w with hu_def
  have hu_lt : ‖u‖ < 1 := by
    rw [hu_def, norm_div, div_lt_one (norm_pos_iff.mpr hw)]
    exact h
  have h1u : (1 : ℂ) - u = (w - (q - p)) / w := by
    rw [hu_def]; field_simp
  have hinv : w / (w - (q - p)) = (1 - u)⁻¹ := by
    rw [h1u, inv_div]
  rw [exp_I_mul_im_logSeries hu_lt, ← hinv]

/-! ## A two-branch continuity lemma -/

/-- If `f` and `g` are continuous at `x` and take the same value there, then so is the function
which selects `f` on an arbitrary set and `g` outside it. -/
theorem continuousAt_ite_of {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α → β} {x : α} (A : Set α) [DecidablePred (· ∈ A)]
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hfg : f x = g x) :
    ContinuousAt (fun y => if y ∈ A then f y else g y) x := by
  rw [ContinuousAt, show (if x ∈ A then f x else g x) = f x by
    by_cases h : x ∈ A <;> simp [h, hfg]]
  rw [Filter.tendsto_def]
  intro s hs
  have hf' : f ⁻¹' s ∈ 𝓝 x :=
    (Filter.tendsto_def.mp (show Tendsto f (𝓝 x) (𝓝 (f x)) from hf)) s hs
  have hg' : g ⁻¹' s ∈ 𝓝 x :=
    (Filter.tendsto_def.mp (show Tendsto g (𝓝 x) (𝓝 (g x)) from hg)) s (hfg ▸ hs)
  filter_upwards [hf', hg'] with y hy1 hy2
  by_cases hyA : y ∈ A
  · simpa [hyA] using hy1
  · simpa [hyA] using hy2

/-! ## Continuity of the gadget -/

theorem continuousAt_gadget {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hρ : 0 < ρ i)
    (hclose : ‖Work.Drive.gQ a i - Work.Drive.gP a i‖ < 2 * ρ i)
    (hsrc : a (i + 1) ∈ (chartAt ℂ (a i)).source)
    (hwell : closure {y : X | y ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) y ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i)}
        ⊆ (chartAt ℂ (a i)).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) :
    ContinuousAt (Work.Drive.gadget a ρ i) x := by
  classical
  set c : X → ℂ := fun y => (chartAt ℂ (a i)) y with hc_def
  have hc_apply : ∀ y : X, c y = (chartAt ℂ (a i)) y := fun y => rfl
  set T : Set X := closure {y : X | y ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) y ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i)} with hT_def
  have hTsub : T ⊆ (chartAt ℂ (a i)).source := hwell
  by_cases hxT : x ∈ T
  · -- Case 1: `x` lies in the closure of the ball region.
    have hxsrc : x ∈ (chartAt ℂ (a i)).source := hTsub hxT
    have hc : ContinuousAt c x := (chartAt ℂ (a i)).continuousAt hxsrc
    have hcx_ne_p : c x ≠ gP a i := by
      intro h
      have h' : c x = c (a i) := by rw [gP] at h; exact h
      exact hx₁ ((chartAt ℂ (a i)).injOn hxsrc (mem_chart_source ℂ (a i)) h')
    have hcx_ne_q : c x ≠ gQ a i := by
      intro h
      have h' : c x = c (a (i + 1)) := by rw [gQ] at h; exact h
      exact hx₂ ((chartAt ℂ (a i)).injOn hxsrc hsrc h')
    set R : ℝ := ‖c x - gP a i‖ with hR_def
    have hR_cont : Tendsto (fun y => ‖c y - gP a i‖) (𝓝 x) (𝓝 R) := by
      rw [hR_def]
      exact (hc.sub continuousAt_const).norm
    have hlt_ev : ∀ {s : ℝ}, R < s → ∀ᶠ y in 𝓝 x, ‖c y - gP a i‖ < s :=
      fun hs => hR_cont.eventually (eventually_lt_nhds hs)
    have hgt_ev : ∀ {s : ℝ}, s < R → ∀ᶠ y in 𝓝 x, s < ‖c y - gP a i‖ :=
      fun hs => hR_cont.eventually (eventually_gt_nhds hs)
    have hsrc_ev : ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ (a i)).source :=
      (chartAt ℂ (a i)).open_source.eventually_mem hxsrc
    set A : Set X := {y : X | y ∈ (chartAt ℂ (a i)).source ∧ ‖c y - gP a i‖ ≤ 2 * ρ i}
      with hA_def
    set B : Set X := {y : X | y ∈ (chartAt ℂ (a i)).source ∧ ‖c y - gP a i‖ < 8 * ρ i}
      with hB_def
    set H1 : X → ℂ := fun y => phase ((c y - gP a i) / (c y - gQ a i)) with hH1_def
    set H2 : X → ℂ := fun y =>
      Complex.exp (Complex.I * ((gCut a ρ i y : ℂ) * ((gArg a i y).im : ℂ))) with hH2_def
    set G2 : X → ℂ := fun y => if y ∈ B then H2 y else 1 with hG2_def
    have hgad : gadget a ρ i = fun y => if y ∈ A then H1 y else G2 y := by
      funext y
      simp only [gadget, hA_def, hB_def, hH1_def, hH2_def, hG2_def, Set.mem_ofPred_eq,
        ← hc_apply]
    have hH1cont : ContinuousAt H1 x := by
      rw [hH1_def]
      have hw : (c x - gP a i) / (c x - gQ a i) ≠ 0 :=
        div_ne_zero (sub_ne_zero.mpr hcx_ne_p) (sub_ne_zero.mpr hcx_ne_q)
      have hf : ContinuousAt (fun y => (c y - gP a i) / (c y - gQ a i)) x :=
        (hc.sub continuousAt_const).div (hc.sub continuousAt_const)
          (sub_ne_zero.mpr hcx_ne_q)
      exact (continuousAt_phase hw).comp (f := fun y => (c y - gP a i) / (c y - gQ a i)) hf
    -- continuity of the "middle" branch, whenever `x` is not strictly inside the inner ball
    have hH2cont_of : ‖gQ a i - gP a i‖ < R → ContinuousAt H2 x := by
      intro hRQ
      have hden : c x - gP a i ≠ 0 := sub_ne_zero.mpr hcx_ne_p
      have hu_lt : ‖(gQ a i - gP a i) / (c x - gP a i)‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
        rw [hR_def] at hRQ
        exact hRQ
      have hcut_cont : ContinuousAt (fun y => gCut a ρ i y) x := by
        have hcont : Continuous (fun t : ℝ => max 0 (min 1 ((8 * ρ i - t) / (6 * ρ i)))) :=
          continuous_const.max (continuous_const.min
            (Continuous.div_const (continuous_const.sub continuous_id) _))
        simp only [gCut]
        exact hcont.continuousAt.comp (x := x) (f := fun y => ‖c y - gP a i‖)
          ((hc.sub continuousAt_const).norm)
      have harg_cont : ContinuousAt (fun y => gArg a i y) x := by
        have hu_cont : ContinuousAt (fun y => (gQ a i - gP a i) / (c y - gP a i)) x :=
          continuousAt_const.div (hc.sub continuousAt_const) hden
        have hmem : (gQ a i - gP a i) / (c x - gP a i) ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero]
          exact hu_lt
        have hlog : ContinuousAt logSeries ((gQ a i - gP a i) / (c x - gP a i)) :=
          continuousOn_logSeries.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
        simp only [gArg]
        exact hlog.comp (f := fun y => (gQ a i - gP a i) / (c y - gP a i)) hu_cont
      rw [hH2_def]
      have h1 : ContinuousAt (fun y => ((gCut a ρ i y : ℝ) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp hcut_cont
      have h2 : ContinuousAt (fun y => (((gArg a i y).im : ℝ) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          (Complex.continuous_im.continuousAt.comp harg_cont)
      exact (Complex.continuous_exp.continuousAt).comp
        (f := fun y => Complex.I * ((gCut a ρ i y : ℂ) * ((gArg a i y).im : ℂ)))
        (continuousAt_const.mul (h1.mul h2))
    rcases lt_trichotomy R (2 * ρ i) with hlt2 | heq2 | hgt2
    · -- Case 1a: `x` is strictly inside the inner ball: the gadget is `H1` nearby.
      have hAev : ∀ᶠ y in 𝓝 x, y ∈ A := by
        rw [hA_def]
        filter_upwards [hsrc_ev, hlt_ev hlt2] with y hy1 hy2
        exact ⟨hy1, le_of_lt hy2⟩
      have heqF : gadget a ρ i =ᶠ[𝓝 x] H1 := by
        filter_upwards [hAev] with y hy
        simp only [hgad, if_pos hy]
      exact hH1cont.congr_of_eventuallyEq heqF
    · -- Case 1b: `x` lies on the sphere of radius `2 ρ i`: the two formulas agree at `x`.
      have hRx : ‖c x - gP a i‖ = 2 * ρ i := by rw [← hR_def]; exact heq2
      have hRQ : ‖gQ a i - gP a i‖ < R := by rw [heq2]; exact hclose
      have hH2cont : ContinuousAt H2 x := hH2cont_of hRQ
      have hcut1 : gCut a ρ i x = 1 := by
        unfold gCut
        rw [hRx, show (8 * ρ i - 2 * ρ i) = 6 * ρ i by ring,
          div_self (by linarith : (6 * ρ i) ≠ 0), min_eq_left le_rfl, max_eq_right zero_le_one]
      have hkey := exp_im_logSeries_eq_phase_div (p := gP a i) (q := gQ a i)
        (w := c x - gP a i) (sub_ne_zero.mpr hcx_ne_p)
        (show ‖gQ a i - gP a i‖ < ‖c x - gP a i‖ from by rw [hRx]; exact hclose)
      have hH1x : H1 x = H2 x := by
        have hArgx : gArg a i x = logSeries ((gQ a i - gP a i) / (c x - gP a i)) := by
          simp only [gArg, ← hc_apply]
        have hmid : phase ((c x - gP a i) / (c x - gQ a i)) =
            Complex.exp (Complex.I *
              ((logSeries ((gQ a i - gP a i) / (c x - gP a i))).im : ℂ)) := by
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
      have hRQ : ‖gQ a i - gP a i‖ < R := lt_trans hclose hgt2
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
        have heqF : gadget a ρ i =ᶠ[𝓝 x] H2 := by
          filter_upwards [hAnot, hBev] with y hyA hyB
          simp only [hgad, hG2_def, if_neg hyA, if_pos hyB]
        exact hH2cont.congr_of_eventuallyEq heqF
      · -- Case 2b: `x` lies on the sphere of radius `8 ρ i`: the middle branch tends to `1`.
        have hRx8 : ‖c x - gP a i‖ = 8 * ρ i := by rw [← hR_def]; exact heq8
        have hcut0 : gCut a ρ i x = 0 := by
          unfold gCut
          rw [hRx8, show (8 * ρ i - 8 * ρ i) = 0 by ring, zero_div,
            min_eq_right zero_le_one, max_self]
        have hH2x : H2 x = 1 := by
          simp only [hH2_def, hcut0, Complex.ofReal_zero, zero_mul, mul_zero,
            Complex.exp_zero]
        have hG2cont : ContinuousAt G2 x := by
          rw [hG2_def]
          exact continuousAt_ite_of B hH2cont (continuousAt_const :
            ContinuousAt (fun _ : X => (1 : ℂ)) x) hH2x
        have heqF : gadget a ρ i =ᶠ[𝓝 x] G2 := by
          filter_upwards [hAnot] with y hyA
          simp only [hgad, if_neg hyA]
        exact hG2cont.congr_of_eventuallyEq heqF
      · -- Case 2c: `x` is strictly outside the ball of radius `8 ρ i`: the gadget is `1`.
        have hBnot : ∀ᶠ y in 𝓝 x, y ∉ B := by
          filter_upwards [hgt_ev hgt8] with y hy hcon
          rw [hB_def] at hcon
          exact absurd hcon.2 (not_lt.mpr (le_of_lt hy))
        have heqF : gadget a ρ i =ᶠ[𝓝 x] (fun _ : X => (1 : ℂ)) := by
          filter_upwards [hAnot, hBnot] with y hyA hyB
          simp only [hgad, hG2_def, if_neg hyA, if_neg hyB]
        exact (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℂ)) x).congr_of_eventuallyEq
          heqF
  · -- Case 3: `x` is outside the closure of the ball region: the gadget is `1` near `x`.
    have hTn : Tᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxT
    have heqF : gadget a ρ i =ᶠ[𝓝 x] (fun _ : X => (1 : ℂ)) := by
      filter_upwards [hTn] with y hy
      by_contra hne
      refine hy (hT_def ▸ subset_closure ?_)
      have hmem := gadget_ne_one_mem (a := a) (ρ := ρ) (i := i) hρ hne
      exact ⟨hmem.1, by simpa [Metric.mem_ball, dist_eq_norm, gP] using hmem.2⟩
    exact (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℂ)) x).congr_of_eventuallyEq heqF

end Work.Drive
