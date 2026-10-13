import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `thetaChain` — the angular chain identity of `I₁` with the two cut-offs

The datum of `Work.FTS.EllipticEst.H2W.Ae.AeData` is only `C^∞` on the *open* quadrant, so the
angular integration by parts `slice_theta_ibp_cut` is available only slice by slice (at a fixed
`z > 0`).  The target integrates it against the radial cut-off `χ_n = cut n`, which is constant
in `θ`; this file performs the bookkeeping:

* for every `z > 0` the constant `w(z)²·χ_n(z)` is pulled out of the `θ`-integral, the slice
  identity `slice_theta_ibp_cut` is applied, and the constant is pushed back in;
* the three `z`-marginals of the right-hand side are integrable, because each integrand is
  continuous on the open quadrant and vanishes off the compact rectangle
  `[1/(n+1), 3(n+1)] × [min (ε/2) (π/4), max (π/2 - ε/2) (π/4)]` (the first factor from `χ_n`,
  the second from `χ_ε` resp. `χ_ε'`), so Fubini (`Integrable.integral_prod_left`) applies;
* the outer `z`-integral is split with `integral_add` / `integral_sub` / `integral_neg` /
  `integral_const_mul` using those integrability facts.
-/

namespace Work.FTS.EllipticEst.I1Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A compactly supported continuous function is integrable for the product measure -/

private theorem integrable_prod_of_box {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d))
    (hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → g z θ = 0) :
    Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
  have hIntK : IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hcont
  have hvol : Integrable (Function.uncurry g) (volume : Measure (ℝ × ℝ)) :=
    hIntK.integrable_of_forall_notMem_eq_zero (fun p hp => by
      rw [Set.mem_prod] at hp
      exact hbox p.1 p.2 (not_and_or.mp hp))
  rw [MeasureTheory.Measure.prod_restrict]
  exact hvol.mono_measure MeasureTheory.Measure.restrict_le_self

/-! ## Continuity of the elementary factors on the open quadrant -/

private theorem continuousOn_wSq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have h : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h' : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
      exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
        ((continuous_id.pow 2).continuousOn) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    exact h'.pow 2
  exact h.comp continuous_fst.continuousOn (fun _ hp => hp.1)

private theorem continuousOn_sinTwo_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 := by
  have hsinI : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsinI.comp continuous_snd.continuousOn (fun p hp => hp.2)

private theorem continuousOn_sigE_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.sigE p.2)
      Work.FTS.EllipticEst.Q0 :=
  (continuousOn_sinTwo_Q0.rpow_const (fun p hp => by
      left
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))).congr (fun p _ => rfl)

private theorem continuousOn_sig1_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.sig1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  (continuousOn_sinTwo_Q0.rpow_const (fun p hp => by
      left
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))).congr (fun p _ => rfl)

private theorem continuousOn_cut_Q0 (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1)
      Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.cut_contDiff n).continuous).continuousOn).comp
    continuous_fst.continuousOn (fun _ _ => Set.mem_univ _)

private theorem continuousOn_cutE_Q0 (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
      Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous).continuousOn).comp
    continuous_snd.continuousOn (fun _ _ => Set.mem_univ _)

private theorem continuousOn_derivCutE_Q0 (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) p.2)
      Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous_deriv
    (by norm_num)).continuousOn).comp continuous_snd.continuousOn
      (fun _ _ => Set.mem_univ _)

private theorem continuousOn_cosTwo_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).comp
    continuous_snd.continuousOn (fun _ hp => hp.2)

/-! ## The vanishing of the cut-offs and of `χ_ε'` at the endpoints of their plateau -/

private theorem deriv_cutE_eq_zero_of_lt {ε θ : ℝ} (hε : 0 < ε) (h : θ < ε / 2) :
    deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.SliceMixedAux.cut ε y)
      =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with y hy
    exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε (le_of_lt hy)
  simpa using hEq.deriv_eq

private theorem deriv_cutE_eq_zero_of_gt {ε θ : ℝ} (hε : 0 < ε)
    (h : Real.pi / 2 - ε / 2 < θ) :
    deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.SliceMixedAux.cut ε y)
      =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
    exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε (le_of_lt hy)
  simpa using hEq.deriv_eq

/-! ## The target -/

theorem thetaChain {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ))
      = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
        + 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
              * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                  * Real.cos (2 * θ)))
        - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * (Work.FTS.EllipticEst.cut n z * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ## the support rectangle
  set a : ℝ := 1 / ((n : ℝ) + 1) with ha
  set b : ℝ := 3 * ((n : ℝ) + 1) with hb
  set c : ℝ := min (ε / 2) (Real.pi / 4) with hc
  set d : ℝ := max (Real.pi / 2 - ε / 2) (Real.pi / 4) with hd
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hc_pos : 0 < c := by
    rw [hc]; exact lt_min (by linarith) (by linarith [Real.pi_pos])
  have hd_lt : d < Real.pi / 2 := by
    rw [hd]; exact max_lt (by linarith) (by linarith [Real.pi_pos])
  have hc_le : c ≤ ε / 2 := by rw [hc]; exact min_le_left _ _
  have hd_ge : Real.pi / 2 - ε / 2 ≤ d := by rw [hd]; exact le_max_left _ _
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ hp
    rw [Set.mem_prod] at hp
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨by linarith [hp.1.1, ha_pos], by linarith [hp.2.1, hc_pos],
      by linarith [hp.2.2, hd_lt]⟩
  have hcutn : ∀ z, z ∉ Set.Icc a b → Work.FTS.EllipticEst.cut n z = 0 := by
    intro z hz
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
    rcases hz with hz | hz
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt hz)
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (by rw [hb] at hz; exact le_of_lt hz)
  have hcutE : ∀ θ, θ ∉ Set.Icc c d →
      Work.FTS.EllipticEst.SliceMixedAux.cut ε θ = 0 := by
    intro θ hθ
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with hθ | hθ
    · exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε
        (le_of_lt (lt_of_lt_of_le hθ hc_le))
    · exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε
        (le_of_lt (lt_of_le_of_lt hd_ge hθ))
  have hdercutE : ∀ θ, θ ∉ Set.Icc c d →
      deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ = 0 := by
    intro θ hθ
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with hθ | hθ
    · exact deriv_cutE_eq_zero_of_lt hε (lt_of_lt_of_le hθ hc_le)
    · exact deriv_cutE_eq_zero_of_gt hε (lt_of_le_of_lt hd_ge hθ)
  have hVc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.V u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeI1Fts.continuousOn_V hS
  have hUc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.U u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeI1Fts.continuousOn_U hS
  -- ## integrability of the three `z`-marginals of the right-hand side
  have hJB : IntegrableOn (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
        * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2) (Set.Ioi 0) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ =>
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2))
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (ContinuousOn.mul (ContinuousOn.mul
        (ContinuousOn.mul continuousOn_wSq_Q0 continuousOn_sigE_Q0)
        (ContinuousOn.mul (continuousOn_cut_Q0 n) (continuousOn_cutE_Q0 ε)))
        (ContinuousOn.pow hVc 2)).mono hKsub
    have hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2 = 0 := by
      intro z θ hr
      rcases hr with hr | hr
      · simp [hcutn z hr]
      · simp [hcutE θ hr]
    have h1 := integrable_prod_of_box hcont hbox
    have h2 := h1.integral_prod_left
    simpa [MeasureTheory.IntegrableOn, Function.uncurry] using h2
  have hJC : IntegrableOn (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
        * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
            * Real.cos (2 * θ))) (Set.Ioi 0) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ =>
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
              * Real.cos (2 * θ)))) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (ContinuousOn.mul (ContinuousOn.mul
        (ContinuousOn.mul continuousOn_wSq_Q0 continuousOn_sig1_Q0)
        (ContinuousOn.mul (continuousOn_cut_Q0 n) (continuousOn_cutE_Q0 ε)))
        (ContinuousOn.mul (ContinuousOn.mul hUc hVc) continuousOn_cosTwo_Q0)).mono hKsub
    have hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
              * Real.cos (2 * θ)) = 0 := by
      intro z θ hr
      rcases hr with hr | hr
      · simp [hcutn z hr]
      · simp [hcutE θ hr]
    have h1 := integrable_prod_of_box hcont hbox
    have h2 := h1.integral_prod_left
    simpa [MeasureTheory.IntegrableOn, Function.uncurry] using h2
  have hJD : IntegrableOn (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
        * (Work.FTS.EllipticEst.cut n z
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
        * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ))
      (Set.Ioi 0) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ =>
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)))
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      (ContinuousOn.mul (ContinuousOn.mul
        (ContinuousOn.mul continuousOn_wSq_Q0 continuousOn_sigE_Q0)
        (ContinuousOn.mul (continuousOn_cut_Q0 n) (continuousOn_derivCutE_Q0 ε)))
        (ContinuousOn.mul hUc hVc)).mono hKsub
    have hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ) = 0 := by
      intro z θ hr
      rcases hr with hr | hr
      · simp [hcutn z hr]
      · simp [hdercutE θ hr]
    have h1 := integrable_prod_of_box hcont hbox
    have h2 := h1.integral_prod_left
    simpa [MeasureTheory.IntegrableOn, Function.uncurry] using h2
  -- ## the slicewise identity (the angular integration by parts at fixed `z`)
  have hz_ident : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ))
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
        + 2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
              * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                  * Real.cos (2 * θ)))
        - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * (Work.FTS.EllipticEst.cut n z
                  * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
    intro z hz
    have hIBP := Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut hS hz hε
    have hA : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ))
        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ)) := by
      have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ))
          = fun θ => ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
              * (Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ)) := by
        funext θ; ring
      rw [hfun, MeasureTheory.integral_const_mul]
    have hB : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2) := by
      have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
          = fun θ => ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
              * (Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2) := by
        funext θ; ring
      rw [hfun, MeasureTheory.integral_const_mul]
    have hC : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                * Real.cos (2 * θ)))
        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.AeI1Fts.sig1 θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                    * Real.cos (2 * θ))) := by
      have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                * Real.cos (2 * θ)))
          = fun θ => ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
              * (Work.FTS.EllipticEst.AeI1Fts.sig1 θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                    * Real.cos (2 * θ))) := by
        funext θ; ring
      rw [hfun, MeasureTheory.integral_const_mul]
    have hD : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ))
        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
      have hfun : (fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ))
          = fun θ => ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.cut n z)
              * (Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
        funext θ; ring
      rw [hfun, MeasureTheory.integral_const_mul]
    rw [hA, hB, hC, hD, hIBP]
    ring
  -- ## assembly
  have hBe : Integrable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
        * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hJB
  have hCe : Integrable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
        * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
            * Real.cos (2 * θ))) (MeasureTheory.volume.restrict (Set.Ioi 0)) := hJC
  have hDe : Integrable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
        * (Work.FTS.EllipticEst.cut n z
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ)
        * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hJD
  have hnegB : Integrable (fun z => -(∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
        * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hBe.neg
  have h2C : Integrable (fun z => 2 * Work.Spaces.eta
      * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                * Real.cos (2 * θ))))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hCe.const_mul (2 * Work.Spaces.eta)
  have hsum : Integrable (fun z => -(∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
      + 2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sig1 θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
              * Real.cos (2 * θ))))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hnegB.add h2C
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hz_ident]
  rw [MeasureTheory.integral_sub hsum hDe]
  rw [MeasureTheory.integral_add hnegB h2C]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]

end

end Work.FTS.EllipticEst.I1Ae
