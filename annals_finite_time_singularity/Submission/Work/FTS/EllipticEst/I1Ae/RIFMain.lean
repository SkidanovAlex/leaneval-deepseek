import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.iter_swap_compact
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.cross_joint_h
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits
import Submission.Work.FTS.EllipticEst.I1Ae.RIFPsiB
import Submission.Work.FTS.EllipticEst.I1Ae.zibpChain
import Submission.Work.FTS.EllipticEst.I1Ae.thetaChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/RIFMain` — the `I₁` expansion identity in the almost-everywhere class

This module assembles the target identity

`IP (z²∂_z²u) (∂_θ²u) = ∫_z w²∫_θ (z∂_z∂_θu)²σ - 2η·IP (z∂_zu) (z∂_zu)
   - 2η(1+η)·N - IP (cw·z∂_zu) (∂_θ²u)`

from the two `cut-off` identities `I1Ae.zibpChain` and `I1Ae.thetaChain` (each proved by the
"radial" resp. "angular" integration by parts with the two cut-offs `χ_n`, `ψ_ε`), the angular
cross identity `AeI1Fts.cross_joint_h` and the limiting lemmas of `I1Ae.RIFLimits`.

-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-! ## The generic angular cut-off limit -/

/-- **The angular cut-off limit.**  If `A` is `L¹` for the product measure `nuQ`, then
multiplying by `ψ ε` does not change the iterated integral in the limit `ε → 0⁺`. -/
theorem tendsto_II_psi_right {A : ℝ → ℝ → ℝ}
    (hA : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2) nuQ) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ * ψ ε θ)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ)) := by
  have hint : ∀ ε : ℝ, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 p.2 * ψ ε p.2) nuQ := by
    intro ε
    refine MeasureTheory.Integrable.mono' hA.norm ?_ ?_
    · exact hA.1.mul (((SliceMixedAux.cut_contDiff ε).continuous.measurable.comp
        measurable_snd).aestronglyMeasurable)
    · filter_upwards with p
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have h1 : |ψ ε p.2| ≤ 1 := by
        rw [abs_of_nonneg (SliceMixedAux.cut_nonneg ε p.2)]
        exact SliceMixedAux.cut_le_one ε p.2
      calc |A p.1 p.2| * |ψ ε p.2| ≤ |A p.1 p.2| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |A p.1 p.2| := mul_one _
  have hconv : ∀ ε : ℝ, (∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ * ψ ε θ)
      = ∫ p, A p.1 p.2 * ψ ε p.2 ∂nuQ := by
    intro ε
    rw [← MeasureTheory.integral_prod (fun p : ℝ × ℝ => A p.1 p.2 * ψ ε p.2) (hint ε)]
  have hconv2 : (∫ z in Set.Ioi 0, ∫ θ in Iθo, A z θ) = ∫ p, A p.1 p.2 ∂nuQ := by
    rw [← MeasureTheory.integral_prod (fun p : ℝ × ℝ => A p.1 p.2) hA]
  have haesm : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => A p.1 p.2 * ψ ε p.2) nuQ :=
    Filter.Eventually.of_forall fun ε =>
      hA.1.mul (((SliceMixedAux.cut_contDiff ε).continuous.measurable.comp
        measurable_snd).aestronglyMeasurable)
  have hbound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      ∀ᵐ p ∂nuQ, ‖A p.1 p.2 * ψ ε p.2‖ ≤ ‖A p.1 p.2‖ :=
    Filter.Eventually.of_forall fun ε => by
      filter_upwards with p
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have h1 : |ψ ε p.2| ≤ 1 := by
        rw [abs_of_nonneg (SliceMixedAux.cut_nonneg ε p.2)]
        exact SliceMixedAux.cut_le_one ε p.2
      calc |A p.1 p.2| * |ψ ε p.2| ≤ |A p.1 p.2| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |A p.1 p.2| := mul_one _
  have hlim : ∀ᵐ p ∂nuQ, Filter.Tendsto (fun ε : ℝ => A p.1 p.2 * ψ ε p.2)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (A p.1 p.2)) := by
    filter_upwards [ae_mem_nuQ] with p hp
    have hmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), ψ ε p.2 = 1 := by
      have h1 : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
          ε < min p.2 (Real.pi / 2 - p.2) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
          (lt_min hp.2.1 (by linarith [hp.2.2, Real.pi_pos])))
      filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
      exact SliceMixedAux.cut_eq_one hε0
        (by linarith [lt_of_lt_of_le hε (min_le_left p.2 (Real.pi / 2 - p.2))])
        (by linarith [lt_of_lt_of_le hε (min_le_right p.2 (Real.pi / 2 - p.2))])
    have hψ : Filter.Tendsto (fun ε : ℝ => ψ ε p.2)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 1) :=
      Filter.Tendsto.congr' (hmem.mono (fun ε hε => hε.symm)) tendsto_const_nhds
    simpa using hψ.const_mul (A p.1 p.2)
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := nuQ) (l := nhdsWithin 0 (Set.Ioi (0 : ℝ)))
    (F := fun (ε : ℝ) (p : ℝ × ℝ) => A p.1 p.2 * ψ ε p.2)
    (f := fun p : ℝ × ℝ => A p.1 p.2) (fun p : ℝ × ℝ => ‖A p.1 p.2‖)
    haesm hbound hA.norm hlim
  simp only [hconv, hconv2]
  exact hmain

/-! ## Joint integrability of a box-supported continuous function -/

/-- A function vanishing off a compact box inside the open quadrant and continuous there is
jointly integrable for the product measure `nuQ`. -/
theorem integrable_nuQ_of_box {g : ℝ → ℝ → ℝ} {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2)
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d))
    (hsupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → g z θ = 0) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2) nuQ := by
  have hboxmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  have h2 : MeasureTheory.Integrable
      ((Set.Icc a b ×ˢ Set.Icc c d).indicator (Function.uncurry g))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (integrable_indicator_iff hboxmeas).mpr
      (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
  have h3 : MeasureTheory.Integrable
      ((Set.Icc a b ×ˢ Set.Icc c d).indicator (Function.uncurry g)) nuQ :=
    h2.mono_measure (by rw [Work.FTS.EllipticEst.AeI1Fts.nuQ_eq]; exact Measure.restrict_le_self)
  refine h3.congr ?_
  filter_upwards [ae_mem_nuQ] with p hp
  by_cases hb : p ∈ Set.Icc a b ×ˢ Set.Icc c d
  · rw [Set.indicator_of_mem hb]
    rfl
  · rw [Set.indicator_of_notMem hb]
    exact (hsupp p.1 p.2 (by
      rcases not_and_or.mp hb with h | h
      · exact Or.inl h
      · exact Or.inr h)).symm


/-- The iterated integral `II` as a product-measure integral. -/
theorem II_eq_integral {g : ℝ → ℝ → ℝ}
    (hg : MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2) nuQ) :
    II g = ∫ p, g p.1 p.2 ∂nuQ := by
  rw [II]
  exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g p.1 p.2) hg).symm

/-- `cw z = 2(z-1)/(1+z)` is continuous on the open quadrant. -/
theorem continuousOn_cw_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.cw p.1)
      Work.FTS.EllipticEst.Q0 := by
  have hcw : Work.FTS.EllipticEst.AngSecond.cw
      = fun z : ℝ => 2 * (z - 1) / (1 + z) := rfl
  have h : ContinuousOn (fun z : ℝ => 2 * (z - 1) / (1 + z)) (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      exact ne_of_gt (by linarith)
  rw [hcw]
  exact h.comp continuous_fst.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- **The cut-off identity.**  The radial integration by parts (`zibpChain`, on `Fp`) combined
with the angular one (`thetaChain`, on the mixed term `U·Hh`) and the pointwise splitting
`Fp = (AA·BB + cw·U·BB) + U·Hh`. -/
theorem auxCutOff {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ Real.pi / 8) :
    (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
        * (AA u z θ * BB u z θ
            + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))
      = - (∫ z in Set.Ioi 0, ∫ θ in Iθo,
            sigE θ * deriv (χ n) z * (ψ ε θ * Fd u z θ))
        + (∫ z in Set.Ioi 0, ∫ θ in Iθo,
            (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ) * (V u z θ) ^ 2)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, ∫ θ in Iθo,
            (Work.Spaces.w z) ^ 2 * sig1 θ * (χ n z * ψ ε θ)
              * (U u z θ * V u z θ * Real.cos (2 * θ)))
        + (∫ z in Set.Ioi 0, ∫ θ in Iθo,
            (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * deriv (ψ ε) θ)
              * (U u z θ * V u z θ)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ## the box
  set a : ℝ := 1 / (2 * (n + 1 : ℝ)) with ha
  set b : ℝ := 4 * (n + 1 : ℝ) with hb
  set c : ℝ := ε / 4 with hc
  set d : ℝ := Real.pi / 2 - ε / 4 with hd
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hab : a ≤ b := by
    rw [ha, hb]
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hcd : c ≤ d := by rw [hc, hd]; linarith [Real.pi_pos, hε8]
  have hd_lt : d < Real.pi / 2 := by rw [hd]; linarith
  have hboxQ : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le ha_pos hz.1, lt_of_lt_of_le hc_pos hθ.1, lt_of_le_of_lt hθ.2 hd_lt⟩
  -- ## the support facts
  have hlt_a : ∀ {z : ℝ}, z < a → z ≤ 1 / (n + 1 : ℝ) := by
    intro z hz
    rw [ha] at hz
    have h2 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
      one_div_le_one_div_of_le hn (by linarith)
    linarith
  have hgt_b : ∀ {z : ℝ}, b < z → 3 * (n + 1 : ℝ) ≤ z := by
    intro z hz
    rw [hb] at hz
    linarith
  have hχ0 : ∀ z ∉ Set.Icc a b, χ n z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (hlt_a hz)
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (hgt_b hz)
  have hχ'0 : ∀ z ∉ Set.Icc a b, deriv (χ n) z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have hEq : (fun y : ℝ => χ n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
        exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (hlt_a hy)
      simpa using hEq.deriv_eq
    · have hEq : (fun y : ℝ => χ n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (hgt_b hy)
      simpa using hEq.deriv_eq
  have hψ0 : ∀ θ ∉ Set.Icc c d, ψ ε θ = 0 := by
    intro θ hθ
    simp only [Set.mem_Icc, not_and_or, not_le] at hθ
    rcases hθ with hθ | hθ
    · refine SliceMixedAux.cut_eq_zero_low hε ?_
      rw [hc] at hθ; linarith
    · refine SliceMixedAux.cut_eq_zero_high hε ?_
      rw [hd] at hθ; linarith
  have hψ'0 : ∀ θ ∉ Set.Icc c d, deriv (ψ ε) θ = 0 := by
    intro θ hθ
    simp only [Set.mem_Icc, not_and_or, not_le] at hθ
    refine deriv_cut_eq_zero_of_notMem_win hε ?_
    rw [win, Set.mem_union, not_or]
    constructor
    · rw [Set.mem_Icc, not_and_or, not_le]
      rcases hθ with hθ | hθ
      · left; rw [hc] at hθ; linarith
      · right; rw [hd] at hθ; linarith [hε8]
    · rw [Set.mem_Icc, not_and_or, not_le]
      rcases hθ with hθ | hθ
      · left; rw [hc] at hθ; linarith [hε8, Real.pi_pos]
      · right; rw [hd] at hθ; linarith
  -- ## the seven integrands
  set G1 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
    * Fp u z θ with hG1
  set G2 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
    * (AA u z θ * BB u z θ
        + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ) with hG2
  set G3 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
    * (U u z θ * Hh u z θ) with hG3
  set G4 : ℝ → ℝ → ℝ := fun z θ => sigE θ * deriv (χ n) z * (ψ ε θ * Fd u z θ) with hG4
  set G5 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
    * (V u z θ) ^ 2 with hG5
  set G6 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sig1 θ * (χ n z * ψ ε θ)
    * (U u z θ * V u z θ * Real.cos (2 * θ)) with hG6
  set G7 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * sigE θ
    * (χ n z * deriv (ψ ε) θ) * (U u z θ * V u z θ) with hG7
  -- ## continuity of the factors
  have hUc : ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (AeI1Fts.smoothOpen_U hS).continuousOn
  have hVc : ContinuousOn (fun p : ℝ × ℝ => V u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (AeI1Fts.smoothOpen_V hS).continuousOn
  have hAc : ContinuousOn (fun p : ℝ × ℝ => AA u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (AeI1Fts.smoothOpen_AA hS).continuousOn
  have hBc : ContinuousOn (fun p : ℝ × ℝ => BB u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (AeI1Fts.smoothOpen_BB hS).continuousOn
  have hHc : ContinuousOn (fun p : ℝ × ℝ => Hh u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (AeI1Fts.smoothOpen_Hh hS).continuousOn
  have hsignc : ContinuousOn (fun p : ℝ × ℝ => sigE p.2) Work.FTS.EllipticEst.Q0 :=
    sigE_continuousOn_Iθo.comp continuous_snd.continuousOn
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hsign1c : ContinuousOn (fun p : ℝ × ℝ => sig1 p.2) Work.FTS.EllipticEst.Q0 := by
    have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_snd)
    refine (hsin.continuousOn.rpow_const (p := -(1 + Work.Spaces.eta)) (fun p hp => Or.inl
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1; linarith)
        (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2; linarith [Real.pi_pos]))))).congr
      (fun p _ => rfl)
  have hchic : ContinuousOn (fun p : ℝ × ℝ => χ n p.1) Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
  have hχ'c : ContinuousOn (fun p : ℝ × ℝ => deriv (χ n) p.1) Work.FTS.EllipticEst.Q0 :=
    (((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by norm_num)).comp
      continuous_fst).continuousOn
  have hψc : ContinuousOn (fun p : ℝ × ℝ => ψ ε p.2) Work.FTS.EllipticEst.Q0 :=
    ((SliceMixedAux.cut_contDiff ε).continuous.comp continuous_snd).continuousOn
  have hψ'c : ContinuousOn (fun p : ℝ × ℝ => deriv (ψ ε) p.2) Work.FTS.EllipticEst.Q0 :=
    (((SliceMixedAux.cut_contDiff ε).continuous_deriv (by norm_num)).comp
      continuous_snd).continuousOn
  have hcosc : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn
  have hw2c : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := continuousOn_w_sq_fst
  -- ## joint integrability
  have hbox2 : ∀ {g : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d) →
      (∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → g z θ = 0) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2) nuQ := fun hc' hs' =>
    integrable_nuQ_of_box ha_pos hab hc_pos hcd hd_lt hc' hs'
  have hint3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G3 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
          * (χ n p.1 * ψ ε p.2) * (U u p.1 p.2 * Hh u p.1 p.2))
          Work.FTS.EllipticEst.Q0 :=
        ((hw2c.mul hsignc).mul (hchic.mul hψc)).mul (hUc.mul hHc)
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG3]; simp only []; rw [hχ0 z h]; ring
      · rw [hG3]; simp only []; rw [hψ0 θ h]; ring
  have hint2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G2 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
          * (χ n p.1 * ψ ε p.2) * (AA u p.1 p.2 * BB u p.1 p.2
            + Work.FTS.EllipticEst.AngSecond.cw p.1 * U u p.1 p.2 * BB u p.1 p.2))
          Work.FTS.EllipticEst.Q0 :=
        ((hw2c.mul hsignc).mul (hchic.mul hψc)).mul
          (((hAc.mul hBc)).add ((continuousOn_cw_fst.mul hUc).mul hBc))
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG2]; simp only []; rw [hχ0 z h]; ring
      · rw [hG2]; simp only []; rw [hψ0 θ h]; ring
  have hint5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G5 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
          * (χ n p.1 * ψ ε p.2) * (V u p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
        ((hw2c.mul hsignc).mul (hchic.mul hψc)).mul (hVc.pow 2)
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG5]; simp only []; rw [hχ0 z h]; ring
      · rw [hG5]; simp only []; rw [hψ0 θ h]; ring
  have hint6 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G6 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sig1 p.2
          * (χ n p.1 * ψ ε p.2) * (U u p.1 p.2 * V u p.1 p.2 * Real.cos (2 * p.2)))
          Work.FTS.EllipticEst.Q0 :=
        ((hw2c.mul hsign1c).mul (hchic.mul hψc)).mul ((hUc.mul hVc).mul hcosc)
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG6]; simp only []; rw [hχ0 z h]; ring
      · rw [hG6]; simp only []; rw [hψ0 θ h]; ring
  have hint7 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G7 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
          * (χ n p.1 * deriv (ψ ε) p.2) * (U u p.1 p.2 * V u p.1 p.2))
          Work.FTS.EllipticEst.Q0 :=
        ((hw2c.mul hsignc).mul (hchic.mul hψ'c)).mul (hUc.mul hVc)
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG7]; simp only []; rw [hχ0 z h]; ring
      · rw [hG7]; simp only []; rw [hψ'0 θ h]; ring
  have hFd_c : ContinuousOn (fun p : ℝ × ℝ => Fd u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 * ((U u p.1 p.2) * BB u p.1 p.2)
        * (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
      (continuous_fst.continuousOn.mul (hUc.mul hBc)).mul hw2c
    refine h1.congr ?_
    intro p _
    simp only [Fd, U, BB]
    ring
  have hint4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G4 p.1 p.2) nuQ := by
    refine hbox2 ?_ ?_
    · have hconts : ContinuousOn (fun p : ℝ × ℝ => sigE p.2 * deriv (χ n) p.1
          * (ψ ε p.2 * Fd u p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
        (hsignc.mul hχ'c).mul (hψc.mul hFd_c)
      exact hconts.mono hboxQ
    · intro z θ h
      rcases h with h | h
      · rw [hG4]; simp only []; rw [hχ'0 z h]; ring
      · rw [hG4]; simp only []; rw [hψ0 θ h]; ring
  have hint1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => G1 p.1 p.2) nuQ := by
    refine (hint2.add hint3).congr ?_
    filter_upwards with p
    have hsplit0 : G1 p.1 p.2 = G2 p.1 p.2 + G3 p.1 p.2 := by
      rw [hG1, hG2, hG3]
      simp only [Fp, AA, BB, U, Hh]
      ring
    simp only [Pi.add_apply]
    exact hsplit0.symm
  -- ## the pointwise splitting
  have hsplit : ∀ z θ, G1 z θ = G2 z θ + G3 z θ := by
    intro z θ
    have h1 : G1 z θ = (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
        * Fp u z θ := by rw [hG1]
    have h2 : G2 z θ = (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
        * (AA u z θ * BB u z θ
            + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ) := by rw [hG2]
    have h3 : G3 z θ = (Work.Spaces.w z) ^ 2 * sigE θ * (χ n z * ψ ε θ)
        * (U u z θ * Hh u z θ) := by rw [hG3]
    rw [h1, h2, h3]
    simp only [Fp, AA, BB, U, Hh]
    ring
  -- ## the two halves
  have hII1 : II G1 = -II G4 := zibpChain h n hε
  have hII3 : II G3 = -II G5 + 2 * Work.Spaces.eta * II G6 - II G7 := by
    have ht := thetaChain h n hε
    convert ht using 1 <;> rfl
  have hII23 : II G2 + II G3 = II G1 := by
    rw [II_eq_integral hint2, II_eq_integral hint3, II_eq_integral hint1,
      ← MeasureTheory.integral_add hint2 hint3]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with p
    exact (hsplit p.1 p.2).symm
  have hgoal : II G2 = -II G4 + II G5 - 2 * Work.Spaces.eta * II G6 + II G7 := by
    linarith [hII1, hII3, hII23]
  exact hgoal

end Work.FTS.EllipticEst.I1Ae
