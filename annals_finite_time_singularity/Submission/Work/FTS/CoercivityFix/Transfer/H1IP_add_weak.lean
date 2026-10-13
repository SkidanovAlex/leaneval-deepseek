/-
# Additivity of `H1IP` in its first argument, from block continuity on `Qd`

`Work.Coercivity.H1IP α` is a sum of four weighted `L²` pairings

  `wip ρ A B = ∫_{z ∈ [0,∞)} ∫_{θ ∈ [0,π/2]} A z θ * B z θ * ρ z θ`,

applied to the two profiles and to their `D_z`- and `D_θ`-derivatives.  Since the Bochner
integral is total, `wip` is additive in `A` only when the pairing integrands are *honest*
(`Work.Coercivity.PairHonest`); honesty does **not** follow from `HkMem` alone —
`Work.Coercivity.H1IP_add_fails` exhibits a non-a.e.-strongly-measurable two-valued
multiplier for which both sides are junk (`0`).

This file proves the additivity from the weakest hypotheses that still give honesty and
that the intended application (the splitting of `𝓛̂(D_θ f) + E₁ α f` and of
`𝓛̂(D_z f) + E₂ α f`) really satisfies:

* `HkMem α 1` of the three arguments — each of the two blocks of a pairing is `L²`, so
  AM–GM bounds the pairing integrand by the integrable average
  `(HkIntegrand α 1 a + HkIntegrand α 1 b)/2`;
* *continuity of the three blocks* `a`, `D_z a`, `D_θ a` of every argument on the open
  quadrant `Qd = (0,∞) × (0,π/2)`: this gives a.e. strong measurability on `Iz × Iθ`
  (`Spaces.aesm_of_continuousOn_Qd`), while the factor `lamEta`/`lamGam`/`lamW` contains
  `w(z)² = ((1+z)²/z²)²`, which vanishes at `z = 0`, killing each pairing integrand there;
  the criterion `Assembly.I2Mem_of_dominated` then yields honesty.

No smoothness, no boundary traces and no `L₁₂`-zero-mode condition is used.  The
linearity identities `D_z (a₁ + a₂) = D_z a₁ + D_z a₂` and `D_θ (a₁ + a₂) = ⋯` are *not*
re-derived: they are hypotheses, because in the intended application the summands are
differentiable only a.e. (their `θ`-slices may jump at `θ = 0, π/2`).

The four `PairHonest` lemmas below are the `Qd`-continuity analogues of
`Assembly.PairHonest_eta_Q`, `…_etaDz_Q`, `…_gam_Q`, `…_w_Q` (which assume the stronger
`SmoothQuad`), and the final assembly mirrors `Assembly.H1IP_add_Q`.
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.wip_add_of_PairHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.CoercivityFix.Assembly

/-! ## Honesty of the four pairings from block continuity on the open quadrant -/

/-- Honesty of the `D_z⁰`-pairing `∫ a b ρη` of `H1IP`, from continuity of `a`, `b` on
the open quadrant. -/
theorem PairHonest_eta_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.Xeta_mul_eq a b z θ hθ]
    calc |Work.Coercivity.Xeta a z θ * Work.Coercivity.Xeta b z θ|
        = |Work.Coercivity.Xeta a z θ| * |Work.Coercivity.Xeta b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xeta a z θ) ^ 2 + (Work.Coercivity.Xeta b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_Xeta_le_HkIntegrand α a z θ
          have h2 := sq_Xeta_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the `D_z`-pairing `∫ (D_z a)(D_z b) ρη` of `H1IP`, from continuity of
`D_z a`, `D_z b` on the open quadrant. -/
theorem PairHonest_etaDz_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry (Work.Spaces.Dz a)) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry (Work.Spaces.Dz b)) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta
      (Work.Spaces.Dz a) (Work.Spaces.Dz b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dz a z θ * Work.Spaces.Dz b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz a) p
            * Function.uncurry (Work.Spaces.Dz b) p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XetaDz_mul_eq a b z θ hθ]
    calc |Work.Coercivity.XetaDz a z θ * Work.Coercivity.XetaDz b z θ|
        = |Work.Coercivity.XetaDz a z θ| * |Work.Coercivity.XetaDz b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XetaDz a z θ) ^ 2
            + (Work.Coercivity.XetaDz b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XetaDz_le_HkIntegrand α a z θ
          have h2 := sq_XetaDz_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the `D_θ`-pairing `∫ (D_θ a)(D_θ b) ργ` of `H1IP`, from continuity of
`D_θ a`, `D_θ b` on the open quadrant. -/
theorem PairHonest_gam_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry (Work.Spaces.Dth a)) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry (Work.Spaces.Dth b)) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest (Work.Coercivity.lamGam α)
      (Work.Spaces.Dth a) (Work.Spaces.Dth b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dth a z θ * Work.Spaces.Dth b z θ * Work.Coercivity.lamGam α z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dth a) p
            * Function.uncurry (Work.Spaces.Dth b) p
            * Function.uncurry (Work.Coercivity.lamGam α) p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul (continuousOn_lamGam α)
  · intro θ
    simp [Work.Coercivity.lamGam, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XgamDth_mul_eq α a b z θ hθ]
    calc |Work.Coercivity.XgamDth α a z θ * Work.Coercivity.XgamDth α b z θ|
        = |Work.Coercivity.XgamDth α a z θ| * |Work.Coercivity.XgamDth α b z θ| :=
          abs_mul _ _
      _ ≤ ((Work.Coercivity.XgamDth α a z θ) ^ 2
            + (Work.Coercivity.XgamDth α b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XgamDth_le_HkIntegrand α a z θ
          have h2 := sq_XgamDth_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the unweighted pairing `∫ a b w²` of `H1IP`, from continuity of `a`, `b`
on the open quadrant.  Off the two null endpoints of `Iθ` the plain `w²`-block is
dominated by the `D_z⁰`-summand of the `ℋ¹`-integrand, since `sin 2θ ≤ 1`. -/
theorem PairHonest_w_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamW a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamW z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamW p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamW
  · intro θ
    simp [Work.Coercivity.lamW, Work.Spaces.w]
  · intro z _
    filter_upwards [sq_Xw_le_HkIntegrand_ae α a z, sq_Xw_le_HkIntegrand_ae α b z]
      with θ h1 h2
    have hXw : Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ
        = a z θ * b z θ * Work.Coercivity.lamW z θ := by
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]; ring
    rw [← hXw]
    calc |Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ|
        = |Work.Coercivity.Xw a z θ| * |Work.Coercivity.Xw b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xw a z θ) ^ 2 + (Work.Coercivity.Xw b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          linarith

/-! ## The additivity of `H1IP` -/

theorem H1IP_add_weak (α : ℝ) {a₁ a₂ b : ℝ → ℝ → ℝ}
    (hm1 : Work.Spaces.HkMem α 1 a₁) (hm2 : Work.Spaces.HkMem α 1 a₂)
    (hmb : Work.Spaces.HkMem α 1 b)
    (hc1 : ContinuousOn (Function.uncurry a₁) Work.Construction.Qd)
    (hc2 : ContinuousOn (Function.uncurry a₂) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hdz1 : ContinuousOn (Function.uncurry (Work.Spaces.Dz a₁)) Work.Construction.Qd)
    (hdz2 : ContinuousOn (Function.uncurry (Work.Spaces.Dz a₂)) Work.Construction.Qd)
    (hdzb : ContinuousOn (Function.uncurry (Work.Spaces.Dz b)) Work.Construction.Qd)
    (hdth1 : ContinuousOn (Function.uncurry (Work.Spaces.Dth a₁)) Work.Construction.Qd)
    (hdth2 : ContinuousOn (Function.uncurry (Work.Spaces.Dth a₂)) Work.Construction.Qd)
    (hdthb : ContinuousOn (Function.uncurry (Work.Spaces.Dth b)) Work.Construction.Qd)
    (hdz : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (a₁ + a₂) z θ = Work.Spaces.Dz a₁ z θ + Work.Spaces.Dz a₂ z θ)
    (hdth : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (a₁ + a₂) z θ = Work.Spaces.Dth a₁ z θ + Work.Spaces.Dth a₂ z θ) :
    Work.Coercivity.H1IP α (a₁ + a₂) b = Work.Coercivity.H1IP α a₁ b + Work.Coercivity.H1IP α a₂ b := by
  have hA : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz (a₁ + a₂))
        (Work.Spaces.Dz b)
      = Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₁) (Work.Spaces.Dz b)
        + Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₂) (Work.Spaces.Dz b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dz (a₁ + a₂))
      (A' := Work.Spaces.Dz a₁ + Work.Spaces.Dz a₂) hdz]
    exact Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta (Work.Spaces.Dz a₁)
      (Work.Spaces.Dz a₂) (Work.Spaces.Dz b)
      (PairHonest_etaDz_Qd α hdz1 hdzb hm1 hmb)
      (PairHonest_etaDz_Qd α hdz2 hdzb hm2 hmb)
  have hB : Work.Coercivity.wip Work.Coercivity.lamEta (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamEta a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamEta a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta a₁ a₂ b
      (PairHonest_eta_Qd α hc1 hcb hm1 hmb) (PairHonest_eta_Qd α hc2 hcb hm2 hmb)
  have hC : Work.Coercivity.wip Work.Coercivity.lamW (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamW a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamW a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamW a₁ a₂ b
      (PairHonest_w_Qd α hc1 hcb hm1 hmb) (PairHonest_w_Qd α hc2 hcb hm2 hmb)
  have hD : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth (a₁ + a₂))
        (Work.Spaces.Dth b)
      = Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
          (Work.Spaces.Dth b)
        + Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₂)
          (Work.Spaces.Dth b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dth (a₁ + a₂))
      (A' := Work.Spaces.Dth a₁ + Work.Spaces.Dth a₂) hdth]
    exact Work.Coercivity.wip_add_of_PairHonest (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
      (Work.Spaces.Dth a₂) (Work.Spaces.Dth b)
      (PairHonest_gam_Qd α hdth1 hdthb hm1 hmb)
      (PairHonest_gam_Qd α hdth2 hdthb hm2 hmb)
  have hEtaW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = Work.Coercivity.lamEta := rfl
  have hGamW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Coercivity.lamGam α := rfl
  have hWtW : (fun z _ => Work.Spaces.w z ^ 2) = Work.Coercivity.lamW := rfl
  simp only [Work.Coercivity.H1IP]
  rw [hEtaW, hGamW, hWtW, hA, hB, hC, hD]
  ring

end

end Work.FTS.CoercivityFix.Transfer
