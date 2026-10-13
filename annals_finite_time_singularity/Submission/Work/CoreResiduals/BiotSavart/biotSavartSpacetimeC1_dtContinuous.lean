/-
# `Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_dtContinuous`

The window theorem `biotSavartSpacetimeC1_holds` with the *Lipschitz* clause
`TimeDerivLocallyLipschitz` weakened to the *continuity* clause `TimeDerivLocallyContinuous`
(`Submission/Work/CoreResiduals/BiotSavart/TimeDerivContinuous.lean`).

The proof is verbatim that of `biotSavartSpacetimeC1_holds` (whose auxiliary lemmas are re-used by
import), with the single observation that the Lipschitz clause is used there only to derive the
*continuity in `t`* of the slices `∂ₜω(y,·)` (via `continuousAt_of_norm_sub_le_mul_abs`), which is
exactly the new hypothesis.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.TimeDerivContinuous
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
import Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
import Submission.Work.CoreResiduals.BiotSavart.norm_sub_le_of_timeDeriv_bound
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsDerivCLM_param
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_biotSavart_param

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

theorem biotSavartSpacetimeC1_of_dtContinuous {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R T : ℝ}
    (hadm : Work.CoreResiduals.BSAdmissibleOnWindow ω R T)
    (hdtc : Work.CoreResiduals.TimeDerivLocallyContinuous ω T) :
    ∀ x₀ : Work.LWP.R3, ∀ t₀ ∈ Work.ConstructionInstance.preWindow T,
      ContDiffAt ℝ 1
        (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) (x₀, t₀) := by
  intro x₀ t₀ ht₀
  obtain ⟨hRpos, hsuppL, hbddL, hholdL, haesmL, hdcL, hbddDL, haesmDL⟩ := hadm
  obtain ⟨ε₁, hε₁, M, hMb⟩ := hbddL t₀ ht₀
  obtain ⟨ε₂, hε₂, c, hc, C, hCb⟩ := hholdL t₀ ht₀
  obtain ⟨ε₃, hε₃, haesm₀⟩ := haesmL t₀ ht₀
  obtain ⟨ε₄, hε₄, hdc₀⟩ := hdcL t₀ ht₀
  obtain ⟨ε₅, hε₅, M₁, hM₁b⟩ := hbddDL t₀ ht₀
  obtain ⟨ε₆, hε₆, haesmD₀⟩ := haesmDL t₀ ht₀
  obtain ⟨ε₇, hε₇, hcontDt⟩ := hdtc t₀ ht₀
  -- the master window `Ibig = {t | |t - t₀| < δ}`, contained in every locality of the bundle
  set δ : ℝ := min (min (min ε₁ ε₂) (min ε₃ ε₄)) (min (min ε₅ ε₆) ε₇) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄)) (lt_min (lt_min hε₅ hε₆) hε₇)
  have hδ1 : δ ≤ ε₁ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ2 : δ ≤ ε₂ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ3 : δ ≤ ε₃ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ4 : δ ≤ ε₄ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ5 : δ ≤ ε₅ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ6 : δ ≤ ε₆ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ7 : δ ≤ ε₇ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set Ibig : Set ℝ := Set.Ioo (t₀ - δ) (t₀ + δ) with hIbigdef
  set Ismall : Set ℝ := Set.Ioo (t₀ - δ / 2) (t₀ + δ / 2) with hIsmalldef
  have hIbigmem : ∀ t : ℝ, t ∈ Ibig ↔ t₀ - δ < t ∧ t < t₀ + δ := by
    intro t; rw [hIbigdef, Set.mem_Ioo]
  have hIsmallmem : ∀ t : ℝ, t ∈ Ismall ↔ t₀ - δ / 2 < t ∧ t < t₀ + δ / 2 := by
    intro t; rw [hIsmalldef, Set.mem_Ioo]
  have hsmall : ∀ t ∈ Ismall, t ∈ Ibig := by
    intro t ht
    obtain ⟨h1, h2⟩ := (hIsmallmem t).mp ht
    rw [hIbigmem t]
    exact ⟨by linarith, by linarith⟩
  have hwin : ∀ t ∈ Ismall, ∀ s : ℝ, s ∈ Set.Ioo (t - δ / 2) (t + δ / 2) → s ∈ Ibig := by
    intro t ht s hs
    obtain ⟨h1, h2⟩ := (hIsmallmem t).mp ht
    obtain ⟨h3, h4⟩ := hs
    rw [hIbigmem s]
    exact ⟨by linarith, by linarith⟩
  have hwinAbs : ∀ t ∈ Ismall, ∀ s : ℝ, |s - t| < δ / 2 → s ∈ Ibig := by
    intro t ht s hs
    refine hwin t ht s ?_
    rw [Set.mem_Ioo]
    rw [abs_lt] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hIbigopen : IsOpen Ibig := by rw [hIbigdef]; exact isOpen_Ioo
  have hIsmallopen : IsOpen Ismall := by rw [hIsmalldef]; exact isOpen_Ioo
  have ht₀small : t₀ ∈ Ismall := by
    rw [hIsmallmem t₀]; exact ⟨by linarith, by linarith⟩
  -- the local hypotheses, transported to `Ibig`, with nonnegative constants
  have hsuppI : ∀ t ∈ Ibig, ∀ y, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
    intro t ht y hy
    exact hsuppL t y hy
  have hbddI : ∀ t ∈ Ibig, ∀ y, ‖ω y t‖ ≤ max M 0 := by
    intro t ht y
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₁) (t₀ + ε₁) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact le_trans (hMb t ht' y) (le_max_left _ _)
  have hholdI : ∀ t ∈ Ibig, ∀ a b : Work.LWP.R3,
      ‖ω a t - ω b t‖ ≤ max C 0 * ‖a - b‖ ^ c := by
    intro t ht a b
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₂) (t₀ + ε₂) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact norm_sub_le_max_mul_rpow hc (hCb t ht' a b)
  have haesmI : ∀ t ∈ Ibig,
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume := by
    intro t ht
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₃) (t₀ + ε₃) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact haesm₀ t ht'
  have hdcI : ∀ t ∈ Ibig, ∀ y,
      HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t := by
    intro t ht y
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₄) (t₀ + ε₄) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact hdc₀ t ht' y
  have hbddDI : ∀ t ∈ Ibig, ∀ y,
      ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ max M₁ 0 := by
    intro t ht y
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₅) (t₀ + ε₅) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact le_trans (hM₁b t ht' y) (le_max_left _ _)
  have haesmDI : ∀ t ∈ Ibig,
      MeasureTheory.AEStronglyMeasurable (fun y => FiniteTimeSingularity.timeDeriv ω y t)
        MeasureTheory.volume := by
    intro t ht
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    have ht' : t ∈ Set.Ioo (t₀ - ε₆) (t₀ + ε₆) := by
      rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩
    exact haesmD₀ t ht'
  have hderivI : ∀ t ∈ Ibig, ∀ s ∈ Ibig, ∀ y,
      ‖ω y t - ω y s‖ ≤ max M₁ 0 * |t - s| := by
    intro t ht s hs y
    exact norm_sub_le_of_timeDeriv_bound (le_max_right _ _)
      (hIbigdef ▸ convex_Ioo (t₀ - δ) (t₀ + δ))
      (fun u hu => hdcI u hu) (fun u hu => hbddDI u hu) t ht s hs y
  have hJoint : ∀ x : Work.LWP.R3, ∀ t ∈ Ibig,
      ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x, t) := by
    intro x t ht
    exact continuousAt_uncurry_of_holder_lipschitz hc (le_max_right _ _) (le_max_right _ _)
      (hIbigopen.mem_nhds ht) ht (fun u hu => hholdI u hu)
      (fun u hu v hv => hderivI u hu v hv)
  have hTcontω : ∀ t ∈ Ibig, ∀ a : Work.LWP.R3,
      ContinuousAt (fun s : ℝ => ω a s) t := by
    intro t ht a
    exact continuousAt_of_norm_sub_le_mul_abs (hIbigopen.mem_nhds ht)
      (fun s hs => hderivI s hs t ht a)
  have hTcontDt : ∀ t ∈ Ibig, ∀ a : Work.LWP.R3,
      ContinuousAt (fun s : ℝ => FiniteTimeSingularity.timeDeriv ω a s) t := by
    intro t ht a
    refine hcontDt t ?_ a
    obtain ⟨h1, h2⟩ := (hIbigmem t).mp ht
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hδ7], by linarith [hδ7]⟩
  set ρ : ℝ := R + ‖x₀‖ + 2 with hρdef
  have hsuppD : ∀ t ∈ Ibig, ∀ y,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
    intro t ht y hy
    obtain ⟨εt, hεt, hεtsub⟩ := Metric.mem_nhds_iff.mp (hIbigopen.mem_nhds ht)
    have hεt' : ∀ s : ℝ, s ∈ Set.Ioo (t - εt) (t + εt) → s ∈ Ibig := by
      intro s hs
      refine hεtsub ?_
      rw [Set.mem_Ioo] at hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    by_contra hyR
    exact hy (Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
      (t := t) (ε := εt)
      (fun s hs => hdcI s (hεt' s hs))
      (fun s hs => hsuppI s (hεt' s hs))
      (by rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩) hyR)
  -- the `x`-partial derivative at every point of the window
  have hxderiv : ∀ (x : Work.LWP.R3) (t : ℝ), x ∈ Metric.ball x₀ 1 → t ∈ Ismall →
      HasFDerivAt (fun x' => bsSTField ω x' t) (bsXDeriv ω ρ x t) x := by
    intro x t hx ht
    have htI : t ∈ Ibig := hsmall t ht
    have hxn : ‖x - x₀‖ < 1 := by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
    have hxnorm : ‖x‖ < ‖x₀‖ + 1 := by
      have h2 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
        have h3 := norm_add_le x₀ (x - x₀)
        rwa [add_sub_cancel] at h3
      linarith
    have hxρ : R + ‖x‖ < ρ := by rw [hρdef]; linarith
    simpa [bsXDeriv, bsSTField] using
      (hasFDerivAt_biotSavart_slice (ω := fun y => ω y t) (R := R) (M := max M 0) (C := max C 0)
        (c := c) (ρ := ρ) hRpos (le_max_right _ _) hc (hbddI t htI) (hsuppI t htI)
        (haesmI t htI) (fun a b => hholdI t htI a b) hxρ)
  -- the `t`-partial derivative at every point of the window
  have htxderiv : ∀ (x : Work.LWP.R3) (t : ℝ), t ∈ Ismall →
      HasFDerivAt (fun s : ℝ => bsSTField ω x s) (bsTDeriv ω x t) t := by
    intro x t ht
    exact hasFDerivAt_bsSTField_time (ω := ω) (R := R) (M := max M 0) (M₁ := max M₁ 0)
      (ε := δ / 2) (t := t) hRpos.le (le_max_right _ _) (le_max_right _ _)
      (by linarith [hδpos])
      (fun s hs => hbddI s (hwin t ht s hs))
      (fun s hs => hbddDI s (hwin t ht s hs))
      (fun s hs => hdcI s (hwin t ht s hs))
      (fun s hs => hsuppI s (hwin t ht s hs))
      (fun s hs => haesmI s (hwin t ht s hs))
      x
  set U : Set (Work.LWP.R3 × ℝ) := Metric.ball x₀ 1 ×ˢ Ismall with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact Metric.isOpen_ball.prod hIsmallopen
  have hUnhds : U ∈ 𝓝 (x₀, t₀) := by
    rw [hUdef, nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
      (hIsmallopen.mem_nhds ht₀small)
  -- continuity of the `x`-partial at every point of `U`
  have hF₁cont : ∀ q : Work.LWP.R3 × ℝ, q ∈ U →
      ContinuousAt (fun q' : Work.LWP.R3 × ℝ => bsXDeriv ω ρ q'.1 q'.2) q := by
    intro q hq
    obtain ⟨hqx, hqt⟩ := hq
    have htI : q.2 ∈ Ibig := hsmall q.2 hqt
    have hA : ContinuousAt (fun q' : Work.LWP.R3 × ℝ =>
        bsDerivCLM (fun y => ω y q'.2) ρ q'.1) q :=
      continuousAt_bsDerivCLM_param (ω := ω) (δ := δ / 2) (c := c) (C := max C 0) (ρ := ρ)
        (x₀ := q.1) (t₀ := q.2) (by linarith [hδpos]) hc (le_max_right _ _)
        (fun s hs => hholdI s (hwinAbs q.2 hqt s hs))
        (hJoint q.1 q.2 htI)
        (fun a => hTcontω q.2 htI a)
    have hsm : ContinuousAt (fun q' : Work.LWP.R3 × ℝ =>
        (4 * Real.pi)⁻¹ • bsDerivCLM (fun y => ω y q'.2) ρ q'.1) q :=
      (continuousAt_const : ContinuousAt
        (fun _ : Work.LWP.R3 × ℝ => (4 * Real.pi)⁻¹) q).smul hA
    simpa [bsXDeriv] using hsm
  -- continuity of the `t`-partial at every point of `U`
  have hF₂cont : ∀ q : Work.LWP.R3 × ℝ, q ∈ U →
      ContinuousAt (fun q' : Work.LWP.R3 × ℝ => bsTDeriv ω q'.1 q'.2) q := by
    intro q hq
    obtain ⟨hqx, hqt⟩ := hq
    have htI : q.2 ∈ Ibig := hsmall q.2 hqt
    have hxn : ‖q.1 - x₀‖ < 1 := by rw [Metric.mem_ball, dist_eq_norm] at hqx; exact hqx
    have hxnorm : ‖q.1‖ < ‖x₀‖ + 1 := by
      have h2 : ‖q.1‖ ≤ ‖x₀‖ + ‖q.1 - x₀‖ := by
        have h3 := norm_add_le x₀ (q.1 - x₀)
        rwa [add_sub_cancel] at h3
      linarith
    have hxρ : R + ‖q.1‖ + 1 < ρ := by rw [hρdef]; linarith
    have hB : ContinuousAt (fun q' : Work.LWP.R3 × ℝ =>
        Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q'.2) q'.1) q :=
      continuousAt_biotSavart_param
        (ω := fun y t => FiniteTimeSingularity.timeDeriv ω y t)
        (δ := δ / 2) (R := R) (M := max M₁ 0) (ρ := ρ) (x₀ := q.1) (t₀ := q.2)
        (by linarith [hδpos]) (le_max_right _ _) hxρ
        (fun s hs => hbddDI s (hwinAbs q.2 hqt s hs))
        (fun s hs => hsuppD s (hwinAbs q.2 hqt s hs))
        (fun s hs => haesmDI s (hwinAbs q.2 hqt s hs))
        (fun a => hTcontDt q.2 htI a)
    have hts : Continuous (fun v : Work.LWP.R3 =>
        ContinuousLinearMap.toSpanSingleton ℝ v) :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Work.LWP.R3)).continuous
    have hCLM : ContinuousAt (fun q' : Work.LWP.R3 × ℝ =>
        ContinuousLinearMap.toSpanSingleton ℝ
          (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q'.2) q'.1)) q :=
      hts.continuousAt.comp hB
    simpa [bsTDeriv] using hCLM
  -- the same two continuities in the uncurried form used by the product-derivative lemma
  have hF₁contU : ∀ q : Work.LWP.R3 × ℝ, q ∈ U →
      ContinuousAt (Function.uncurry (bsXDeriv ω ρ)) q := by
    intro q hq
    have heq : Function.uncurry (bsXDeriv ω ρ)
        = (fun q' : Work.LWP.R3 × ℝ => bsXDeriv ω ρ q'.1 q'.2) := by
      funext q'; obtain ⟨a, b⟩ := q'; rfl
    rw [heq]
    exact hF₁cont q hq
  have hF₂contU : ∀ q : Work.LWP.R3 × ℝ, q ∈ U →
      ContinuousAt (Function.uncurry (bsTDeriv ω)) q := by
    intro q hq
    have heq : Function.uncurry (bsTDeriv ω)
        = (fun q' : Work.LWP.R3 × ℝ => bsTDeriv ω q'.1 q'.2) := by
      funext q'; obtain ⟨a, b⟩ := q'; rfl
    rw [heq]
    exact hF₂cont q hq
  -- continuity of the assembled derivative
  have hcU : ContinuousOn (fun q : Work.LWP.R3 × ℝ =>
      (bsXDeriv ω ρ q.1 q.2).coprod (bsTDeriv ω q.1 q.2)) U := by
    intro q hq
    have hpair : ContinuousAt (fun q' : Work.LWP.R3 × ℝ =>
        (bsXDeriv ω ρ q'.1 q'.2, bsTDeriv ω q'.1 q'.2)) q :=
      (hF₁cont q hq).prodMk (hF₂cont q hq)
    have hcopC : Continuous (fun p : (Work.LWP.R3 →L[ℝ] Work.LWP.R3) × (ℝ →L[ℝ] Work.LWP.R3) =>
        p.1.coprod p.2) :=
      (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (S := ℝ) (E := Work.LWP.R3) (F := ℝ)
        (G := Work.LWP.R3)).continuous
    simpa [Function.comp_def] using (hcopC.continuousAt.comp hpair).continuousWithinAt
  -- the joint derivative at every point of `U`, from the two partials
  have hdiff : ∀ q ∈ U, HasFDerivWithinAt
      (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
      ((bsXDeriv ω ρ q.1 q.2).coprod (bsTDeriv ω q.1 q.2)) U q := by
    intro q hq
    have hqU : U ∈ 𝓝 q := hUopen.mem_nhds hq
    have hgoal : HasFDerivWithinAt (Function.uncurry (bsSTField ω))
        ((bsXDeriv ω ρ q.1 q.2).coprod (bsTDeriv ω q.1 q.2)) U q :=
      (hasStrictFDerivAt_uncurry_coprod (u := q) (f := bsSTField ω) (f₁ := bsXDeriv ω ρ)
        (f₂ := bsTDeriv ω)
        (by
          filter_upwards [hqU] with v hv
          obtain ⟨x, t⟩ := v
          exact hxderiv x t hv.1 hv.2)
        (by
          filter_upwards [hqU] with v hv
          obtain ⟨x, t⟩ := v
          exact htxderiv x t hv.2)
        (hF₁contU q hq) (hF₂contU q hq)).hasFDerivAt.hasFDerivWithinAt
    have hfun : (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
        = Function.uncurry (bsSTField ω) := by
      funext q; obtain ⟨a, b⟩ := q; rfl
    rw [hfun]
    exact hgoal
  -- assemble the `C¹` statement on the open neighbourhood `U`
  have key : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
      (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) U := by
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn]
    exact ⟨fun h => absurd h (by simp), fun q => (bsXDeriv ω ρ q.1 q.2).coprod (bsTDeriv ω q.1 q.2),
      contDiffOn_zero.mpr hcU, hdiff⟩
  have hkey : ContDiffOn ℝ 1
      (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) U := by
    simpa using key
  exact hkey.contDiffAt hUnhds

end Work.CoreResiduals.BiotSavart
