import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.BSSwirl.NewtonPotentialAux
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_dtContinuous =====
section

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
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity in `t` of the glued `∂ₜ`-slices.**  `dtExt ω S y ·` is the composition of the
`∂ₜ`-slice `∂ₜω(y,·)` with the clamping map `t ↦ max 0 (min t S)`; since that map is `1`-Lipschitz
and the `∂ₜ`-slice is `α`-Hölder on `Icc 0 S`, the glued slice is `α`-Hölder on all of `ℝ`, hence
continuous everywhere. -/
theorem continuousAt_dtExt {α : NNReal} (hα : 0 < (α : ℝ)) {ω : R3 → ℝ → R3} {S : ℝ}
    (hS : 0 < S) {N₁ : ℝ}
    (hN₁ : ∀ y : R3, ∀ u ∈ Set.Icc (0:ℝ) S, ∀ v ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω y u - FiniteTimeSingularity.timeDeriv ω y v‖
        ≤ N₁ * |u - v| ^ (α : ℝ))
    (y : R3) (t : ℝ) : ContinuousAt (fun s : ℝ => dtExt ω S y s) t := by
  set N₁' := max N₁ 0 with hN₁'def
  have hN₁'nn : 0 ≤ N₁' := le_max_right _ _
  have hb : ∀ s : ℝ, ‖dtExt ω S y s - dtExt ω S y t‖ ≤ N₁' * |s - t| ^ (α : ℝ) := by
    intro s
    have hs_mem : max 0 (min s S) ∈ Set.Icc (0:ℝ) S :=
      ⟨le_max_left _ _, max_le (le_of_lt hS) (min_le_right _ _)⟩
    have ht_mem : max 0 (min t S) ∈ Set.Icc (0:ℝ) S :=
      ⟨le_max_left _ _, max_le (le_of_lt hS) (min_le_right _ _)⟩
    have hclamp : |max 0 (min s S) - max 0 (min t S)| ≤ |s - t| := by
      have h1 := abs_max_sub_max_le_max 0 (min s S) 0 (min t S)
      have h2 := abs_min_sub_min_le_max s S t S
      have h3 : max |0 - (0:ℝ)| |min s S - min t S| = |min s S - min t S| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      have h4 : max |s - t| |S - S| = |s - t| := by
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      rw [h3] at h1
      rw [h4] at h2
      exact le_trans h1 h2
    rw [dtExt_eq_clamp (ω := ω) (S := S) (y := y) (t := s) hS,
        dtExt_eq_clamp (ω := ω) (S := S) (y := y) (t := t) hS]
    refine le_trans (hN₁ y _ hs_mem _ ht_mem) ?_
    have hpow : |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ) ≤ |s - t| ^ (α : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hclamp (le_of_lt hα)
    calc N₁ * |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ)
        ≤ N₁' * |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ N₁' * |s - t| ^ (α : ℝ) := mul_le_mul_of_nonneg_left hpow hN₁'nn
  exact continuousAt_of_norm_sub_le_rpow (f := fun s : ℝ => dtExt ω S y s) hα hN₁'nn hb

/-- **The two-sided time-extension of a bundled strip vorticity.**

Let `0 < α < 1`, let `S > 0`, let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`,
and assume additionally that the `∂ₜ`-slices `x ↦ ∂ₜω(x,t)` are Hölder in `x`, uniformly on the
strip (this is the conclusion of `timeDeriv_xHolderOn_of_stripBundle`; the extension needs it in
order to be `x`-Hölder for `t < 0`).

Conclusion: there is an extension `ω_ext` of `ω` in the time variable, agreeing with `ω` on the
strip, which satisfies

* the *window* admissibility bundle `BSAdmissibleOnWindow ω_ext R (S+1)` — the hypotheses of
  `Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds` apart from the Lipschitz clause — and
* `Work.CoreResiduals.TimeDerivLocallyContinuous ω_ext (S+1)` — the `∂ₜ`-slices are locally
  continuous in `t`.

**Suggested construction** (glue `ω` to its affine continuation outside the strip):
`ω_ext y t = ω y 0 + t • ∂ₜω(y,0)` for `t ≤ 0`; `= ω y t` for `0 ≤ t ≤ S`;
`= ω y S + (t-S) • ∂ₜω(y,S)` for `t ≥ S`.

Checks needed:

* *agreement* on `Icc 0 S`, and `ω_ext y 0 = ω y 0`, `ω_ext y S = ω y S` at the junctions;
* *support*: for `y ∉ closedBall 0 R` one has `ω y t = 0` for `t ∈ Icc 0 S`, hence `ω y 0 = 0`,
  `ω y S = 0`, and moreover `∂ₜω(y,0) = 0`, `∂ₜω(y,S) = 0`: the strip bundle gives the (two-sided)
  `HasDerivAt` of `s ↦ ω y s` at the endpoint times, while the right (resp. left) difference quotient
  vanishes identically on `(0, min(S,1))` (resp. `(max(S-1,0), S)`), so the derivative is `0` — e.g.
  by combining `h.hasDerivWithinAt` on `Ici 0` with the `HasDerivWithinAt` of the constant `0` and
  `HasDerivWithinAt.unique` (`uniqueDiffWithinAt_Ici`), or by `HasDerivWithinAt.union`;
* the *local clauses of `BSAdmissibleOnWindow`* (for `t₀ ∈ preWindow (S+1) = Ioo (-2) (S+1)`, with a
  locality `ε` chosen so that the window lies in at most one of the three regimes, or straddles a
  junction): local boundedness `M + |t|M₁`; local `x`-Hölder (from the strip clause at times in
  `Icc 0 S`, and from the strip clause at the endpoint together with the extra `∂ₜ`-Hölder
  hypothesis on the affine pieces); local measurability (`AEStronglyMeasurable.add`, `.const_smul`
  of the strip measurability clauses at the endpoint times); local `t`-differentiability with the
  matching `timeDeriv` (the affine pieces give `HasDerivAt ... (∂ₜω(y,0)) t`, and at a junction the
  required statement is `HasDerivAt (fun s => ω_ext y s) (timeDeriv ω_ext y 0) 0` for the *same*
  value, which follows from `HasDerivWithinAt.union` of the two one-sided derivatives — the value
  `timeDeriv ω_ext y 0` is then `∂ₜω(y,0)` by `HasDerivAt.unique`/`HasDerivAt.deriv`);
  local bound `max M₁ 0` on `∂ₜω_ext`; local measurability of the `∂ₜω_ext`-slices; and
* *continuity in `t` of the `∂ₜ`-slices*: on the affine pieces `∂ₜω_ext y ·` is constant, and across
  a junction the strip side converges to the endpoint value by the `α`-Hölder clause of `∂ₜω`
  (`TimeDerivStripHolder` with one of the two times equal to `0` resp. `S`). -/
theorem exists_windowExtension_of_stripBundle {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : BSAdmissibleStripFull α ω R S)
    (hxH : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c) :
    ∃ ω_ext : Work.LWP.R3 → ℝ → Work.LWP.R3,
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3, ω_ext y t = ω y t) ∧
      BSAdmissibleOnWindow ω_ext R (S + 1) ∧
      TimeDerivLocallyContinuous ω_ext (S + 1) := by
  have hstrip := hbun.1
  have hTD := hbun.2.1
  have hTDH := hbun.2.2
  obtain ⟨hRpos, hsupp, hbdd, hholder, htholder, hslices⟩ := hstrip
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨H, hH⟩ := hholder
  have hdiff := hTD.1
  obtain ⟨M₁, hM₁⟩ := hTD.2.1
  have hdtmeas := hTD.2.2
  obtain ⟨N₁, hN₁⟩ := hTDH
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hSmem : S ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hS, le_refl S⟩
  refine ⟨windowExt ω S, ?_, ?_, ?_⟩
  · intro t ht y
    exact windowExt_of_mem_Icc ht
  · refine ⟨hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t y hy
      by_contra hyb
      exact hy (windowExt_eq_zero_of_notMem_closedBall hS hsupp hdiff hyb t)
    · intro t₀ _
      obtain ⟨M', hM'⟩ := windowExt_localBdd hS hbun t₀
      exact ⟨1, one_pos, M', fun t ht y => hM' t ht y⟩
    · intro t₀ _
      obtain ⟨c, hc, C, hC⟩ := windowExt_holder_bound hα hS hbun hxH t₀
      exact ⟨1, one_pos, c, hc, C, fun t ht a b => hC t ht a b⟩
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      by_cases h : t ≤ 0
      · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
            = fun y => ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact windowExt_of_nonpos h
        rw [heq]
        exact (hslices 0 h0mem).add ((hdtmeas 0 h0mem).const_smul t)
      · by_cases h2 : t ≤ S
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t) = fun y => ω y t := by
            funext y; exact windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq]
          exact hslices t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
              = fun y => ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq]
          exact (hslices S hSmem).add ((hdtmeas S hSmem).const_smul (t - S))
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      exact hasDerivAt_windowExt hS hdiff y t
    · intro t₀ _
      refine ⟨1, one_pos, max M₁ 0, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      by_cases h : t ≤ 0
      · rw [dtExt_of_nonpos h]
        exact le_trans (hM₁ 0 h0mem y) (le_max_left _ _)
      · by_cases h2 : t ≤ S
        · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
          exact le_trans (hM₁ t ⟨le_of_lt (lt_of_not_ge h), h2⟩ y) (le_max_left _ _)
        · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
          exact le_trans (hM₁ S hSmem y) (le_max_left _ _)
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      have heq : (fun y : Work.LWP.R3 => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t)
          = fun y => dtExt ω S y t := by
        funext y; exact timeDeriv_windowExt hS hdiff y t
      rw [heq]
      by_cases h : t ≤ 0
      · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
            = fun y => FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact dtExt_of_nonpos h
        rw [heq2]
        exact hdtmeas 0 h0mem
      · by_cases h2 : t ≤ S
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y t := by
            funext y; exact dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq2]
          exact hdtmeas t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq2]
          exact hdtmeas S hSmem
  · intro t₀ _
    refine ⟨1, one_pos, fun t _ y => ?_⟩
    have heq : (fun s : ℝ => FiniteTimeSingularity.timeDeriv (windowExt ω S) y s)
        = fun s => dtExt ω S y s := by
      funext s; exact timeDeriv_windowExt hS hdiff y s
    rw [heq]
    exact continuousAt_dtExt hα hS hN₁ y t

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.gsBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-- Row `N₁^{gs} = 2ℛ(Φ̃_g)·F_*`: the `L₁₂`-density estimate with the explicit `r`-dependent
majorant `M r = √(CA/(γ-1)·Ψ r)` of the `HQo`-coefficient `ℛ(Φ̃_g)`.  The pointwise input is
`|K θ·F_*| ≤ 60α·r/(1+r)²` (`Work.FTS.NonlinRows.Rl1.K_Fstar_pt`), and the profile
`c r = 120α·r/(1+r)` closes the `r`-step through `Fa_le_of_profile`. -/
theorem row1gs {CA α Ce : ℝ} {g Φg : Fn} (hCA : 0 < CA)
    (hang : ∀ (A : Fn), Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Fa (Work.FTS.Nonlin.N1gs α g Φg)
      ≤ ENNReal.ofReal (2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Xn α g) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := div_nonneg hCA.le hγ.le
  -- the coefficient `A = ℛ(Φ̃_g)` and its energy `Ψ`
  set A : Fn := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) with hA
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := by rw [hA]; exact hell.R.1.1
  have hAmem : Work.Spaces.HkMem α 4 A := by rw [hA]; exact hell.R.1.2
  have hAxn : Xn α A ≤ Ce * Xn α g := by rw [hA]; exact hell.R.2
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ
    with hΨ
  set M : ℝ → ℝ := fun r => Real.sqrt (CA / (Work.Spaces.gam α - 1) * Ψ r) with hM
  set cc : ℝ → ℝ := fun r => 120 * α * r / (1 + r) with hcc
  have hccnn : ∀ r, 0 < r → 0 ≤ cc r := by
    intro r hr
    rw [hcc]
    positivity
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hΨnn : ∀ r, 0 ≤ Ψ r := by
    intro r
    exact MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ)
  have hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ CA / (Work.Spaces.gam α - 1) * Ψ r := by
    intro r _
    exact (Real.sq_sqrt (mul_nonneg hC (hΨnn r))).le
  obtain ⟨hΨmeas, hΨint, hΨle⟩ := HkSlot_data hAmem
  -- `r⁻¹ · cc r = 120α/(1+r)` on `r > 0`
  have hccinv : ∀ r, 0 < r → r⁻¹ * cc r = 120 * α / (1 + r) := by
    intro r hr
    rw [hcc]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hccmeas : AEMeasurable (fun r => r⁻¹ * cc r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => 120 * α * (1 + r)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).inv)).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hccinv r hr).symm
  have hccint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * cc r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hbase : MeasureTheory.IntegrableOn (fun r => (120 * α / (1 + r)) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      have h2 : MeasureTheory.IntegrableOn (fun r => (120 * α) ^ 2 * (1 / (1 + r)) ^ 2)
          (Set.Ioi (0 : ℝ)) := (integrableOn_inv_one_add_sq'.1).const_mul _
      refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ioi
      intro r hr
      field_simp
    refine MeasureTheory.IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro r hr
    exact congrArg (fun x => x ^ 2) (hccinv r hr).symm
  -- the θ-step
  have hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg r θ| ≤ cc r * M r := by
    intro r hr θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hR : |A r θ| ≤ M r := by
      have h2 := hang A hAsm hAmem r θ hr hθ0 hθ1
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at h3
    have hF := K_Fstar_pt hα hα1 hr hθI
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg r θ|
        = 2 * |A r θ| * |Work.Spaces.K θ * Work.Construction.Fstar α r θ| := by
      simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg, hA, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [habs]
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hle : (1 : ℝ) + r ≤ (1 + r) ^ 2 := by nlinarith [sq_nonneg r]
    have hdiv : r / (1 + r) ^ 2 ≤ r / (1 + r) := by
      rw [div_le_div_iff₀ (by positivity) h1r]
      nlinarith [mul_le_mul_of_nonneg_left hle hr.le]
    have hstep : 2 * |A r θ| * |Work.Spaces.K θ * Work.Construction.Fstar α r θ|
        ≤ 2 * M r * (60 * α * r / (1 + r) ^ 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hF (abs_nonneg _) ?_
      positivity
    refine hstep.trans ?_
    rw [hcc]
    have h1 : 2 * M r * (60 * α * r / (1 + r) ^ 2)
        = 120 * α * (r / (1 + r) ^ 2) * M r := by ring
    rw [h1]
    have h2 : 120 * α * (r / (1 + r) ^ 2) * M r ≤ 120 * α * (r / (1 + r)) * M r := by
      refine mul_le_mul_of_nonneg_right ?_ (hMnn r)
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    have h3 : 120 * α * (r / (1 + r)) * M r = 120 * α * r / (1 + r) * M r := by ring
    linarith [h2, h3.le, h3.ge]
  -- the Cauchy–Schwarz step
  have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N1gs α g Φg) (c := cc) (M := M)
    (Ψ := Ψ) (C := CA / (Work.Spaces.gam α - 1)) hC hccnn hMnn hΨnn hΨmeas hΨint
    hccmeas hccint hMle hpt
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hsq : Work.Spaces.HkSq α 4 A = (Xn α A) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)).symm
  have hΨbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ max Ce 0 * Xn α g := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ (Xn α A) ^ 2 :=
      hΨle.trans (le_of_eq hsq)
    have h2 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Xn α A := by
      calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Real.sqrt ((Xn α A) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = |Xn α A| := Real.sqrt_sq_eq_abs _
        _ = Xn α A := abs_of_nonneg (Work.Spaces.HkNorm_nonneg α 4 A)
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Xn α A := h2
      _ ≤ Ce * Xn α g := hAxn
      _ ≤ max Ce 0 * Xn α g := mul_le_mul_of_nonneg_right (le_max_left Ce 0) hX0
  have hcinteg : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      = (120 * α) ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 := by
    have hcong : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (120 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      change (r⁻¹ * cc r) ^ 2 = (120 * α) ^ 2 * (1 / (1 + r)) ^ 2
      rw [hccinv r hr]
      field_simp
    rw [hcong, MeasureTheory.integral_const_mul]
  have hcbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      ≤ 120 * α * Real.sqrt 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2) ≤ (120 * α) ^ 2 * 2 := by
      rw [hcinteg]
      exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt ((120 * α) ^ 2 * 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt ((120 * α) ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
      _ = 120 * α * Real.sqrt 2 := by rw [Real.sqrt_sq (by positivity)]
  have hkey : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
      ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by
    have h1 : Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Xn α g)
            * (120 * α * Real.sqrt 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hΨbd (Real.sqrt_nonneg _)) hcbd
        (Real.sqrt_nonneg _) ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCa0 hX0)
    have h2 : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * (max Ce 0 * Xn α g) * (120 * α * Real.sqrt 2))
        = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α)
            * max Ce 0 * Xn α g := by ring
    have h3 : Real.pi / 2 * Real.sqrt 2 * 120
        * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * max Ce 0 * Xn α g
        ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by
      rw [sqrt_coef_mul_alpha hCA.le hα]
      have h4 : Real.pi / 2 * Real.sqrt 2 * 120 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ))
          * max Ce 0 * Xn α g
          = (Real.pi / 2 * Real.sqrt 2 * 120) * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)
              * max Ce 0 * Xn α g) := by ring
      rw [h4]
      calc (Real.pi / 2 * Real.sqrt 2 * 120) * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)
            * max Ce 0 * Xn α g)
          ≤ 2000 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0 * Xn α g) :=
            mul_le_mul_of_nonneg_right pi_div_two_mul_sqrt_two_mul
              (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
                (Real.rpow_nonneg hα.le _)) hCa0) hX0)
        _ = 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by ring
    calc Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
        ≤ Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Xn α g)
            * (120 * α * Real.sqrt 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * max Ce 0 * Xn α g := h2
      _ ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := h3
  exact hmain.trans (ENNReal.ofReal_le_ofReal hkey)

/-
The three `gs`-rows (coefficient a `HQo`-coefficient of `EllPkgGo`, slot an explicit profile
`F_*`, `∂_θF_*`, `D_zF_*`).  Route (unprimed sibling: `rl1Pieces.Pgs` in
`Pieces/rl1Pieces/Pgs.lean`, constant bounds via `gPt`; here the coefficient majorant is
`z`-dependent):
* for `N1gs = 2ℛ(Φ̃_g)·F_*` use the pointwise `|K θ·F_*| ≤ 60 α z/(1+z)²`
  (`Work.FTS.NonlinRows.Rl1.K_Fstar_pt`), so
  `∫⁻_θ |K·N1gs| ≤ ofReal(M r)·ofReal(60 α r/(1+r)²)` with `M r` the coefficient majorant
  (`angSup_le`), and then `outer_gen` with `θw r := 60α/(1+r)` (valid since
  `r/(1+r)² ≤ 1/(1+r)`), `Ψ` the coefficient energy (`HkSlot_data`), `C = C_A/(γ-1)·4`
  (the factor `2` of the piece), `∫θw² ≤ 3600α²·2`.  Rate: `C·α^{1/2}·Ce·X ≤ Ce·Env`.
* `N2gs = -2𝒰(Φ̃_g)·∂_θF_*`: write `𝒰 = sin2θ·(𝒰/sin2θ)` (valid on `Ioo 0 (π/2)`; at the
  endpoints `K = 0`), use `K_sin_pth_Fstar_pt`-style pointwise bound
  `|K θ·∂_θF_*| ≤ 80α² z/(1+z)²` (`Work.FTS.NonlinRows.Rl1.K_pthFstar_pt`), same `outer_gen`.
* `N3gs = -2α𝒱(Φ̃_g)·D_zF_*`: `|K θ·D_zF_*| ≤ 60α z/(1+z)²` (`K_DzFstar_pt`), `outer_gen`.
All three rates fit `K·Env α g` since `√α·X` and `α^{3/2}·X` are dominated by `Env`.
-/
theorem gsBounds {Ce : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φg : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CA, hCApos, hCA⟩ := angSup_le
  set K : ℝ := 1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA)) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hA : 0 ≤ max Ce 0 * Real.sqrt (10 * CA) :=
      mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φg hα hα1 hgal hell
  have hEnv : 0 ≤ Env α g := Env_nonneg g hα.le
  have hK : 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      ≤ K * Env α g := by
    rw [hKdef]
    exact const_mul_le_K hCApos.le hα hEnv
  have hang : ∀ (A : Fn), Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ' :=
    fun A => hCA α A hα hα1
  refine ⟨?_, ?_, ?_⟩
  · exact (row1gs (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)
  · exact (gsRow2 (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)
  · exact (gsRow3 (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.AngU.Linv_iter_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Linv_iter_uniform` — uniform control of the `Lop`-iterates of `Linv h`

`Linv h` is the `σ`-normalised zero-moment Dirichlet inverse of `L₀` (node P-G of the
`Φ_*` construction).  It solves the *first-order* linear equation

`Lop (Linv h) = -(h + L₂ · Linv h)`,   `L₂ θ = 5 cos 2θ - 1 = 10 cos²θ - 6`,

equivalently `Lop (Linv h) = (6 - 10 cos²θ)·Linv h - h`, where `Lop u = sin 2θ · u'`.

This file produces a **single** nonnegative sequence `C` — independent of the source `h`
and of the bound `K` — with

`|Lop^[i] (Linv h) θ| ≤ C i · K`,   `i ≤ 5`,   `θ ∈ (0, π/2)`,

from only: `|Linv h θ| ≤ K`, `|Lop^[a] h θ| ≤ K` for `a ≤ 4`, `h ∈ C⁹` on `(0, π/2)` and
`h · sinCos2 ∈ L¹(Iθ)`.  (The zero-moment hypothesis is part of the interface the consumer
uses but is not needed here: the ODE `LI_lop_Linv_eq` is valid without it.)

## Route

The prototype is `LinvFlat.LinvLopIter`, which proves the same statement with the stronger
hypothesis `|Lop^[a] h θ| ≤ K` for `a ≤ 8`.  Here only four source iterates are assumed, so
the induction stops at order `5`: at each step the recursion

`Lop^[n+1] (Linv h) = -(Lop^[n] h) - ∑_{a ≤ n} C(n,a) (Lop^[a] L₂)(Lop^[n-a] (Linv h))`

is obtained from the Leibniz rule for iterates of a product (`LI_lop_iter_Xfun_eqOn`), and
the explicit majorant `C i = 4·(10⁶(M₀+1))^i` closes the induction, where `M₀` is the
uniform bound for the iterates of `L₂` up to order `7` (`LI_L2fun_lop_bound`).  Since `M₀`
does not depend on `h` or `K`, the resulting sequence is uniform.
-/

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.AngU

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem Linv_iter_uniform : ∃ C : ℕ → ℝ, (∀ i : ℕ, 0 ≤ C i) ∧
    ∀ (h : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ a : ℕ, a ≤ 4 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[a]) h θ| ≤ K) →
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.Linv h θ| ≤ K) →
      ContDiffOn ℝ 9 h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0 →
      ∀ i : ℕ, i ≤ 5 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv h) θ| ≤ C i * K := by
  -- a uniform bound `M₀` for the iterates of the coefficient `L₂` (order `≤ 7`)
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.PhiStar.LinvFlat.LI_L2fun_lop_bound
  refine ⟨fun i => Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 i,
    fun i => Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn i, ?_⟩
  intro h K hK hiter hlinv hcd hint hmom i hi θ hθ
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  -- `Linv h` is `C^9` on the open interval
  have hg9 : ContDiffOn ℝ 9 (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.PhiStar.LinvFlat.Linv_contDiffOn_hasDerivAt (h := h) (n := 9) (by norm_num)
      hcd hint).1
  -- the first-order equation, in the form used by the iterate expansion
  have hode : Set.EqOn (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
      (fun θ : ℝ => -(h θ + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ
        * Work.FTS.PhiStar.Linv h θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.PhiStar.LinvFlat.LI_lop_Linv_eq hcd hint
  -- the Leibniz recursion for the iterates of `Linv h`
  have hrec : ∀ n : ℕ, n ≤ 4 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h) θ
        = -(Work.Spaces.Lop^[n] h θ)
          - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ) := by
    intro n hn4 θ hθ'
    have h1 : Set.EqOn (Work.Spaces.Lop^[n + 1] (Work.FTS.PhiStar.Linv h))
        (Work.Spaces.Lop^[n]
          (fun θ : ℝ => -(h θ + Work.FTS.PhiStar.LinvFlat.LI_L2fun θ
            * Work.FTS.PhiStar.Linv h θ)))
        (Set.Ioo 0 (Real.pi / 2)) := by
      rw [show (Work.Spaces.Lop^[n + 1]) (Work.FTS.PhiStar.Linv h)
          = (Work.Spaces.Lop^[n]) (Work.Spaces.Lop (Work.FTS.PhiStar.Linv h))
          from Function.iterate_succ_apply (f := Work.Spaces.Lop) n
            (Work.FTS.PhiStar.Linv h)]
      exact Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_congr_eqOn hU n hode
    have h2 := Work.FTS.PhiStar.LinvFlat.LI_lop_iter_Xfun_eqOn hcd hg9 (k := n) (by omega)
    exact h1.trans h2 hθ'
  -- the induction producing the uniform constant
  have key : ∀ n : ℕ, n ≤ 5 → ∀ b : ℕ, b ≤ n → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[b]) (Work.FTS.PhiStar.Linv h) θ|
        ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 b * K := by
    intro n
    induction n with
    | zero =>
        intro _ b hb θ hθ'
        obtain rfl : b = 0 := Nat.le_zero.mp hb
        have hL : (Work.Spaces.Lop^[0]) (Work.FTS.PhiStar.Linv h) θ
            = Work.FTS.PhiStar.Linv h θ := rfl
        have hC0 : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 0 = 4 := by
          show 4 * (1000000 * (M0 + 1)) ^ 0 = 4
          rw [pow_zero]; ring
        rw [hL, hC0]
        calc |Work.FTS.PhiStar.Linv h θ| ≤ K := hlinv θ hθ'
          _ ≤ 4 * K := by linarith [hK]
    | succ n ih =>
        intro hn b hb θ hθ'
        by_cases hbn : b ≤ n
        · exact ih (by omega) b hbn θ hθ'
        · have hbeq : b = n + 1 := by omega
          subst hbeq
          have hn4 : n ≤ 4 := by omega
          rw [hrec n hn4 θ hθ']
          have hX : |(Work.Spaces.Lop^[n]) h θ| ≤ K := hiter n hn4 θ hθ'
          have hterm : ∀ a ∈ Finset.range (n + 1),
              |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a])
                Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ 256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            intro a ha
            have haj : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            have hc0 : (0 : ℝ) ≤ (n.choose a : ℝ) := by positivity
            have hcB : (n.choose a : ℝ) ≤ 256 := by
              have h1 : n.choose a ≤ 2 ^ n := Nat.choose_le_two_pow n a
              have h2 : 2 ^ n ≤ 2 ^ 8 :=
                pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega)
              have h3 : 2 ^ 8 = (256 : ℕ) := by norm_num
              exact_mod_cast (le_trans h1 (le_trans h2 (le_of_eq h3)))
            rw [abs_mul, abs_of_nonneg hc0, abs_mul]
            have hL2 : |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| ≤ M0 :=
              hM0 a (by omega) θ
            have hgv : |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a) * K :=
              ih (by omega) (n - a) (by omega) θ hθ'
            have hCf : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n - a)
                ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_mono hM0nn (Nat.sub_le n a)
            have hBnd : |(Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ| *
                |(Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ|
                ≤ M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              refine mul_le_mul hL2 ?_ (abs_nonneg _) hM0nn
              exact le_trans hgv (mul_le_mul_of_nonneg_right hCf hK)
            exact mul_le_mul hcB hBnd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (by norm_num)
          have hSabs : |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            have h2 : ∑ a ∈ Finset.range (n + 1),
                |(n.choose a : ℝ) * ((Work.Spaces.Lop^[a])
                  Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ (Finset.range (n + 1)).card •
                  (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))) :=
              Finset.sum_le_card_nsmul _ _ _ (fun a ha => hterm a ha)
            refine le_trans h2 ?_
            rw [Finset.card_range, nsmul_eq_mul]
            have hn8 : (((n + 1 : ℕ)) : ℝ) ≤ 8 := by
              exact_mod_cast (by omega : n + 1 ≤ 8)
            have hY0 : (0 : ℝ)
                ≤ 256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
              have hcf : (0 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
                Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn n
              exact mul_nonneg (by norm_num) (mul_nonneg hM0nn (mul_nonneg hcf hK))
            calc (((n + 1 : ℕ)) : ℝ) *
                  (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)))
                ≤ 8 * (256 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))) :=
                  mul_le_mul_of_nonneg_right hn8 hY0
              _ = 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by ring
          have hgoal : K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))
              ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n + 1) * K := by
            have hCn1 : (1 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_one_le hM0nn n
            have hCn0 : (0 : ℝ) ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n :=
              Work.FTS.PhiStar.LinvFlat.LI_Cfun_nonneg hM0nn n
            have hkey2 : 2048 * M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)
                ≤ ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              have h1 : 2048 * M0 ≤ (1000000 * (M0 + 1)) - 1 := by nlinarith [hM0nn]
              exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hCn0 hK)
            have hAK : K ≤ Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K := by
              have := mul_le_mul_of_nonneg_right hCn1 hK
              simpa using this
            have hstepA : K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K))
                ≤ K + ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K) := by
              linarith [hkey2]
            have hstepB : K + ((1000000 * (M0 + 1)) - 1) *
                  (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)
                ≤ (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * (1000000 * (M0 + 1))) * K := by
              linarith [hAK]
            have hCsucc : Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 (n + 1)
                = Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * (1000000 * (M0 + 1)) := by
              show 4 * (1000000 * (M0 + 1)) ^ (n + 1)
                = 4 * (1000000 * (M0 + 1)) ^ n * (1000000 * (M0 + 1))
              rw [pow_succ]; ring
            rw [hCsucc]
            linarith [hstepA, hstepB]
          have htri : |-(Work.Spaces.Lop^[n] h θ)
              - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                  (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
              ≤ K + 2048 * (M0 * (Work.FTS.PhiStar.LinvFlat.LI_Cfun M0 n * K)) := by
            have h1 : |-(Work.Spaces.Lop^[n] h θ)
                - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                  ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                    (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                ≤ |(Work.Spaces.Lop^[n]) h θ|
                  + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                    ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                      (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
              calc |-(Work.Spaces.Lop^[n] h θ)
                    - ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                      ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                        (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)|
                  = |(-(Work.Spaces.Lop^[n] h θ))
                      + (-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)))| := by
                    simp only [sub_eq_add_neg]
                _ ≤ |-(Work.Spaces.Lop^[n] h θ)|
                      + |-(∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ))| :=
                    abs_add_le _ _
                _ = |(Work.Spaces.Lop^[n]) h θ|
                      + |∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
                        ((Work.Spaces.Lop^[a]) Work.FTS.PhiStar.LinvFlat.LI_L2fun θ *
                          (Work.Spaces.Lop^[n - a]) (Work.FTS.PhiStar.Linv h) θ)| := by
                    rw [abs_neg, abs_neg]
            linarith [h1, hX, hSabs]
          linarith [htri, hgoal]
  exact key 5 le_rfl i hi θ hθ

end Work.FTS.PhiStar.AngU
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.RadGreenDivFlatU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.FlatWAux.RadGreenDivFlatU`

The flat (`(z+1)^k∂_z^k`) estimate for the *divided* radial Green function
`(z+1)/z · radGreen α m c`, uniform in `α ≤ 1/5` and in the mode `m ≥ 1`.

Route (see `NOTES_radialWAux.md` / `_DevDivFlat.lean`): with the rescaled pieces
`Φ z = ∫₀¹ c(zu)u^{q-1}du`, `Ψ z = ∫_{u>1} c(zu)u^{-p-1}du` (`q = (2m+5)/α`, `p = 2m/α`,
`K = 1/(α(4m+5))`), the rescaled identity `radGreen = K(Φ+Ψ)` and the substitution `t = zu`
give, for `h = c/t`,

  `(z+1)/z · radGreen α m c z = K·(z+1)·(PhiQ (q+1) h z + PsiP (p-1) h z)`.

Every `z`-derivative is then a differentiation under the integral sign over a fixed domain
(`phiKernel_hasDerivAt`, `psiKernel_hasDerivAt`), and the weighted bounds
`phiKernelWeightedLe` / `psiKernelWeightedLe` give
`(z+1)^{j+1}|(Φ̃+Ψ̃)^{(j)}(z)| ≤ 2^{j+1}A(1/(j+q+1) + 1/(q-1) + 1/(p-1-j) + 1/(p+1))`,
which after multiplication by `K` is `≤ 10A/λ_m` by the four arithmetic lemmas below
(the `α`-smallness of `1/(j+q+1)` and `1/(q-1)` is exactly what makes the estimate uniform).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

open Work.FTS.PhiStar.RadialWAux

/-! ## The `j`-th `z`-derivative kernel of `PhiQ Q h + PsiP P h` -/

/-- The `j`-th `z`-derivative kernel of `PhiQ Q h + PsiP P h`, i.e. the parametric integral
`z ↦ ∫₀¹ h^{(j)}(zu)u^{j+Q-1}du + ∫_{u>1} h^{(j)}(zu)u^{j-P-1}du`. -/
def Wker (Q P : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => (∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + Q - 1))
    + (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))

/-! ## The uniform arithmetic

The four bounds `K/(j+q+1) ≤ 1/λ_m`, `K/(q-1) ≤ 1/λ_m`, `K/(p-1-j) ≤ 4/λ_m`,
`K/(p+1) ≤ 4/λ_m` (`K = radK`, `q = radQ`, `p = radP`, `λ_m = 2m(2m+5)`), all uniform in
`α ≤ 1/5`, `m ≥ 1`, `j ≤ 7`. -/

private lemma radK_inv_jQ_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {j : ℕ} :
    radK α m * (1 / ((j : ℝ) + (radQ α m + 1))) ≤ 1 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [radK, radQ, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((j : ℝ) + ((2 * (m : ℝ) + 5) / α + 1)))
      = 1 / ((4 * (m : ℝ) + 5) * (α * ((j : ℝ) + 1) + 2 * (m : ℝ) + 5)) := by
    field_simp
    ring
  rw [hkey]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [hj0, hm0, hα, mul_nonneg (le_of_lt hα) (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1)]

private lemma radK_inv_Q2_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    radK α m * (1 / ((radQ α m + 1) - 2)) ≤ 1 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [radK, radQ, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (((2 * (m : ℝ) + 5) / α + 1) - 2))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α)) := by
    field_simp
    ring
  rw [hkey]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg (2 * (m : ℝ) + 5), hα5, hα, hm1,
      mul_le_mul_of_nonneg_left hα5 (by linarith : (0 : ℝ) ≤ 4 * (m : ℝ) + 5)]

private lemma radK_inv_Pj_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m)
    {j : ℕ} (hj : j ≤ 7) :
    radK α m * (1 / ((radP α m - 1) - (j : ℝ))) ≤ 4 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [radK, radP, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((2 * (m : ℝ) / α - 1) - (j : ℝ)))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) - α * ((j : ℝ) + 1))) := by
    field_simp
    ring
  rw [hkey, show (4 : ℝ) / (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
      = 1 / (2 * (m : ℝ) * (2 * (m : ℝ) + 5) / 4) by field_simp]
  apply one_div_le_one_div_of_le
  · positivity
  · have hj8 : (j : ℝ) + 1 ≤ 8 := by
      have h : (j : ℝ) ≤ 7 := by exact_mod_cast hj
      linarith
    have h1 : α * ((j : ℝ) + 1) ≤ (1 / 5) * 8 :=
      mul_le_mul hα5 hj8 (by positivity) (by norm_num)
    nlinarith [h1, hm1, hα]

private lemma radK_inv_P2_le {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    radK α m * (1 / ((radP α m - 1) + 2)) ≤ 4 / Gegenbauer.lam m := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [radK, radP, Gegenbauer.lam]
  have hkey : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / ((2 * (m : ℝ) / α - 1) + 2))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α)) := by
    have h1 : (2 * (m : ℝ) / α - 1) + 2 = (2 * (m : ℝ) + α) / α := by field_simp; ring
    rw [h1, one_div_div]
    field_simp
  rw [hkey, show (4 : ℝ) / (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
      = 1 / (2 * (m : ℝ) * (2 * (m : ℝ) + 5) / 4) by field_simp]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [hm1, hα, mul_nonneg (le_of_lt hα) (by linarith : (0 : ℝ) ≤ 2 * (m : ℝ) + 5)]

/-! ## The main theorem -/

theorem RadGreenDivFlatU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m → ∀ (c : ℝ → ℝ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 14 c (Set.Ioi 0) →
      (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) →
      (∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (fun t => c t / t) t| ≤ A / (1 + t ^ (k + 2))) →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
        |(z + 1) ^ k * iteratedDeriv k
            (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m c z') z|
          ≤ C * A / Work.FTS.PhiStar.Gegenbauer.lam m := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α hα hα5 m hm c A hA hc hb hbt k hk z hz
  have hlam : 0 < Gegenbauer.lam m := by
    simp only [Gegenbauer.lam]; positivity
  have hKpos : 0 < radK α m := radK_pos hα m
  have hPge : (10 : ℝ) ≤ radP α m := ten_le_radP hα hα5 hm
  have hQge : (35 : ℝ) ≤ radQ α m := thirtyfive_le_radQ hα hα5 hm
  let h : ℝ → ℝ := fun t => c t / t
  have hh : ContDiffOn ℝ 14 h (Set.Ioi 0) := by
    show ContDiffOn ℝ 14 (fun t : ℝ => c t / t) (Set.Ioi 0)
    exact hc.div contDiffOn_id (fun t ht => ne_of_gt ht)
  have hsharp : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv j h t| ≤ A / (1 + t ^ (j + 2)) :=
    fun j hj t ht => hbt j (by omega) t ht
  have hbdd : BddDeriv 14 h A := by
    intro j hj t ht
    refine le_trans (hbt j hj t ht) ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ (j + 2))]
    nlinarith [hA, pow_nonneg (le_of_lt ht) (j + 2)]
  -- the divided identity `(z+1)/z·radGreen = K·(z+1)·Wker_0`
  have hY : ∀ z : ℝ, 0 < z →
      (z + 1) / z * Radial.radGreen α m c z
        = radK α m * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h 0 z) := by
    intro z hz
    have hgr := radGreen_eq_rescaled hα m c z hz
    have hPhi : radPhi α m c z = z * PhiQ (radQ α m + 1) h z := by
      show (∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1))
          = z * ∫ u in (0 : ℝ)..1, h (z * u) * u ^ ((radQ α m + 1) - 1)
      rw [show ((radQ α m + 1) - 1) = radQ α m from by ring]
      rw [show (∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1))
          = ∫ u in (0 : ℝ)..1, z * (h (z * u) * u ^ (radQ α m)) from by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with u hu
            change c (z * u) * u ^ (radQ α m - 1) = z * (h (z * u) * u ^ (radQ α m))
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
            have hu0 : 0 < u := hu.1
            have hc1 : c (z * u) = (z * u) * h (z * u) := by
              simp only [h]
              field_simp
            have hpw : u * u ^ (radQ α m - 1) = u ^ (radQ α m) := by
              have h2 : u ^ (radQ α m) = u ^ (1 : ℝ) * u ^ (radQ α m - 1) := by
                rw [← Real.rpow_add hu0 (1 : ℝ) (radQ α m - 1)]
                congr 1
                ring
              rw [h2, Real.rpow_one]
            rw [hc1, ← hpw]
            ring,
          intervalIntegral.integral_const_mul]
    have hPsi : radPsi α m c z = z * PsiP (radP α m - 1) h z := by
      show (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1))
          = z * ∫ u in Set.Ioi (1 : ℝ), h (z * u) * u ^ (-(radP α m - 1) - 1)
      rw [show (-(radP α m - 1) - 1) = -(radP α m) from by ring]
      rw [show (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1))
          = ∫ u in Set.Ioi (1 : ℝ), z * (h (z * u) * u ^ (-(radP α m))) from by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            change c (z * u) * u ^ (-(radP α m) - 1) = z * (h (z * u) * u ^ (-(radP α m)))
            have hu0 : 0 < u := lt_trans zero_lt_one hu
            have hc1 : c (z * u) = (z * u) * h (z * u) := by
              simp only [h]
              field_simp
            have hpw : u * u ^ (-(radP α m) - 1) = u ^ (-(radP α m)) := by
              have h2 : u ^ (-(radP α m)) = u ^ (1 : ℝ) * u ^ (-(radP α m) - 1) := by
                rw [← Real.rpow_add hu0 (1 : ℝ) (-(radP α m) - 1)]
                congr 1
                ring
              rw [h2, Real.rpow_one]
            rw [hc1, ← hpw]
            ring,
          MeasureTheory.integral_const_mul]
    have hWker0 : Wker (radQ α m + 1) (radP α m - 1) h 0 z
        = PhiQ (radQ α m + 1) h z + PsiP (radP α m - 1) h z := by
      simp only [Wker, PhiQ, PsiP, iteratedDeriv_zero, Nat.cast_zero, zero_add, zero_sub]
    rw [hgr, hPhi, hPsi, hWker0]
    field_simp
  -- differentiating the kernel
  have hWkderiv : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      HasDerivAt (Wker (radQ α m + 1) (radP α m - 1) h j)
        (Wker (radQ α m + 1) (radP α m - 1) h (j + 1) z) z := by
    intro j hj z hz
    have hjP : (j : ℝ) + 1 < radP α m - 1 := by
      have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast hj
      linarith
    have h1 := phiKernel_hasDerivAt (Q := radQ α m + 1) (B := A) (by linarith) hA hh hbdd
      (j := j) (by omega) hz
    have h2 := psiKernel_hasDerivAt (P := radP α m - 1) (B := A) hA hh hbdd
      (j := j) (by omega) hjP hz
    have hfun : Wker (radQ α m + 1) (radP α m - 1) h j
        = ((fun x : ℝ => ∫ u in (0 : ℝ)..1,
              iteratedDeriv j h (x * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
          + fun x : ℝ => ∫ u in Set.Ioi (1 : ℝ),
              iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - (radP α m - 1) - 1)) := rfl
    rw [hfun]
    simpa only [Wker, Pi.add_apply] using h1.add h2
  -- the iterated derivative formula
  have key : ∀ k : ℕ, k ≤ 7 → ∀ x : ℝ, 0 < x →
      iteratedDeriv k (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') x
        = radK α m * ((x + 1) * Wker (radQ α m + 1) (radP α m - 1) h k x
            + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) x) := by
    intro k
    induction k with
    | zero =>
      intro _ x hx
      simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero] using hY x hx
    | succ k ih =>
      intro hk x hx
      have hk6 : k ≤ 6 := by omega
      have hfun : iteratedDeriv k (fun z' => (z' + 1) / z' * Radial.radGreen α m c z')
          =ᶠ[𝓝 x] (fun y => radK α m * ((y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y
              + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih (by omega) y hy
      rw [iteratedDeriv_succ, hfun.deriv_eq]
      have hdWk : HasDerivAt (Wker (radQ α m + 1) (radP α m - 1) h k)
          (Wker (radQ α m + 1) (radP α m - 1) h (k + 1) x) x := hWkderiv k hk6 x hx
      have hlin : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const (1 : ℝ)
      have hderA := hlin.mul hdWk
      have hfunA : ((fun y : ℝ => y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k)
          = fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y := rfl
      rw [hfunA] at hderA
      have hderB : HasDerivAt
          (fun y : ℝ => (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)
          ((k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h k x) x := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          have h0 : (fun y : ℝ => ((0 : ℕ) : ℝ)
                * Wker (radQ α m + 1) (radP α m - 1) h (0 - 1) y) = fun _ => 0 := by
            funext y
            simp
          rw [h0]
          simpa using hasDerivAt_const x (0 : ℝ)
        · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
          have hh' := (hWkderiv (k - 1) (by omega) x hx).const_mul (k : ℝ)
          rwa [hk1] at hh'
      have hsum := hderA.add hderB
      have hfunF : ((fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y)
            + fun y : ℝ => (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y)
          = fun y : ℝ => (y + 1) * Wker (radQ α m + 1) (radP α m - 1) h k y
              + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) y := rfl
      rw [hfunF] at hsum
      have hderF := hsum.const_mul (radK α m)
      rw [hderF.deriv, show (k + 1) - 1 = k from by omega]
      push_cast
      ring
  -- the arithmetic package
  have hSle : ∀ j : ℕ, j ≤ 7 → radK α m *
      (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
        + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
      ≤ 10 / Gegenbauer.lam m := by
    intro j hj
    have h1 := radK_inv_jQ_le hα hm (j := j)
    have h2 := radK_inv_Q2_le hα hα5 hm
    have h3 := radK_inv_Pj_le hα hα5 hm (j := j) hj
    have h4 := radK_inv_P2_le hα hα5 hm
    have hexp : radK α m *
        (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
        = radK α m * (1 / ((j : ℝ) + (radQ α m + 1)))
          + radK α m * (1 / ((radQ α m + 1) - 2))
          + radK α m * (1 / ((radP α m - 1) - (j : ℝ)))
          + radK α m * (1 / ((radP α m - 1) + 2)) := by ring
    rw [hexp]
    have hcomb : 1 / Gegenbauer.lam m + 1 / Gegenbauer.lam m + 4 / Gegenbauer.lam m
          + 4 / Gegenbauer.lam m = 10 / Gegenbauer.lam m := by ring
    calc radK α m * (1 / ((j : ℝ) + (radQ α m + 1))) + radK α m * (1 / ((radQ α m + 1) - 2))
          + radK α m * (1 / ((radP α m - 1) - (j : ℝ))) + radK α m * (1 / ((radP α m - 1) + 2))
        ≤ 1 / Gegenbauer.lam m + 1 / Gegenbauer.lam m + 4 / Gegenbauer.lam m
          + 4 / Gegenbauer.lam m :=
          add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = 10 / Gegenbauer.lam m := hcomb
  -- the weighted kernel bound
  have hker : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) * |Wker (radQ α m + 1) (radP α m - 1) h j z| ≤
        (2 : ℝ) ^ (j + 1) * A *
          (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2)) := by
    intro j hj z hz
    have hQ2 : (2 : ℝ) < radQ α m + 1 := by linarith
    have hP9 : (9 : ℝ) ≤ radP α m - 1 := by linarith
    have hjP : (j : ℝ) < radP α m - 1 := by
      have hj7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj
      linarith
    have hp := Kernels.phiKernelWeightedLe (Q := radQ α m + 1) (B := A) hQ2 hA hh hsharp j (by omega) z hz
    have hq := Kernels.psiKernelWeightedLe (P := radP α m - 1) (B := A) hP9 hA hh hsharp j (by omega) hjP z hz
    have htri : (z + 1) ^ (j + 1) * |Wker (radQ α m + 1) (radP α m - 1) h j z|
        ≤ (z + 1) ^ (j + 1) * |(∫ u in (0 : ℝ)..1,
              iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))|
          + (z + 1) ^ (j + 1) * |(∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u)
              * u ^ ((j : ℝ) - (radP α m - 1) - 1))| := by
      rw [show Wker (radQ α m + 1) (radP α m - 1) h j z
          = (∫ u in (0 : ℝ)..1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
            + (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv j h (z * u)
                * u ^ ((j : ℝ) - (radP α m - 1) - 1)) from rfl]
      have h := mul_le_mul_of_nonneg_left
        (abs_add_le (∫ u in (0 : ℝ)..1,
            iteratedDeriv j h (z * u) * u ^ ((j : ℝ) + (radQ α m + 1) - 1))
          (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - (radP α m - 1) - 1)))
        (by positivity : (0 : ℝ) ≤ (z + 1) ^ (j + 1))
      rwa [mul_add] at h
    refine le_trans htri ?_
    have hsplit : (2 : ℝ) ^ (j + 1) * A *
          (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2))
        = (2 : ℝ) ^ (j + 1) * A * (1 / ((j : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2))
          + (2 : ℝ) ^ (j + 1) * A
            * (1 / ((radP α m - 1) - (j : ℝ)) + 1 / ((radP α m - 1) + 2)) := by ring
    rw [hsplit]
    exact add_le_add hp hq
  -- numerical bounds on the powers of `2`
  have h2k : (2 : ℝ) ^ k ≤ 128 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hk
      _ = 128 := by norm_num
  have h2k1 : (2 : ℝ) ^ (k + 1) ≤ 256 := by
    calc (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      _ ≤ 2 * 128 := by linarith
      _ = 256 := by norm_num
  have hkR : (k : ℝ) ≤ 7 := by exact_mod_cast hk
  have hkmul : (k : ℝ) * (2 : ℝ) ^ k ≤ 7 * 128 :=
    mul_le_mul hkR h2k (by positivity) (by norm_num)
  have hkey := key k hk z hz
  have hkerk := hker k hk z hz
  have hSK := hSle k hk
  have hSK1 := hSle (k - 1) (by omega)
  -- the `k-1` term: `(k-1)+1 = k` needs `k ≥ 1`, and the case `k = 0` is trivial
  have hkerk1 : (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|)
      ≤ (k : ℝ) * ((2 : ℝ) ^ k * A *
          (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      have h := hker (k - 1) (by omega) z hz
      rw [hk1] at h
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)
  have hb1 : radK α m * ((2 : ℝ) ^ (k + 1) * A *
        (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2)))
      ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m) := by
    calc radK α m * ((2 : ℝ) ^ (k + 1) * A *
          (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2)))
        = (2 : ℝ) ^ (k + 1) * A * (radK α m *
            (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2))) := by ring
      _ ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m) :=
          mul_le_mul_of_nonneg_left hSK (by positivity)
  have hb2 : radK α m * ((k : ℝ) * ((2 : ℝ) ^ k * A *
        (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
          + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))))
      ≤ (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
    calc radK α m * ((k : ℝ) * ((2 : ℝ) ^ k * A *
          (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2))))
        = (k : ℝ) * ((2 : ℝ) ^ k * A * (radK α m *
            (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2)))) := by
          ring
      _ ≤ (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
          exact mul_le_mul_of_nonneg_left hSK1 (by positivity)
  have habs1 : |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') z|
      = radK α m * |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| := by
    rw [hkey]
    rw [show (z + 1) ^ k * (radK α m * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z))
        = radK α m * ((z + 1) ^ k * ((z + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)) from by ring]
    rw [abs_mul, abs_of_pos hKpos]
    congr 1
    rw [pow_succ]
    ring_nf
  have habs2 : |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
        + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)|
      ≤ (z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
        + (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|) := by
    calc |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)|
        ≤ |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z|
          + |(k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| :=
          abs_add_le _ _
      _ = (z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
          + (k : ℝ) * ((z + 1) ^ k * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|) := by
          simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ (k + 1) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ ((k : ℕ) : ℝ) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ k by positivity)]
  calc |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Radial.radGreen α m c z') z|
      = radK α m * |(z + 1) ^ (k + 1) * Wker (radQ α m + 1) (radP α m - 1) h k z
          + (k : ℝ) * ((z + 1) ^ k * Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z)| := habs1
    _ ≤ radK α m * ((z + 1) ^ (k + 1) * |Wker (radQ α m + 1) (radP α m - 1) h k z|
          + (k : ℝ) * ((z + 1) ^ k
            * |Wker (radQ α m + 1) (radP α m - 1) h (k - 1) z|)) :=
          mul_le_mul_of_nonneg_left habs2 (le_of_lt hKpos)
    _ ≤ radK α m * ((2 : ℝ) ^ (k + 1) * A *
          (1 / ((k : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
            + 1 / ((radP α m - 1) - (k : ℝ)) + 1 / ((radP α m - 1) + 2))
          + (k : ℝ) * ((2 : ℝ) ^ k * A *
            (1 / (((k - 1 : ℕ) : ℝ) + (radQ α m + 1)) + 1 / ((radQ α m + 1) - 2)
              + 1 / ((radP α m - 1) - ((k - 1 : ℕ) : ℝ)) + 1 / ((radP α m - 1) + 2)))) :=
          mul_le_mul_of_nonneg_left (add_le_add hkerk hkerk1) (le_of_lt hKpos)
    _ ≤ (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m)
          + (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m)) := by
          rw [mul_add]
          exact add_le_add hb1 hb2
    _ ≤ 10 ^ 6 * A / Gegenbauer.lam m := by
        rw [show (2 : ℝ) ^ (k + 1) * A * (10 / Gegenbauer.lam m)
              + (k : ℝ) * ((2 : ℝ) ^ k * A * (10 / Gegenbauer.lam m))
            = A * (10 / Gegenbauer.lam m)
              * ((2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k) by ring]
        have hsum : (2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k ≤ 256 + 896 := by linarith
        calc A * (10 / Gegenbauer.lam m) * ((2 : ℝ) ^ (k + 1) + (k : ℝ) * (2 : ℝ) ^ k)
            ≤ A * (10 / Gegenbauer.lam m) * (256 + 896) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = A * 11520 / Gegenbauer.lam m := by ring
          _ ≤ A * 10 ^ 6 / Gegenbauer.lam m := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hlam)
              nlinarith [hA]
          _ = 10 ^ 6 * A / Gegenbauer.lam m := by ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.LinvLopIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000



end Work.FTS.PhiStar.LinvFlat
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.Aux3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadialWAux.Aux3` — the tail integration by parts and the Euler relation for `Ψ`

* `radPsi_tail_ibp_aux`: the integration-by-parts identity for the tail kernel;
* `radPsi_deriv_value_aux`: the first-order Euler relation `z Ψ' = p Ψ - c`;
* `radPsi_base_aux`: the base case `HasDerivAt Ψ (psiFormal 1 z) z`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-! ### C. The tail integration by parts -/

theorem radPsi_tail_ibp_aux {c : ℝ → ℝ} {k : ℕ} {K s z : ℝ} (hk : 1 ≤ k) (hz : 0 < z)
    (hK : 0 ≤ K) (hs : s < -1) (hc : ContDiffOn ℝ k c (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ k → ∀ t : ℝ, 0 < t → |iteratedDeriv j c t| ≤ K) :
    ∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s
      = -(1 / z) * iteratedDeriv (k - 1) c z
        - (s / z) * (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hcontk : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    continuousOn_iteratedDeriv_of (n := k) hc le_rfl
  have hcontk1 : ContinuousOn (iteratedDeriv (k - 1) c) (Set.Ioi 0) :=
    continuousOn_iteratedDeriv_of (n := k) hc (by omega)
  have hdiffc : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (iteratedDeriv (k - 1) c) y := by
    intro y hy
    have hEq : Set.EqOn (iteratedDeriv (k - 1) c) (iteratedDerivWithin (k - 1) c (Set.Ioi 0))
        (Set.Ioi 0) := by
      intro t ht
      exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
        ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
          (by exact_mod_cast (by omega : k - 1 ≤ k))) ht).symm
    have hd : DifferentiableOn ℝ (iteratedDerivWithin (k - 1) c (Set.Ioi 0)) (Set.Ioi 0) :=
      hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : k - 1 < k))
        (uniqueDiffOn_Ioi 0)
    exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)
  -- the antiderivative and its derivative
  have hFderiv : ∀ u ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s)
        (z * iteratedDeriv k c (z * u) * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hzu : 0 < z * u := mul_pos hz hu0
    have hgd : HasDerivAt (iteratedDeriv (k - 1) c) (iteratedDeriv k c (z * u)) (z * u) := by
      simpa only [← iteratedDeriv_succ, hk1'] using (hdiffc (z * u) hzu).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => z * y) z u := by
      simpa using (hasDerivAt_id u).const_mul z
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv (k - 1) c (z * y))
        (iteratedDeriv k c (z * u) * z) u := by
      simpa only [Function.comp_def] using hgd.comp u hlin
    have hmul := hcomp.mul (Real.hasDerivAt_rpow_const (x := u) (p := s) (Or.inl (ne_of_gt hu0)))
    have hval : iteratedDeriv k c (z * u) * z * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))
        = z * iteratedDeriv k c (z * u) * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)) := by
      ring
    exact hmul.congr_deriv hval
  -- the two summands of the derivative are integrable
  have hcont1 : ContinuousOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s)
      (Set.Ioi 1) := by
    have h5 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (z * u)) (Set.Ioi 1) :=
      hcontk.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun u hu => mul_pos hz (lt_trans zero_lt_one hu))
    have h4 : ContinuousOn (fun u : ℝ => u ^ s) (Set.Ioi 1) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun u hu => Or.inl (ne_of_gt (lt_trans zero_lt_one hu)))
    exact ((h5.mul h4).const_mul z).congr (fun u _ => by simp only [Pi.mul_apply]; try ring)
  have hint1 : IntegrableOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_le_rpow (C := z * K) hs (by positivity) hcont1 ?_
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [abs_mul, abs_mul, abs_of_nonneg hz.le, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
    have h1 : |iteratedDeriv k c (z * u)| ≤ K := hb k le_rfl (z * u) (mul_pos hz hu0)
    have h2 : (0 : ℝ) ≤ u ^ s := Real.rpow_nonneg (le_of_lt hu0) s
    have h3 : z * |iteratedDeriv k c (z * u)| ≤ z * K := mul_le_mul_of_nonneg_left h1 hz.le
    calc (z * |iteratedDeriv k c (z * u)|) * u ^ s ≤ (z * K) * u ^ s :=
          mul_le_mul_of_nonneg_right h3 h2
      _ = z * K * u ^ s := by ring
  have hcont2 : ContinuousOn
      (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) := by
    have h5 : ContinuousOn (fun u : ℝ => iteratedDeriv (k - 1) c (z * u)) (Set.Ioi 1) :=
      hcontk1.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun u hu => mul_pos hz (lt_trans zero_lt_one hu))
    have h4 : ContinuousOn (fun u : ℝ => u ^ (s - 1)) (Set.Ioi 1) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun u hu => Or.inl (ne_of_gt (lt_trans zero_lt_one hu)))
    exact (h5.mul (h4.const_mul s)).congr (fun u _ => by simp only [Pi.mul_apply]; try ring)
  have hint2 : IntegrableOn
      (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_le_rpow (C := K * |s|) (t := s - 1) (by linarith) (by positivity) hcont2 ?_
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
    have h1 : |iteratedDeriv (k - 1) c (z * u)| ≤ K := hb (k - 1) (by omega) (z * u) (mul_pos hz hu0)
    have h2 : 0 ≤ |s| * u ^ (s - 1) := by positivity
    calc |iteratedDeriv (k - 1) c (z * u)| * (|s| * u ^ (s - 1)) ≤ K * (|s| * u ^ (s - 1)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = K * |s| * u ^ (s - 1) := by ring
  have hF'int : IntegrableOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s
      + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) :=
    hint1.add hint2
  -- the limit at `∞`
  have hlim : Tendsto (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s) atTop (𝓝 0) := by
    have h0 : Tendsto (fun w : ℝ => K * w ^ s) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := -s) (by linarith)
      simpa only [neg_neg, mul_zero] using h.const_mul K
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu) _)]
    exact mul_le_mul_of_nonneg_right
      (hb (k - 1) (by omega) (z * u) (mul_pos hz hu)) (Real.rpow_nonneg (le_of_lt hu) _)
  have hFcont : ContinuousWithinAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s)
      (Set.Ici (1 : ℝ)) 1 := by
    have hAt : HasDerivAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w))
        (iteratedDeriv k c (z * 1) * z) 1 := by
      have hgd : HasDerivAt (iteratedDeriv (k - 1) c) (iteratedDeriv k c (z * 1)) (z * 1) := by
        simpa only [← iteratedDeriv_succ, hk1'] using (hdiffc (z * 1) (by simpa using hz)).hasDerivAt
      have hlin : HasDerivAt (fun y : ℝ => z * y) z 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).const_mul z
      simpa only [Function.comp_def] using hgd.comp 1 hlin
    exact (hAt.continuousAt.mul
      (continuousAt_id.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))).continuousWithinAt
  have hF1 : iteratedDeriv (k - 1) c (z * 1) * (1 : ℝ) ^ s = iteratedDeriv (k - 1) c z := by
    rw [mul_one, Real.one_rpow, mul_one]
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hFcont hFderiv hF'int hlim
  have hsplit : ∫ u in Set.Ioi (1 : ℝ), (z * iteratedDeriv k c (z * u) * u ^ s
        + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)))
      = z * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s)
        + s * (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) := by
    rw [MeasureTheory.integral_add hint1 hint2]
    congr 1
    · rw [show (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s)
          = fun u : ℝ => z * (iteratedDeriv k c (z * u) * u ^ s) from by funext u; ring,
        MeasureTheory.integral_const_mul]
    · rw [show (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)))
          = fun u : ℝ => s * (iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) from by
        funext u; ring,
        MeasureTheory.integral_const_mul]
  have hmain : z * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s)
      + s * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1))
      = -iteratedDeriv (k - 1) c z := by
    rw [← hsplit, hFTC, hF1]
    ring
  field_simp
  linarith [hmain]

/-! ### E′. The formal-derivative machinery for `Ψ` (self-contained) -/

/-- The formal iterated derivatives of `Ψ`: `psiF 0 = Ψ` and
`z · psiF (j+1) z = (p - j) · psiF j z - c^{(j)}(z)`. -/
noncomputable def psiF (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun n => Nat.rec (radPsi α m c)
    (fun j (fj : ℝ → ℝ) => fun z => ((radP α m - (j : ℝ)) * fj z - iteratedDeriv j c z) / z) n

lemma psiF_zero (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : psiF α m c 0 = radPsi α m c := rfl

lemma psiF_succ (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (j : ℕ) :
    psiF α m c (j + 1) =
      fun z => ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z := rfl

lemma psiF_rec {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (j : ℕ) {z : ℝ} (hz : z ≠ 0) :
    z * psiF α m c (j + 1) z
      = (radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z := by
  rw [psiF_succ]
  field_simp



/-! ### D. The first-order Euler relation and the base case for `Ψ` -/



end Work.FTS.PhiStar.RadialWAux
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.htaumod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.htaumod` — the fake-time Hölder modulus of the extension `g̃`

**Statement.**  Under the joint `C¹`-regularity `hcont` of `(z,τ) ↦ g̃ z θ τ` on the open strip
`(-1,∞) × (-1,S+1)` (one angle `θ ∈ Iθ` at a time) and the `Jet α S Nd` bound `hdt` on the
fake-time derivative `∂_τg̃` on the closed domain `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`, the function
`τ ↦ g̃ z θ τ` is `α`-Hölder on `[0,S]`, uniformly in `(z,θ)` in that domain.

**Proof.**  For fixed `z ≥ 0`, `θ ∈ Iθ` the slice `t ↦ g̃ z θ t` is differentiable at every
`t ∈ [0,S]`: this is the chain rule along the affine curve `t ↦ (z,t)` applied to the joint
`C¹`-function, whose domain `z > -1` contains `z ≥ 0` (`differentiableAt_extG_slice`).  The
mean value theorem on the convex segment `[0,S]` (`norm_image_sub_le_of_norm_deriv_le`) then
bounds the increment by `Nd · |τ - τ'|`, using that *the* derivative
`deriv (fun s => g̃ z θ s) t` is the function whose `Jet` is `hdt`.  Finally `|τ - τ'| ≤ S`, so
`|τ - τ'| = |τ - τ'|^α · |τ - τ'|^{1-α} ≤ S^{1-α} · |τ - τ'|^α` (`Real.rpow_add'` plus
monotonicity of `x ↦ x^{1-α}`, `1 - α ≥ 0`), giving the constant `Lt = Nd · S^{1-α}`.

Note that no case distinction at `z = 0` (nor the boundedness data `hsup`) is needed: the
extension is `C¹` on the whole half-strip `z > -1` and the derivative jet already covers the
closed domain `z ≥ 0`. -/

namespace Work.FTS.RegPkgGal.Der

open Set

/-- **The `τ`-slice of the extension is differentiable.**

If the uncurried family `(z,τ) ↦ g̃ z θ τ` is jointly `C¹` on the open strip
`(-1,∞) × (-1,S+1)` at a fixed angle, then the one-variable slice `t ↦ g̃ z θ t` is
differentiable at every interior point `c` of the strip.  This is the chain rule along the
affine curve `t ↦ (z,t)`, whose derivative is the second basis vector `(0,1)`. -/
theorem differentiableAt_extG_slice {S : ℝ} {g : Work.FTS.RegPkgGal.Fam} {θ z c : ℝ}
    (h : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hz : z ∈ Set.Ioi (-1)) (hc : c ∈ Set.Ioo (-1) (S + 1)) :
    DifferentiableAt ℝ (fun s => Work.FTS.RegPkgGal.extG g z θ s) c := by
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, c) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) := ⟨hz, hc⟩
  have hnb : (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) ∈ nhds (z, c) :=
    hopen.mem_nhds hmem
  have hca : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2) (z, c) :=
    h.contDiffAt hnb
  have hder : HasDerivAt (fun s : ℝ => (z, s)) ((0 : ℝ), (1 : ℝ)) c := by
    have h0 := (hasDerivAt_const (c := z) (x := c)).prodMk (hasDerivAt_id c)
    simpa using h0
  have hcomp := (hca.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt c hder
  have h2 : DifferentiableAt ℝ
      ((fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2) ∘ fun s : ℝ => (z, s)) c :=
    hcomp.differentiableAt
  convert h2 using 1
  ext s
  rfl

theorem htaumod {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hdt : ∃ Nd : ℝ, Work.FTS.Regularity.Jet α S Nd
      (fun z θ τ => deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ))
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Lt : ℝ, 0 ≤ Lt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
          ≤ Lt * |τ - τ'| ^ α := by
  obtain ⟨Nd, hNd⟩ := hdt
  have hLt0 : 0 ≤ Nd * S ^ (1 - α) :=
    mul_nonneg hNd.1 (Real.rpow_nonneg hS.le (1 - α))
  refine ⟨Nd * S ^ (1 - α), hLt0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  -- the fake-time slice is differentiable on the closed strip, with derivative bounded by `Nd`
  have hdiff : ∀ c ∈ Set.Icc 0 S,
      DifferentiableAt ℝ (fun t : ℝ => Work.FTS.RegPkgGal.extG g z θ t) c := by
    intro c hc
    exact differentiableAt_extG_slice (θ := θ) (z := z) (c := c) (S := S)
      (hcont θ hθ) (Set.mem_Ioi.mpr (by linarith))
        (Set.mem_Ioo.mpr ⟨by linarith [hc.1], by linarith [hc.2, hS]⟩)
  have hbound : ∀ c ∈ Set.Icc 0 S,
      ‖deriv (fun t : ℝ => Work.FTS.RegPkgGal.extG g z θ t) c‖ ≤ Nd := by
    intro c hc
    rw [Real.norm_eq_abs]
    exact hNd.abs_le hz hθ hc
  -- the mean value theorem on the segment `[0,S]`
  have hmvt : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
      ≤ Nd * |τ - τ'| := by
    simpa only [Real.norm_eq_abs]
      using Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 S) hτ' hτ
  -- the two `τ`-values lie in `[0,S]`, so `|τ - τ'| ≤ S`
  have hseg : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  -- `|τ - τ'| = |τ - τ'|^α · |τ - τ'|^{1-α}`, and the second factor is `≤ S^{1-α}`
  have hsplit : |τ - τ'| = |τ - τ'| ^ α * |τ - τ'| ^ (1 - α) := by
    have hsum : α + (1 - α) = 1 := by ring
    calc |τ - τ'| = |τ - τ'| ^ (α + (1 - α)) := by simp [hsum]
      _ = |τ - τ'| ^ α * |τ - τ'| ^ (1 - α) :=
            Real.rpow_add' (abs_nonneg _) (by rw [hsum]; norm_num)
  have hpow : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) :=
    Real.rpow_le_rpow (abs_nonneg _) hseg (by linarith)
  calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
      ≤ Nd * |τ - τ'| := hmvt
    _ = Nd * (|τ - τ'| ^ α * |τ - τ'| ^ (1 - α)) := congrArg (fun u => Nd * u) hsplit
    _ ≤ Nd * (|τ - τ'| ^ α * S ^ (1 - α)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNd.1
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg _) α)
    _ = (Nd * S ^ (1 - α)) * |τ - τ'| ^ α := by ring

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.htaumodp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-! ## Slice smoothness of the extension `g̃`

The hypothesis `hcont` of `htaumodp` gives joint `C¹` smoothness of `(z,τ) ↦ g̃ z θ τ` on the
open rectangle `(-1,S+1) × (-1,S+1)`, at every fixed angle `θ ∈ Iθ`.  The two `HasDerivAt`
facts below are its one-variable slices; the `τ`-slice is the one that carries the equation
`∂_τg̃ = R`. -/

lemma contDiffOn_extG_tauSlice {g : Work.FTS.RegPkgGal.Fam} {S θ z : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ 1 (fun σ : ℝ => Work.FTS.RegPkgGal.extG g z θ σ)
      (Set.Ioo (-1) (S + 1)) := by
  have hmap : ContDiffOn ℝ 1 (fun σ : ℝ => (z, σ)) (Set.Ioo (-1) (S + 1)) := by fun_prop
  exact (hcont θ hθ).comp hmap (fun σ hσ => ⟨hz, hσ⟩)

lemma contDiffOn_extG_zSlice {g : Work.FTS.RegPkgGal.Fam} {S θ τ : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) :
    ContDiffOn ℝ 1 (fun ζ : ℝ => Work.FTS.RegPkgGal.extG g ζ θ τ) (Set.Ioi (-1)) := by
  have hmap : ContDiffOn ℝ 1 (fun ζ : ℝ => (ζ, τ)) (Set.Ioi (-1)) := by fun_prop
  exact (hcont θ hθ).comp hmap (fun ζ hζ => ⟨hζ, hτ⟩)

/-- The `τ`-slice of `g̃` at height `z > 0` has derivative `R z θ ·` (the equation `hid`). -/
lemma hasDerivAt_extG_tau {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S θ z x : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) (hx : x ∈ Set.Icc 0 S) :
    HasDerivAt (fun σ => Work.FTS.RegPkgGal.extG g z θ σ) (R z θ x) x := by
  have hz' : (-1 : ℝ) < z := by linarith
  have hcd := contDiffOn_extG_tauSlice hcont hθ hz'
  have hxmem : x ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hca : ContDiffAt ℝ 1 (fun σ => Work.FTS.RegPkgGal.extG g z θ σ) x :=
    hcd.contDiffAt (isOpen_Ioo.mem_nhds hxmem)
  have hd := hca.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hh := hd.hasDerivAt
  rwa [hid z θ x (le_of_lt hz) hθ hx] at hh

/-- The `z`-slice of `g̃` at time `τ` is differentiable everywhere on `z > -1`. -/
lemma hasDerivAt_extG_z {g : Work.FTS.RegPkgGal.Fam} {S θ z τ : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ)
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ) z := by
  have hcd := contDiffOn_extG_zSlice hcont hθ hτ
  have hca : ContDiffAt ℝ 1 (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ) z :=
    hcd.contDiffAt (isOpen_Ioi.mem_nhds hz)
  have hd := hca.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  simpa only [Work.Spaces.pz] using hd.hasDerivAt

/-! ## The two mean-value steps -/

/-- The right-hand side `R` is `z`-Lipschitz with constant `N1` on the open half-line. -/
lemma R_z_mvt {R : ℝ → ℝ → ℝ → ℝ} {S N1 : ℝ}
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    {θ σ z z' : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hσ : σ ∈ Set.Icc 0 S)
    (hz : 0 < z) (hz' : 0 < z') :
    |R z θ σ - R z' θ σ| ≤ N1 * |z - z'| := by
  have hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun ζ => R ζ θ σ) x :=
    fun x hx => ((hRHz σ hσ θ hθ x hx).choose_spec.1).differentiableAt
  have hbnd : ∀ x ∈ Set.Ioi (0 : ℝ), ‖deriv (fun ζ => R ζ θ σ) x‖ ≤ N1 := by
    intro x hx
    obtain ⟨d, hd, hdle⟩ := hRHz σ hσ θ hθ x hx
    rw [hd.deriv, Real.norm_eq_abs]
    exact hdle
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ioi (0 : ℝ)) (x := z) (y := z')
    hdiff hbnd (convex_Ioi (0 : ℝ)) hz hz'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (R z' θ σ) (R z θ σ),
    abs_sub_comm z' z] at h
  exact h

/-- The key mean-value step in the *fake time* variable: the `τ`-difference of `g̃` is itself
`z`-Lipschitz, with the product constant `N1·|z-z'|·|τ-τ'|`. -/
lemma extG_tau_diff_mvt {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ z z' τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) (hz' : 0 < z')
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |(Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')|
      ≤ N1 * |z - z'| * |τ - τ'| := by
  have hderiv : ∀ x ∈ Set.Icc 0 S,
      HasDerivAt (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ)
        (R z θ x - R z' θ x) x := fun x hx =>
    (hasDerivAt_extG_tau hcont hid hθ hz hx).sub (hasDerivAt_extG_tau hcont hid hθ hz' hx)
  have hdiff : ∀ x ∈ Set.Icc 0 S, DifferentiableAt ℝ
      (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ) x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hbnd : ∀ x ∈ Set.Icc 0 S,
      ‖deriv (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ) x‖
        ≤ N1 * |z - z'| := by
    intro x hx
    rw [(hderiv x hx).deriv, Real.norm_eq_abs]
    exact R_z_mvt hRHz hθ hx hz hz'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc 0 S) (x := τ) (y := τ')
    hdiff hbnd (convex_Icc 0 S) hτ hτ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm τ' τ] at h
  have hgoal : |(Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')|
      = |(Work.FTS.RegPkgGal.extG g z θ τ' - Work.FTS.RegPkgGal.extG g z' θ τ')
        - (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ)| := by
    rw [show (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')
        = -((Work.FTS.RegPkgGal.extG g z θ τ' - Work.FTS.RegPkgGal.extG g z' θ τ')
        - (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ)) from by ring,
      abs_neg]
  rw [hgoal]
  exact h

/-! ## The `τ`-modulus of `∂_zg̃` -/

/-- **The pointwise bound for `z > 0`.**  `∂_zg̃(·,θ,τ)` is `τ`-Lipschitz with constant `N1`. -/
lemma pz_tau_le {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ z τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hN1 : 0 ≤ N1) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
      ≤ N1 * |τ - τ'| := by
  have hlip : LipschitzOnWith ⟨N1 * |τ - τ'|, mul_nonneg hN1 (abs_nonneg _)⟩
      (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ - Work.FTS.RegPkgGal.extG g ζ θ τ')
      (Set.Ioi (0 : ℝ)) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    have hm := extG_tau_diff_mvt hcont hid hRHz hθ hx hy hτ hτ'
    calc |(Work.FTS.RegPkgGal.extG g x θ τ - Work.FTS.RegPkgGal.extG g x θ τ')
          - (Work.FTS.RegPkgGal.extG g y θ τ - Work.FTS.RegPkgGal.extG g y θ τ')|
        ≤ N1 * |x - y| * |τ - τ'| := hm
      _ = (N1 * |τ - τ'|) * |x - y| := by ring
  have hnd := norm_deriv_le_of_lipschitzOn (isOpen_Ioi.mem_nhds hz) hlip
  have hd : HasDerivAt
      (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ - Work.FTS.RegPkgGal.extG g ζ θ τ')
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
        - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ) z := by
    have hz1 : (-1 : ℝ) < z := by linarith
    have hm1 : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hm2 : τ' ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    exact (hasDerivAt_extG_z hcont hθ hm1 hz1).sub (hasDerivAt_extG_z hcont hθ hm2 hz1)
  rw [hd.deriv, Real.norm_eq_abs] at hnd
  exact hnd

/-- **The endpoint `z = 0`.**  The bound of `pz_tau_le` extends to `z = 0` by continuity of
`z ↦ ∂_zg̃(z,θ,τ)` at `0` (which is `C¹` smoothness). -/
lemma pz_zero_tau_le {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hN1 : 0 ≤ N1) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) 0 θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') 0 θ|
      ≤ N1 * |τ - τ'| := by
  have hm1 : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hm2 : τ' ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
  have hmono : Set.Ioi (0 : ℝ) ⊆ Set.Ioi (-1 : ℝ) :=
    Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)
  have hcont1 : ContinuousWithinAt
      (fun ζ => deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ) (Set.Ioi 0) 0 :=
    (((contDiffOn_extG_zSlice hcont hθ hm1).continuousOn_deriv_of_isOpen
        isOpen_Ioi le_rfl).continuousWithinAt (by norm_num)).mono hmono
  have hcont2 : ContinuousWithinAt
      (fun ζ => deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ) (Set.Ioi 0) 0 :=
    (((contDiffOn_extG_zSlice hcont hθ hm2).continuousOn_deriv_of_isOpen
        isOpen_Ioi le_rfl).continuousWithinAt (by norm_num)).mono hmono
  have hlim : Filter.Tendsto
      (fun ζ => |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ|) (𝓝[Set.Ioi 0] 0)
      (𝓝 |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) 0
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') 0|) :=
    (hcont1.tendsto.sub hcont2.tendsto).abs
  have hev : ∀ᶠ ζ in 𝓝[Set.Ioi 0] 0,
      |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ| ≤ N1 * |τ - τ'| := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact pz_tau_le hcont hid hRHz hN1 hθ hζ hτ hτ'
  have hfin := le_of_tendsto hlim hev
  simpa only [Work.Spaces.pz] using hfin

/-! ## The theorem -/

theorem htaumodp {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∃ N1 : ℝ, 0 ≤ N1 ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
          ≤ Nt * |τ - τ'| ^ α := by
  obtain ⟨M, hMnn, hM⟩ := hsup
  obtain ⟨N1, hN1nn, hN1⟩ := hRHz
  have hNt0 : (0 : ℝ) ≤ max N1 (2 * M) := le_trans hN1nn (le_max_left _ _)
  refine ⟨max N1 (2 * M), hNt0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hkey : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
      ≤ N1 * |τ - τ'| := by
    rcases lt_or_eq_of_le hz with hzpos | hz0
    · exact pz_tau_le hcont hid hN1 hN1nn hθ hzpos hτ hτ'
    · rw [← hz0]
      exact pz_zero_tau_le hcont hid hN1 hN1nn hθ hτ hτ'
  have hbd : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ| ≤ 2 * M := by
    have h1 := hM τ hτ z θ hz hθ
    have h2 := hM τ' hτ' z θ hz hθ
    have h3 := abs_sub (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ)
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ)
    linarith
  rcases le_or_gt |τ - τ'| 1 with hle | hgt
  · have hrpow : |τ - τ'| ≤ |τ - τ'| ^ α := by
      rcases eq_or_lt_of_le (abs_nonneg (τ - τ')) with h0 | h0
      · rw [← h0, Real.zero_rpow hα.ne']
      · have hh := Real.rpow_le_rpow_of_exponent_ge h0 hle hα1
        rwa [Real.rpow_one] at hh
    calc |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
        ≤ N1 * |τ - τ'| := hkey
      _ ≤ max N1 (2 * M) * |τ - τ'| ^ α :=
          mul_le_mul (le_max_left N1 (2 * M)) hrpow (abs_nonneg _) hNt0
  · have hrpow : 1 ≤ |τ - τ'| ^ α := Real.one_le_rpow hgt.le (le_of_lt hα)
    calc |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
        ≤ 2 * M := hbd
      _ ≤ max N1 (2 * M) * |τ - τ'| ^ α := by
          calc 2 * M ≤ max N1 (2 * M) * 1 := by rw [mul_one]; exact le_max_right N1 (2 * M)
            _ ≤ max N1 (2 * M) * |τ - τ'| ^ α := mul_le_mul_of_nonneg_left hrpow hNt0

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.hzmod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem hzmod {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Lz : ℝ, 0 ≤ Lz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
          ≤ Lz * |z - z'| ^ α := by
  obtain ⟨M, hM0, hM⟩ := hsup
  -- The uniform bound `M` on `g̃` and on `∂_zg̃` makes every `z`-slice Lipschitz with constant `M`;
  -- a Lipschitz function is `α`-Hölder for every `0 < α ≤ 1` (with constant `2M`).
  refine ⟨2 * M, by linarith, ?_⟩
  intro τ hτ z z' hz hz' θ hθ
  have hτmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- The `z`-slice of the joint `C¹` function `(z,τ) ↦ g̃ z θ τ` is `C¹` on `Ioi (-1)`.
  have hmaps : Set.MapsTo (fun x : ℝ => (x, τ)) (Set.Ioi (-1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) := fun x hx => ⟨hx, hτmem⟩
  have hf : ContDiffOn ℝ 1 (fun x : ℝ => (x, τ)) (Set.Ioi (-1)) := by fun_prop
  have hslice : ContDiffOn ℝ 1 (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ)
      (Set.Ioi (-1)) := (hcont θ hθ).comp hf hmaps
  have hdiff : ∀ x ∈ Set.Icc 0 (max z z'),
      DifferentiableAt ℝ (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ) x := by
    intro x hx
    refine (hslice.differentiableOn (by norm_num)).differentiableAt ?_
    exact IsOpen.mem_nhds isOpen_Ioi (by simp only [Set.mem_Ioi]; linarith [hx.1])
  have hbnd : ∀ x ∈ Set.Icc 0 (max z z'),
      ‖deriv (fun x : ℝ => Work.FTS.RegPkgGal.extG g x θ τ) x‖ ≤ M := by
    intro x hx
    have hx' := (hM τ hτ x θ hx.1 hθ).2
    rw [Real.norm_eq_abs]
    simpa only [Work.Spaces.pz] using hx'
  have hzmem : z ∈ Set.Icc 0 (max z z') := ⟨hz, le_max_left _ _⟩
  have hz'mem : z' ∈ Set.Icc 0 (max z z') := ⟨hz', le_max_right _ _⟩
  -- Mean value theorem on the segment `[0, max z z']`.
  have hmvt : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
      ≤ M * |z - z'| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_Icc 0 (max z z'))
      hz'mem hzmem
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h
  have hd : 0 ≤ |z - z'| := abs_nonneg _
  rcases le_or_gt |z - z'| 1 with hle | hlt
  · -- `|z - z'| ≤ 1`: use `|z - z'| ≤ |z - z'| ^ α` and the Lipschitz bound.
    have hdα : |z - z'| ≤ |z - z'| ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge' hd hle hα.le hα1
      simpa using this
    calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ M * |z - z'| := hmvt
      _ ≤ M * |z - z'| ^ α := by gcongr
      _ ≤ 2 * M * |z - z'| ^ α := by nlinarith [Real.rpow_nonneg hd α, hM0]
  · -- `1 < |z - z'|`: use the two sup bounds and `1 ≤ |z - z'| ^ α`.
    have h1 : (1 : ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hlt.le hα.le
    have hupper : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ 2 * M := by
      have hz1 := (hM τ hτ z θ hz hθ).1
      have hz2 := (hM τ hτ z' θ hz' hθ).1
      have := abs_sub (Work.FTS.RegPkgGal.extG g z θ τ) (Work.FTS.RegPkgGal.extG g z' θ τ)
      linarith
    calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ|
        ≤ 2 * M := hupper
      _ ≤ 2 * M * |z - z'| ^ α :=
          le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ 2 * M) h1

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.hzmodp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.sup2_extG_ext =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open Set

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`.  (This is a verbatim copy of the private lemma of the same name in `sup2_extG.lean`,
which is not exported.) -/
private lemma pz_pz_extG_eq {g : Work.FTS.RegPkgGal.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.sup_extG_ext =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Locality of the slice `z`-derivative for the extension.**  For `z > 0` and `τ ∈ [0,S]` the
slice of `g̃ = extG g` at time `τ` agrees with the slice of `g` on the open half line `Ioi 0`,
hence so do their `z`-derivatives. -/
theorem pz_gSlice_extG_eq {g : ℝ → ℝ → ℝ → ℝ} {S τ θ z : ℝ} (hτ : τ ∈ Set.Icc 0 S) (hz : 0 < z) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ) z θ
      = Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ := by
  have hev : (fun z' => Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.FTS.Regularity.gSlice g τ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    simp only [Work.FTS.Regularity.gSlice]
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1
  calc Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ) z θ
      = deriv (fun z' => Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ z' θ) z := rfl
    _ = deriv (fun z' => Work.FTS.Regularity.gSlice g τ z' θ) z := hev.deriv_eq
    _ = Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ := rfl


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.GalMin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE REDUCED INPUT BUNDLE.**  See the module docstring: `GalHyp` minus the five derivable
fields (`hsup`, `hhz`, `hhzp`, `hhτ`, `hhτp`) and their constants, plus `StData2`, `RegQ` and the
uniform `ℋ⁴` bound. -/
structure GalMin (α S : ℝ) (g : Fam) (m : ℝ → ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ)
    (a b c Lz7 : ℝ) : Prop where
  /-- the Hölder exponent is positive -/
  hα : 0 < α
  /-- the paper's regime -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the lead's minimal Galerkin input (design `FTS_STRONG_ROUTE.md` §1/§4) -/
  hmin : RegPkgMin (pExp α) g
  /-- the modulation rate of design §2 is continuous near the strip -/
  hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1))
  /-- `|m| ≤ 1/2` on the strip (design §2) -/
  hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2
  /-- `m` is `α`-Hölder on the strip (design §2, `muDyn_holderOn`) -/
  hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |m τ - m τ'| ≤ L * |τ - τ'| ^ α
  /-- **THE ONE NAMED CLASS-DATA CONJUNCT** (`St1Class.lean`): the `Γ`-vanishing of `D_θg̃` with its
  `z²` factor, the Taylor data at `z = 0`, the second-order `z`-bound at the origin, and the two
  angular moduli `hhθ`, `hhθp`.  Not derivable from `RegPkgMin` + the `ℋ⁴` bound (NOTES §2, §8,
  §11.4), so it is the export the strong-solution/persistence side must provide. -/
  hSt1 : St1Class α S g
  /-- the frozen interior class `RegQ (pExp α) 4` of every slice (the class the estimates use) -/
  hRQ : ∀ τ ∈ Set.Icc 0 S, Work.FTS.Nonlin.RegQ (pExp α) 4 (gSlice g τ)
  /-- the uniform `ℋ⁴` bound of the slices on the strip -/
  hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
    Work.Spaces.HkNorm (pExp α) 4 (gSlice g τ) ≤ C₀
  /-- R1's joint `C¹` hypothesis on `{z > 0}` -/
  hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit `(z,τ) → (0,τ₀)` of `g` -/
  hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹g` -/
  hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_zg` -/
  hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_τg` -/
  hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: `C¹` of `z ↦ ∂_τg(z,θ,0)` on `{z > 0}` -/
  hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit of `∂_z(∂_τg(·,θ,0))` -/
  hd1z : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹∂_τg(z,θ,0)` -/
  hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: right continuity of `τ ↦ ∂_τg` at `τ = 0` -/
  ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
    Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))
  /-- R7: joint `C¹` of the full profile `F = F_* + g̃` on the slab -/
  hFjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => profFull α (extG g) p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: joint continuity of the transport velocity on the closed angular box -/
  hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: a `τ`-uniform Lipschitz constant for the velocity, required only on `z > Lz7` (the
  region visited by the backward characteristics, which stay above `Lz7` because `0 ≤ Vz ≤ a` and
  the support threshold is `Lz7·e^{aS}`; design item R-a, `R7e.support_strip_zL`) -/
  hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
    (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
    (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- R7: continuity of the source coefficient -/
  hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: the transport equation `(E)` in the characteristic form -/
  hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
    HasDerivAt (fun s => profFull α (extG g) z θ s)
      (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => profFull α (extG g) z θ τ) z θ
        + Vθ z θ τ * Work.Spaces.pth (fun z θ => profFull α (extG g) z θ τ) z θ
        + cs z θ τ * profFull α (extG g) z θ τ)) τ
  /-- R7: non-negativity of the `z`-speed -/
  hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ
  /-- R7: the `z`-speed bound -/
  hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a
  /-- R7: the `θ`-speed bound -/
  hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b
  /-- R7: the `θ`-speed vanishes at `θ = 0` -/
  hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0
  /-- R7: the `θ`-speed vanishes at `θ = π/2` -/
  hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0
  /-- R7: the source coefficient is bounded -/
  hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c
  /-- R7: the initial support of the profile (the localised datum) -/
  hInit : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
    profFull α (extG g) z θ 0 = 0
  /-- the profile vanishes for `z ≥ L` at the angles *outside* `Iθ` -/
  hsuppOut : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
    θ ∉ Work.Spaces.Iθ → profFull α (extG g) z θ τ = 0
  /-- R7: the support threshold is non-negative -/
  hLz7 : 0 ≤ Lz7
  /-- R7: the `z`-speed bound is non-negative -/
  ha : 0 ≤ a
  /-- R7: the `θ`-speed bound is non-negative -/
  hb : 0 ≤ b
  /-- R7: the source bound is non-negative -/
  hc : 0 ≤ c

end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1c.extG_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1c

open Set Filter Topology MeasureTheory
open scoped Topology Real ContDiff
open Work.FTS.RegPkgGal.R1b

set_option autoImplicit false

/-! ## The corner `z = 0`: the two local statements -/

/-- **The corner at `z = 0` is differentiable.**  `extG g` has derivative `0` at `(0,τ₀)`,
using the limits at `τ₀ = 0` only (the base family enters only when `0 ≤ τ₀`, where the limit
at `τ₀` is available). -/
theorem hasFDerivAt_extFun_zero {S : ℝ} (hS : 0 < S) {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hjz : ∀ τ₀ ∈ Ico (0:ℝ) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    (hd1z2 : Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
        (nhdsWithin (0, 0) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo (-1) (S + 1)) :
    HasFDerivAt (extFun g θ) (0 : (ℝ × ℝ) →L[ℝ] ℝ) ((0:ℝ), τ₀) := by
  refine (hasFDerivAt_iff_isLittleO).2 ?_
  have hsub : (fun y : ℝ × ℝ =>
        extFun g θ y - extFun g θ ((0:ℝ), τ₀)
          - (0 : (ℝ × ℝ) →L[ℝ] ℝ) (y - ((0:ℝ), τ₀)))
      = fun y : ℝ × ℝ => extFun g θ y := by
    funext y
    rw [extFun_of_nonpos g θ le_rfl]
    simp
  rw [hsub]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  set η : ℝ := c / (2 * (|τ₀| + 2)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hηK : η * (|τ₀| + 2) = c / 2 := by rw [hηdef]; field_simp
  have hηc : η ≤ c := by
    rw [hηdef]
    have h2 : (1:ℝ) ≤ 2 * (|τ₀| + 2) := by nlinarith [abs_nonneg τ₀]
    calc c / (2 * (|τ₀| + 2)) ≤ c / 1 := div_le_div_of_nonneg_left (le_of_lt hc) one_pos h2
      _ = c := by ring
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := slice_bound_of_tendsto hηpos (hjz 0 ⟨le_rfl, by linarith⟩)
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := slice_bound_of_tendsto hηpos hd1z2
  have hev₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → |y.1⁻¹ * g y.1 θ 0| < η := by
    filter_upwards [eventually_box τ₀ δ₂ hδ₂pos] with y hy hy1
    exact hδ₂ y.1 hy1 (hy hy1).1
  have hev₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → |y.1⁻¹ * tauDer g θ y.1| < η := by
    filter_upwards [eventually_box τ₀ δ₃ hδ₃pos] with y hy hy1
    exact hδ₃ y.1 hy1 (hy hy1).1
  have hev₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀), 0 < y.1 → y.1 < 1 := by
    filter_upwards [eventually_box τ₀ 1 one_pos] with y hy hy1
    exact (hy hy1).1
  have hevτ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀), 0 < y.1 → |y.2 - τ₀| < 1 := by
    filter_upwards [eventually_box τ₀ 1 one_pos] with y hy hy1
    exact (hy hy1).2
  -- The base branch of the family is used only when `0 ≤ τ₀`; for `τ₀ < 0` it stays at
  -- distance `≥ |τ₀|` from `(0,τ₀)`, so it does not occur in a small box.
  have hyA : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → 0 ≤ y.2 → |g y.1 θ y.2| < η * y.1 := by
    by_cases hτ0 : 0 ≤ τ₀
    · filter_upwards [eventually_of_tendsto_box hηpos (hjz τ₀ ⟨hτ0, hτ₀.2⟩)] with y hy hy1 _
      exact abs_lt_mul_of_abs_inv_mul_lt hy1 (hy hy1)
    · push_neg at hτ0
      filter_upwards [eventually_box τ₀ (|τ₀| / 2) (by rw [abs_of_neg hτ0]; linarith)]
        with y hy hy1 hy2
      exfalso
      have hb : |y.2 - τ₀| < |τ₀| / 2 := (hy hy1).2
      have h1 : |τ₀| ≤ |y.2 - τ₀| := by
        rw [abs_of_neg hτ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ y.2 - τ₀)]
        linarith
      linarith [abs_pos.mpr (ne_of_lt hτ0)]
  filter_upwards [hyA, hev₂, hev₃, hev₁, hevτ] with y hA h₂ h₃ h₁ hτ
  rw [Real.norm_eq_abs]
  by_cases hy1 : 0 < y.1
  · have hg0 : |g y.1 θ 0| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (h₂ hy1)
    have hdd : |tauDer g θ y.1| < η * y.1 := abs_lt_mul_of_abs_inv_mul_lt hy1 (h₃ hy1)
    have hyt : |y.2| ≤ |τ₀| + 1 := by
      have habs : |y.2 - τ₀| < 1 := hτ hy1
      calc |y.2| = |(y.2 - τ₀) + τ₀| := by ring_nf
        _ ≤ |y.2 - τ₀| + |τ₀| := abs_add_le _ _
        _ ≤ |τ₀| + 1 := by linarith [habs]
    have hnorm : y.1 ≤ ‖y - ((0:ℝ), τ₀)‖ := by
      have hle : y.1 ≤ max |y.1| |y.2 - τ₀| := by
        rw [abs_of_pos hy1]; exact le_max_left _ _
      calc y.1 ≤ max |y.1| |y.2 - τ₀| := hle
        _ = ‖y - ((0:ℝ), τ₀)‖ := by
            rw [Prod.norm_def]
            simp [Real.norm_eq_abs]
    rcases lt_or_ge y.2 0 with hy2 | hy2
    · -- jet branch
      have he : extFun g θ y = jetFn g θ y := by
        obtain ⟨y1, y2⟩ := y
        exact extFun_of_pos_of_neg g θ hy1 hy2
      rw [he, jetFn_apply]
      have hb : |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ₀| + 2) := by
        have h1 : |y.2 * tauDer g θ y.1| = |y.2| * |tauDer g θ y.1| := abs_mul _ _
        have h2 : |y.2| * |tauDer g θ y.1| ≤ (|τ₀| + 1) * (η * y.1) :=
          mul_le_mul hyt (le_of_lt hdd) (abs_nonneg _) (by positivity)
        have h3 : |g y.1 θ 0 + y.2 * tauDer g θ y.1|
            ≤ |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by
          calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
              ≤ |g y.1 θ 0| + |y.2 * tauDer g θ y.1| := abs_add_le _ _
            _ = |g y.1 θ 0| + |y.2| * |tauDer g θ y.1| := by rw [h1]
        have h4 : |g y.1 θ 0| + |y.2| * |tauDer g θ y.1|
            ≤ η * y.1 + (|τ₀| + 1) * (η * y.1) := add_le_add (le_of_lt hg0) h2
        calc |g y.1 θ 0 + y.2 * tauDer g θ y.1|
            ≤ η * y.1 + (|τ₀| + 1) * (η * y.1) := le_trans h3 h4
          _ = η * y.1 * (|τ₀| + 2) := by ring
      calc |g y.1 θ 0 + y.2 * tauDer g θ y.1| ≤ η * y.1 * (|τ₀| + 2) := hb
        _ = (c / 2) * y.1 := by rw [← hηK]; ring
        _ ≤ (c / 2) * ‖y - ((0:ℝ), τ₀)‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ ≤ c * ‖y - ((0:ℝ), τ₀)‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · -- family branch
      have hgr : |g y.1 θ y.2| < η * y.1 := hA hy1 hy2
      have he : extFun g θ y = baseFn g θ y := by
        obtain ⟨y1, y2⟩ := y
        exact extFun_of_pos_of_nonneg g θ hy1 hy2
      rw [he, baseFn_apply]
      calc |g y.1 θ y.2| ≤ η * y.1 := le_of_lt hgr
        _ ≤ η * ‖y - ((0:ℝ), τ₀)‖ := mul_le_mul_of_nonneg_left hnorm (le_of_lt hηpos)
        _ ≤ c * ‖y - ((0:ℝ), τ₀)‖ := mul_le_mul_of_nonneg_right hηc (norm_nonneg _)
  · -- `y.1 ≤ 0`: the extension vanishes
    obtain ⟨y1, y2⟩ := y
    rw [extFun_of_nonpos g θ (le_of_not_gt hy1)]
    simp only [abs_zero]
    exact mul_nonneg (le_of_lt hc) (by positivity)

/-- **The corner at `z = 0`: continuity of the candidate derivative.**  `extDeriv g θ` is
continuous at `(0,τ₀)`.  The jet branch uses the limits at `τ₀ = 0`; the base branch is used
only when `0 ≤ τ₀` (its limits at `τ₀`), and for `τ₀ < 0` it is unreachable in a small box. -/
theorem continuousAt_extDeriv_zero {S : ℝ} (hS : 0 < S) {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hjdz : ∀ τ₀ ∈ Ico (0:ℝ) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
        (nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    (hd1z : Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
        (nhdsWithin (0, 0) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    (hd1z2 : Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
        (nhdsWithin (0, 0) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    (hjdt : ∀ τ₀ ∈ Ico (0:ℝ) (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ)) (nhds 0))
    (hz0diff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (fun z' => g z' θ 0) z)
    (hτdiff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (tauDer g θ) z)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo (-1) (S + 1)) :
    ContinuousAt (extDeriv g θ) ((0:ℝ), τ₀) := by
  have hxd : extDeriv g θ ((0:ℝ), τ₀) = 0 := extDeriv_of_nonpos g θ le_rfl τ₀
  rw [ContinuousAt, hxd, Metric.tendsto_nhds]
  simp_rw [dist_zero_right]
  intro ε hε
  set η : ℝ := ε / (2 * (|τ₀| + 3)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hηK : η * (|τ₀| + 3) = ε / 2 := by rw [hηdef]; field_simp
  have hηε : η ≤ ε := by
    rw [hηdef]
    have h2 : (1:ℝ) ≤ 2 * (|τ₀| + 3) := by nlinarith [abs_nonneg τ₀]
    calc ε / (2 * (|τ₀| + 3)) ≤ ε / 1 := div_le_div_of_nonneg_left (le_of_lt hε) one_pos h2
      _ = ε := by ring
  have hslice₀ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → |deriv (fun z => g z θ 0) y.1| < η := by
    obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos (hjdz 0 ⟨le_rfl, by linarith⟩)
    filter_upwards [eventually_box τ₀ δ hδ] with y hy hy1
    exact H y.1 hy1 (hy hy1).1
  have hslice₁ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → |deriv (fun z => deriv (fun s => g z θ s) 0) y.1| < η := by
    obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos hd1z
    filter_upwards [eventually_box τ₀ δ hδ] with y hy hy1
    exact H y.1 hy1 (hy hy1).1
  have hslice₂ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → |tauDer g θ y.1| < η * y.1 := by
    obtain ⟨δ, hδ, H⟩ := slice_bound_of_tendsto hηpos hd1z2
    filter_upwards [eventually_box τ₀ δ hδ] with y hy hy1
    exact abs_lt_mul_of_abs_inv_mul_lt hy1 (H y.1 hy1 (hy hy1).1)
  have hslice₃ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀), 0 < y.1 → y.1 < 1 := by
    filter_upwards [eventually_box τ₀ 1 one_pos] with y hy hy1
    exact (hy hy1).1
  have hslice₄ : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀), 0 < y.1 → |y.2 - τ₀| < 1 := by
    filter_upwards [eventually_box τ₀ 1 one_pos] with y hy hy1
    exact (hy hy1).2
  have hdz : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → 0 ≤ y.2 → |deriv (fun z' => baseFn g θ (z', y.2)) y.1| < η := by
    by_cases hτ0 : 0 ≤ τ₀
    · filter_upwards [eventually_of_tendsto_box hηpos (hjdz τ₀ ⟨hτ0, hτ₀.2⟩)] with y hy hy1 _
      simpa only [baseFn] using hy hy1
    · push_neg at hτ0
      filter_upwards [eventually_box τ₀ (|τ₀| / 2) (by rw [abs_of_neg hτ0]; linarith)]
        with y hy hy1 hy2
      exfalso
      have hb : |y.2 - τ₀| < |τ₀| / 2 := (hy hy1).2
      have h1 : |τ₀| ≤ |y.2 - τ₀| := by
        rw [abs_of_neg hτ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ y.2 - τ₀)]
        linarith
      linarith [abs_pos.mpr (ne_of_lt hτ0)]
  have hdt : ∀ᶠ y : ℝ × ℝ in 𝓝 ((0:ℝ), τ₀),
      0 < y.1 → 0 ≤ y.2 → |deriv (fun t => baseFn g θ (y.1, t)) y.2| < η := by
    by_cases hτ0 : 0 ≤ τ₀
    · filter_upwards [eventually_of_tendsto_box hηpos (hjdt τ₀ ⟨hτ0, hτ₀.2⟩)] with y hy hy1 _
      simpa only [baseFn] using hy hy1
    · push_neg at hτ0
      filter_upwards [eventually_box τ₀ (|τ₀| / 2) (by rw [abs_of_neg hτ0]; linarith)]
        with y hy hy1 hy2
      exfalso
      have hb : |y.2 - τ₀| < |τ₀| / 2 := (hy hy1).2
      have h1 : |τ₀| ≤ |y.2 - τ₀| := by
        rw [abs_of_neg hτ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ y.2 - τ₀)]
        linarith
      linarith [abs_pos.mpr (ne_of_lt hτ0)]
  filter_upwards [hdz, hdt, hslice₀, hslice₁, hslice₂, hslice₃, hslice₄]
    with y hdz' hdt' h₀ h₁ h₂ h₃ h₄
  by_cases hy1 : 0 < y.1
  · rcases lt_or_ge y.2 0 with hy2 | hy2
    · -- jet branch
      have hye : extDeriv g θ y = jetBranch g θ y := by
        obtain ⟨y1, y2⟩ := y
        exact extDeriv_of_pos_of_neg' g θ hy1 hy2
      rw [hye]
      have hsplit : ‖jetBranch g θ y‖
          ≤ |deriv (fun z' => jetFn g θ (z', y.2)) y.1|
            + |deriv (fun t => jetFn g θ (y.1, t)) y.2| := by
        simp only [jetBranch]
        exact norm_smul_fst_add_smul_snd_le _ _
      have hzf : deriv (fun z' => jetFn g θ (z', y.2)) y.1
          = deriv (fun z' => g z' θ 0) y.1
            + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1 :=
        deriv_jetFn_fst g θ (hz0diff y.1 hy1) (hτdiff y.1 hy1)
      have htf : deriv (fun t => jetFn g θ (y.1, t)) y.2 = tauDer g θ y.1 :=
        deriv_jetFn_snd g θ y.1 y.2
      rw [hzf, htf] at hsplit
      have hyt : |y.2| ≤ |τ₀| + 1 := by
        have habs : |y.2 - τ₀| < 1 := h₄ hy1
        calc |y.2| = |(y.2 - τ₀) + τ₀| := by ring_nf
          _ ≤ |y.2 - τ₀| + |τ₀| := abs_add_le _ _
          _ ≤ |τ₀| + 1 := by linarith [habs]
      have hb : |deriv (fun z' => g z' θ 0) y.1
            + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
          + |tauDer g θ y.1| < ε := by
        have hI : |deriv (fun z' => g z' θ 0) y.1
            + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
            ≤ η + (|τ₀| + 1) * η := by
          calc |deriv (fun z' => g z' θ 0) y.1
                + y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1|
              ≤ |deriv (fun z' => g z' θ 0) y.1|
                + |y.2 * deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := abs_add_le _ _
            _ = |deriv (fun z' => g z' θ 0) y.1|
                + |y.2| * |deriv (fun z' => deriv (fun s => g z' θ s) 0) y.1| := by
                  rw [abs_mul]
            _ ≤ η + (|τ₀| + 1) * η :=
                  add_le_add (le_of_lt (h₀ hy1))
                    (mul_le_mul hyt (le_of_lt (h₁ hy1)) (abs_nonneg _) (by positivity))
        have hII : |tauDer g θ y.1| ≤ η :=
          le_of_lt (lt_of_lt_of_le (h₂ hy1) (by nlinarith [h₃ hy1]))
        have hIII : η + (|τ₀| + 1) * η + η ≤ ε := by
          have heq : η + (|τ₀| + 1) * η + η = η * (|τ₀| + 3) := by ring
          rw [heq, hηK]
          linarith
        linarith [hI, hII, hIII]
      exact lt_of_le_of_lt hsplit hb
    · -- family branch
      have hye : extDeriv g θ y = baseBranch g θ y := by
        obtain ⟨y1, y2⟩ := y
        exact extDeriv_of_pos_of_nonneg' g θ hy1 hy2
      rw [hye]
      have hsplit : ‖baseBranch g θ y‖
          ≤ |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
            + |deriv (fun t => baseFn g θ (y.1, t)) y.2| := by
        simp only [baseBranch]
        exact norm_smul_fst_add_smul_snd_le _ _
      have hb : |deriv (fun z' => baseFn g θ (z', y.2)) y.1|
          + |deriv (fun t => baseFn g θ (y.1, t)) y.2| < ε := by
        have h1 : |deriv (fun z' => baseFn g θ (z', y.2)) y.1| < η := hdz' hy1 hy2
        have h2 : |deriv (fun t => baseFn g θ (y.1, t)) y.2| < η := hdt' hy1 hy2
        have hηhalf : η ≤ ε / 2 := by
          rw [hηdef]
          have h2 : (2:ℝ) ≤ 2 * (|τ₀| + 3) := by linarith [abs_nonneg τ₀]
          exact div_le_div_of_nonneg_left (le_of_lt hε) (by norm_num) h2
        linarith [h1, h2, hηhalf]
      exact lt_of_le_of_lt hsplit hb
  · -- `y.1 ≤ 0`
    have hye : extDeriv g θ y = 0 := by
      obtain ⟨y1, y2⟩ := y
      exact extDeriv_of_nonpos g θ (le_of_not_gt hy1) y2
    rw [hye]
    simpa using hε

/-! ## The gluing -/

theorem extG_cont {S : ℝ} (hS : 0 < S) {g : ℝ → ℝ → ℝ → ℝ}
    (hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (-1)))
    (hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
        (nhdsWithin (0, τ₀) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
        (nhdsWithin (0, τ₀) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (-1)))
    (hd1z : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
        (nhdsWithin (0, 0) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
        (nhdsWithin (0, 0) (Set.Ioi (0:ℝ) ×ˢ Set.univ)) (nhds 0))
    (ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))) :
    ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) := by
  intro θ hθ
  change ContDiffOn ℝ 1 (extFun g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1))
  have hUopen : IsOpen (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := isOpen_Ioi.prod isOpen_Ioo
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hbase θ hθ
  have hddV : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := hd1 θ hθ
  have hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    jetFn_contDiffOn hbaseV hddV
  have hτV : ContDiffOn ℝ 1 (tauDer g θ) (Ioi (0:ℝ)) := tauDer_contDiffOn hddV
  have hbaseAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (baseFn g θ) (fderiv ℝ (baseFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hbaseV hx
  have hjetAt : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)),
      HasFDerivAt (jetFn g θ) (fderiv ℝ (jetFn g θ) x) x :=
    fun x hx => hasFDerivAt_of_contDiffOn_one hVopen hjetV hx
  have hbasediff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (baseFn g θ) x :=
    fun x hx => (hbaseAt x hx).differentiableAt
  have hjetdiff : ∀ x ∈ (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)), DifferentiableAt ℝ (jetFn g θ) x :=
    fun x hx => (hjetAt x hx).differentiableAt
  have hτdiff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (tauDer g θ) z :=
    fun z hz => (hτV.differentiableOn one_ne_zero z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hz0diff : ∀ z ∈ Ioi (0:ℝ), DifferentiableAt ℝ (fun z' => g z' θ 0) z := by
    intro z hz
    have hzc : DifferentiableAt ℝ (fun z' : ℝ => (z', (0:ℝ))) z := by fun_prop
    have hbd : DifferentiableAt ℝ (baseFn g θ) (z, (0:ℝ)) := hbasediff (z, 0) ⟨hz, by norm_num⟩
    have hcomp := hbd.comp z hzc
    simpa [Function.comp_def, baseFn] using hcomp
  have hAcont : ContinuousOn (jetBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_jetBranch hjetV
  have hBcont : ContinuousOn (baseBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    continuousOn_baseBranch hbaseV
  have h0mem : (0:ℝ) ∈ Ioo (-1:ℝ) (S + 1) := ⟨by norm_num, by linarith⟩
  -- ## Step 1: differentiability with derivative `extDeriv`
  have hderiv : ∀ x ∈ (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)),
      HasFDerivAt (extFun g θ) (extDeriv g θ x) x := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`: the extension vanishes identically nearby
      have hxd : extDeriv g θ (z, τ) = 0 := extDeriv_of_nonpos g θ (le_of_lt hz) τ
      rw [hxd]
      refine (hasFDerivAt_const (c := (0:ℝ)) (x := ((z, τ) : ℝ × ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
      exact extFun_of_nonpos g θ (le_of_lt hy)
    · -- `z = 0`: the corner; everything is `o(z)` in the *joint* variable, uniformly in
      -- `τ₀`; see `hasFDerivAt_extFun_zero` (only the limits at `τ₀ = 0` are used)
      subst hz
      have hxd : extDeriv g θ ((0:ℝ), τ) = 0 := extDeriv_of_nonpos g θ le_rfl τ
      rw [hxd]
      exact hasFDerivAt_extFun_zero hS (hjz θ hθ) (hd1z2 θ hθ) hτU
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hxd : extDeriv g θ (z, τ) = fderiv ℝ (jetFn g θ) (z, τ) :=
          extDeriv_eq_fderiv_jetFn g θ hz hτn (hjetdiff (z, τ) hxV)
        rw [hxd]
        refine (hjetAt (z, τ) hxV).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
          (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
        exact extFun_of_pos_of_neg g θ hy1 hy2
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hxd : extDeriv g θ (z, τ) = fderiv ℝ (baseFn g θ) (z, τ) :=
            extDeriv_eq_fderiv_baseFn g θ hz (le_of_lt hτp) (hbasediff (z, τ) hxV)
          rw [hxd]
          refine (hbaseAt (z, τ) hxV).congr_of_eventuallyEq ?_
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
          exact extFun_of_pos_of_nonneg g θ hy1 (le_of_lt hy2)
        · -- the `τ = 0` join
          subst hτ0
          exact hasFDerivAt_extFun_join hz hbaseV hjetV
  -- ## Step 2: continuity of the candidate derivative
  have hcont : ContinuousOn (extDeriv g θ) (Ioi (-1:ℝ) ×ˢ Ioo (-1:ℝ) (S + 1)) := by
    rintro ⟨z, τ⟩ hxU
    have hτU : τ ∈ Ioo (-1:ℝ) (S + 1) := hxU.2
    rcases lt_trichotomy z 0 with hz | hz | hz
    · -- `z < 0`
      have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun _ => (0 : (ℝ × ℝ) →L[ℝ] ℝ)) := by
        filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds hz] with y hy
        exact extDeriv_of_nonpos g θ (le_of_lt hy) y.2
      exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
    · -- `z = 0`: continuity of the candidate derivative; see `continuousAt_extDeriv_zero`
      subst hz
      exact (continuousAt_extDeriv_zero hS (hjdz θ hθ) (hd1z θ hθ) (hd1z2 θ hθ)
        (hjdt θ hθ) hz0diff hτdiff hτU).continuousWithinAt
    · -- `z > 0`
      have hxV : (z, τ) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, hτU.1⟩
      by_cases hτn : τ < 0
      · -- the jet branch
        have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] jetBranch g θ := by
          filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
            (isOpen_Iio.preimage continuous_snd).mem_nhds hτn] with y hy1 hy2
          exact extDeriv_of_pos_of_neg' g θ hy1 hy2
        exact ((hAcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
      · rcases lt_or_eq_of_le (le_of_not_gt hτn) with hτp | hτ0
        · -- the family branch
          have hev : extDeriv g θ =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] baseBranch g θ := by
            filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
              (isOpen_Ioi.preimage continuous_snd).mem_nhds hτp] with y hy1 hy2
            exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_lt hy2)
          exact ((hBcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq hev).continuousWithinAt
        · -- the `τ = 0` join: the two branches agree there
          subst hτ0
          have hxV0 : (z, (0:ℝ)) ∈ Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ) := ⟨hz, by norm_num⟩
          have hAca : ContinuousAt (jetBranch g θ) (z, 0) :=
            hAcont.continuousAt (hVopen.mem_nhds hxV0)
          have hBca : ContinuousAt (baseBranch g θ) (z, 0) :=
            hBcont.continuousAt (hVopen.mem_nhds hxV0)
          have hAB : jetBranch g θ (z, 0) = baseBranch g θ (z, 0) :=
            jetBranch_eq_baseBranch_at_zero g θ z
          have hxe : extDeriv g θ (z, 0) = jetBranch g θ (z, 0) := by
            rw [extDeriv_of_pos_of_nonneg' g θ hz le_rfl]
            exact hAB.symm
          refine ContinuousAt.continuousWithinAt ?_
          rw [ContinuousAt, hxe, Metric.tendsto_nhds]
          intro ε hε
          have hAev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (jetBranch g θ y) (jetBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hAca) ε hε
          have hBev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ),
              dist (baseBranch g θ y) (baseBranch g θ (z, 0)) < ε :=
            (Metric.tendsto_nhds.mp hBca) ε hε
          have hVev : ∀ᶠ y in 𝓝 ((z, 0) : ℝ × ℝ), 0 < y.1 :=
            (isOpen_Ioi.preimage continuous_fst).mem_nhds hz
          filter_upwards [hAev, hBev, hVev] with y hyA hyB hy1
          by_cases hy : y.2 < 0
          · have hye : extDeriv g θ y = jetBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_neg' g θ hy1 hy
            rw [hye]
            exact hyA
          · have hye : extDeriv g θ y = baseBranch g θ y := by
              obtain ⟨y1, y2⟩ := y
              exact extDeriv_of_pos_of_nonneg' g θ hy1 (le_of_not_gt hy)
            rw [hye, hAB]
            exact hyB
  -- ## Assembly
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl]
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn).2 ?_
  refine ⟨?_, extDeriv g θ, ?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · exact contDiffOn_zero.mpr hcont
  · intro x hx
    exact (hderiv x hx).hasFDerivWithinAt

end Work.FTS.RegPkgGal.R1c
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4c.van_global =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R4c

set_option autoImplicit false

/-- **The gluing step of R4c.**  If `|g|` is dominated by `K·z²·Γ` on the whole half-line (the
output of the analytic core `van_zsq`) and by `Lz·Γ` in the far field `z ≥ Lz`, then `|g|` is
dominated by a single multiple of `Γ` everywhere: the case `z ≤ Lz` uses the `z²`-bound and
`z² ≤ Lz²`, the case `z > Lz` is the far-field bound.  The constant is
`max (K·Lz²) Lz`. -/
theorem van_global_of_zsq {α S Lz : ℝ} (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hzsq : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  refine ⟨max (K * Lz ^ 2) Lz, ?_, ?_⟩
  · exact le_trans (mul_nonneg hK (sq_nonneg Lz)) (le_max_left _ _)
  · intro τ hτ z θ hz hθ
    have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
    rcases le_or_gt z Lz with hzL | hzL
    · have h1 : |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := hzsq τ hτ z θ hz hθ
      have h2 : K * z ^ 2 ≤ K * Lz ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzL 2) hK
      calc |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := h1
        _ ≤ K * Lz ^ 2 * Work.FTS.Regularity.Gamma α θ := mul_le_mul_of_nonneg_right h2 hΓ0
        _ ≤ max (K * Lz ^ 2) Lz * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
    · have h1 : |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ :=
        hfar τ hτ z θ (le_of_lt hzL) hθ
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0)

theorem van_global {α S Cθ Lz : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ) (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨K, hK0, hzsq⟩ :=
    van_zsq (α := α) (S := S) (Cθ := Cθ) hα hS hCθ hsm hd hvt
  exact van_global_of_zsq hLz hK0 hzsq hfar

end Work.FTS.RegPkgGal.R4c
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L.L12fAux

/-- Monotonicity of `Work.FTS.Regularity.Jet` in its constant `N`.  (A local copy: the shared
one lives in `Work.FTS_RegExport.RXR5L.SG_C1Jet`, whose import cone is much larger than this
file needs.) -/
private theorem jet_mono {α S N N' : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) (hN : N ≤ N') : Work.FTS.Regularity.Jet α S N' h := by
  refine ⟨le_trans H.1 hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_nonneg (by positivity) α
    exact le_trans h1 (mul_le_mul_of_nonneg_right hN hd)

theorem C1Jet_L12f_of_support {α S N Kl Lf Nt : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0:ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∃ N' : ℝ, 0 ≤ N' ∧ Work.FTS.RegPkgGal.C1Jet α S N'
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z) := by
  -- The `Jet` half of the conclusion is the sibling `Der.jet_L12f`; it supplies a constant `N₀`.
  obtain ⟨N₀, hJet₀⟩ := Work.FTS.RegPkgGal.Der.jet_L12f hα hα1 hS hJ hlin hsupp htau
  -- The `z`-derivative half is the fundamental theorem of calculus at `a = 0`, with the density
  -- bound of `Der.L12fDensBound` (and `Der.L12fDensContInt` for the continuity requirements).
  have hCI := Work.FTS.RegPkgGal.Der.L12fDensContInt (α := α) (S := S) (N := N)
    (Kl := Kl) (Lf := Lf) hα hJ hlin hsupp
  have hBd := (Work.FTS.RegPkgGal.Der.L12fDensBound (α := α) (S := S) (N := N)
    (Kl := Kl) (Lf := Lf) hJ hlin hsupp).1
  refine ⟨max N₀ (6 * max Kl N), le_max_of_le_left hJet₀.1, ?_, ?_⟩
  · exact jet_mono hJet₀ (le_max_left _ _)
  · intro τ hτ θ hθ z hz
    refine ⟨-(Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) z), ?_, ?_⟩
    · exact Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K)
        (f := Work.FTS.Regularity.gSlice F τ) (a := 0) (ρ := z)
        (hCI τ hτ).2 (fun s hs => (hCI τ hτ).1.continuousAt (Ioi_mem_nhds hs)) hz
    · rw [abs_neg]
      exact le_trans (hBd τ hτ z hz) (le_max_right _ _)

end Work.FTS_RegExport.RXR5L.L12fAux
end
