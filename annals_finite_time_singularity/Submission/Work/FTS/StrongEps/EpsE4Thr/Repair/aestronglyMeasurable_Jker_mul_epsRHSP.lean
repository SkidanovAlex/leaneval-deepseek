/-
Copyright: work module for the Elgindi finite-time singularity project.

# `aestronglyMeasurable_Jker_mul_epsRHSP`

The dominated-convergence obligation of `hasDerivWithinAt_Jeps_slice_repair`: the integrand
`p ↦ J_ε(p) · epsRHSP … g τ (z + p, θ + p)` of the `τ`-derivative is a.e. strongly measurable.

Note that **no measurability of `ρ` is assumed**, and none is proved: the argument is that the
derivative `epsRHSP α ρ ε Φs E g τ` of the slice at the *shifted* point is the pointwise limit
of the difference quotients at times `τ + δ/(n+1)`, and each difference quotient is a constant
multiple of a difference of two functions whose `Jker`-multiple is integrable by `hint`.  So
`AEStronglyMeasurable` of the integrand follows from `AEStronglyMeasurable` of the limit of a
sequence of a.e. strongly measurable functions (`aestronglyMeasurable_of_tendsto_ae`) — the wild
factor `Jker ρ ε` is pulled along through the whole computation and never needs a measurability
lemma of its own.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsE4Thr.Repair

theorem aestronglyMeasurable_Jker_mul_epsRHSP
    {ρ : ℝ × ℝ → ℝ} {α T ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hτ : τ ∈ Set.Ioo 0 T)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hint : ∀ s ∈ Set.Icc 0 T, MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p *
        (Work.FTS.Galerkin.slice g s) (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      MeasureTheory.volume := by
  have hτ0 : 0 < τ := hτ.1
  have hτT : τ < T := hτ.2
  have hTτ : 0 < T - τ := by linarith
  -- the sequence of times along which we differentiate, approaching `τ` from the interior
  set sq : ℕ → ℝ := fun n => τ + ((T - τ) / 2) / ((n : ℝ) + 1) with hsq
  have hspos : ∀ n : ℕ, 0 < sq n - τ := by
    intro n
    have hpos : 0 < ((T - τ) / 2) / ((n : ℝ) + 1) := by positivity
    simp only [hsq]
    linarith
  have hsmem : ∀ n : ℕ, sq n ∈ Set.Icc 0 T := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hle : ((T - τ) / 2) / ((n : ℝ) + 1) ≤ (T - τ) / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hTτ, hn1]
    have h1 : 0 ≤ sq n := by have := hspos n; linarith
    have h2 : sq n ≤ T := by simp only [hsq]; linarith
    exact ⟨h1, h2⟩
  have hstend : Tendsto sq atTop (𝓝 τ) := by
    have hc : Tendsto (fun n : ℕ => ((T - τ) / 2) / ((n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_div_atTop_nhds_zero_nat ((T - τ) / 2)
    have hcomp : Tendsto (fun n : ℕ => ((T - τ) / 2) / (((n + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) :=
      hc.comp (tendsto_add_atTop_nat 1)
    have hcomp' : Tendsto (fun n : ℕ => ((T - τ) / 2) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      Tendsto.congr' (Eventually.of_forall fun n => by push_cast; ring) hcomp
    have := hcomp'.const_add τ
    simpa only [hsq, add_zero] using this
  have hseq : Tendsto sq atTop (𝓝[≠] τ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sq hstend ?_
    refine Eventually.of_forall fun n => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mp (hspos n).ne'
  -- the derivative of the slice at the *shifted* point, at time `τ`
  have hder : ∀ p : ℝ × ℝ, HasDerivAt
      (fun t : ℝ => g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) t)
      (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      τ := by
    intro p
    exact (hsol.2 (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) τ
      (Work.FTS.StrongEps.zShift_pos hz) (Work.FTS.StrongEps.thShift_mem hθ)
      ⟨hτ0.le, hτT.le⟩).hasDerivAt (Icc_mem_nhds hτ0 hτT)
  have hlim : ∀ p : ℝ × ℝ, Tendsto (fun n : ℕ =>
      (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) (sq n)
        - g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) τ) / (sq n - τ))
      atTop (𝓝 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    intro p
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) ((hder p).tendsto_slope.comp hseq)
    exact slope_def_field _ _ _
  -- the difference quotients of the integrand
  set F : ℕ → ℝ × ℝ → ℝ := fun n p =>
      (sq n - τ)⁻¹ * (Work.FTS.StrongEps.Jker ρ ε p *
          (Work.FTS.Galerkin.slice g (sq n)) (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
        - Work.FTS.StrongEps.Jker ρ ε p * (Work.FTS.Galerkin.slice g τ)
            (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) with hF
  have hFasm : ∀ n : ℕ, AEStronglyMeasurable (F n) MeasureTheory.volume := by
    intro n
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (Work.FTS.Galerkin.slice g (sq n)) (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume :=
      (hint (sq n) (hsmem n)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (Work.FTS.Galerkin.slice g τ) (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume :=
      (hint τ ⟨hτ0.le, hτT.le⟩).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.FTS.StrongEps.Jker ρ ε p * (Work.FTS.Galerkin.slice g (sq n))
            (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        - Work.FTS.StrongEps.Jker ρ ε p * (Work.FTS.Galerkin.slice g τ)
            (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
        MeasureTheory.volume :=
      h1.sub h2
    have h4 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (sq n - τ)⁻¹ * (Work.FTS.StrongEps.Jker ρ ε p *
            (Work.FTS.Galerkin.slice g (sq n)) (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
          - Work.FTS.StrongEps.Jker ρ ε p * (Work.FTS.Galerkin.slice g τ)
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
        MeasureTheory.volume :=
      h3.const_mul _
    rw [hF]
    exact h4
  have hFlim : ∀ᵐ p ∂MeasureTheory.volume, Tendsto (fun n : ℕ => F n p) atTop
      (𝓝 (Work.FTS.StrongEps.Jker ρ ε p * Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    refine Eventually.of_forall fun p => ?_
    have hc : Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jker ρ ε p *
        ((g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) (sq n)
          - g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) τ) / (sq n - τ)))
        atTop
        (𝓝 (Work.FTS.StrongEps.Jker ρ ε p * Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) :=
      (hlim p).const_mul _
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hc
    simp only [hF, hsq, Work.FTS.Galerkin.slice]
    ring
  exact aestronglyMeasurable_of_tendsto_ae atTop hFasm hFlim

end Work.FTS.StrongEps.EpsE4Thr.Repair
