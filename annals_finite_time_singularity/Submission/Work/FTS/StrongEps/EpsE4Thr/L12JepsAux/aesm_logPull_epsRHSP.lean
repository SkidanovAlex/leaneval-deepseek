/-
Copyright: work module for the Elgindi finite-time singularity project.

# `aesm_logPull_epsRHSP`

`logPull (epsRHSP α ρ ε Φs E g τ)` is a.e. strongly measurable.

The point is that the log-coordinate pull-back is *linear* in the profile and that
`epsRHSP α ρ ε Φs E g τ` is, by the scheme `IsEpsSolP`, the `τ`-derivative of the slice
`g (·,·,·)`.  Consequently, on the whole plane `ℝ²`,

  `logPull (epsRHSP … τ) x = lim_n (logPull (slice g (sq n)) x - logPull (slice g τ) x) / (sq n - τ)`

along any sequence `sq n → τ` inside `[0,T]` with `sq n ≠ τ` (`τ ∈ (0,T)` is an interior point of
`[0,T]`, so the *within*-derivative of the scheme is an honest derivative).  Each difference quotient
is `AEStronglyMeasurable` by the hypothesis `hslice` (the two times `sq n` and `τ` both lie in
`[0,T]`), and `aestronglyMeasurable_of_tendsto_ae` concludes.  No measurability of `ρ` is needed.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

theorem aesm_logPull_epsRHSP {ρ : ℝ × ℝ → ℝ} {α T ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hslice : ∀ s ∈ Set.Icc 0 T,
      MeasureTheory.AEStronglyMeasurable (Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g s))
        MeasureTheory.volume)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    MeasureTheory.AEStronglyMeasurable
      (Work.FTS.StrongEps.logPull (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ))
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
  -- each difference quotient is a.e. strongly measurable
  have hGasm : ∀ n : ℕ, AEStronglyMeasurable (fun x : ℝ × ℝ =>
      (Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g (sq n)) x
        - Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g τ) x) / (sq n - τ))
      MeasureTheory.volume := by
    intro n
    have h1 : AEStronglyMeasurable (Work.FTS.StrongEps.logPull
        (Work.FTS.Galerkin.slice g (sq n))) MeasureTheory.volume := hslice (sq n) (hsmem n)
    have h2 : AEStronglyMeasurable (Work.FTS.StrongEps.logPull
        (Work.FTS.Galerkin.slice g τ)) MeasureTheory.volume := hslice τ ⟨hτ0.le, hτT.le⟩
    have h3 : AEStronglyMeasurable (fun x : ℝ × ℝ =>
        (Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g (sq n)) x
          - Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g τ) x) * (sq n - τ)⁻¹)
        MeasureTheory.volume := (h1.sub h2).mul_const _
    simpa only [div_eq_mul_inv] using h3
  -- pointwise convergence to the derivative of the slice, i.e. to `logPull (epsRHSP …)`
  have hlim : ∀ᵐ x ∂MeasureTheory.volume, Tendsto (fun n : ℕ =>
      (Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g (sq n)) x
        - Work.FTS.StrongEps.logPull (Work.FTS.Galerkin.slice g τ) x) / (sq n - τ))
      atTop (𝓝 (Work.FTS.StrongEps.logPull
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) x)) := by
    refine Eventually.of_forall fun x => ?_
    have hz : 0 < Real.exp x.1 := Real.exp_pos x.1
    have hθ : Real.arctan (Real.exp x.2) ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨(Real.arctan_pos).2 (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩
    have hder : HasDerivAt (fun s : ℝ => g (Real.exp x.1) (Real.arctan (Real.exp x.2)) s)
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
          (Real.exp x.1) (Real.arctan (Real.exp x.2))) τ :=
      (hsol.2 (Real.exp x.1) (Real.arctan (Real.exp x.2)) τ hz hθ
        ⟨hτ0.le, hτT.le⟩).hasDerivAt (Icc_mem_nhds hτ0 hτT)
    have h1 : Tendsto (fun n : ℕ =>
        slope (fun s : ℝ => g (Real.exp x.1) (Real.arctan (Real.exp x.2)) s) τ (sq n))
        atTop (𝓝 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
          (Real.exp x.1) (Real.arctan (Real.exp x.2)))) :=
      (hder.tendsto_slope).comp hseq
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) h1
    rw [slope_def_field]
    simp only [Work.FTS.StrongEps.logPull, Work.FTS.Galerkin.slice]
  exact aestronglyMeasurable_of_tendsto_ae atTop hGasm hlim

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
