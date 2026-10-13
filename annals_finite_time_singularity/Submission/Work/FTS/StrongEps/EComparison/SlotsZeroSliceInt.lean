import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real
open MeasureTheory Set Filter

/-!
# Integrability of the `cos θ`-weighted `θ`-slice of a straightened solution

The `Ω`-comparison layer needs the `z`-slices of the straightened solution `Φ` to be
`L²(Iθ, cos θ dθ)`-integrable: `∀ z > 0, IntegrableOn (fun θ => Φ z θ ^ 2 * cos θ) Iθ`
(the consumer is `Work.FTS.StrongEps.EComparison.HomClsSlotsZero` with `Φ = Uop α w`).

This is a consequence of the *slot* hypothesis `HkMem α 6 (Φ / sin 2θ)`, in the same way as
`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem`: the level-`0` integrand of `Φ / sin 2θ`
dominates `Φ² cos θ` up to the bounded multiplier `sin²(2·) cos · ≤ 1`, and `HkMem α 6` implies
`HkMem α 0` by the monotonicity of the `ℋ^k`-integrand (the quotient is again `C^∞` on the open
quadrant, where `sin 2θ ≠ 0`).

Concretely: on `Iθ` the identity `Φ² cos θ = (Φ / sin 2θ)² cos θ · sin²(2θ)` holds away from the
two points `{0, π/2}` (which is the null set where `sin (2·)` vanishes), and there
`sin²(2θ) ≤ 1` while `cos θ ≥ 0`.  So the assertion is an a.e.-comparison of two functions, the
dominating one being the `θ`-slice of the level-`0` slot, whose integrability is the content of
`HkMem α 0 (Φ / sin 2θ)`.
-/

theorem SlotsZeroSliceInt {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ)
    (h0 : ∀ z, Φ z 0 = 0)
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => Φ z θ ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
  intro z hz
  -- `Φ / sin 2θ` is `C^∞` on the open quadrant, so the level-`6` honesty descends to level `0`.
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Work.Construction.s2 θ) := by
    rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hsm n
    have hs : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hfun : Function.uncurry (fun z θ => Φ z θ / Work.Construction.s2 θ)
        = Function.uncurry Φ / fun p : ℝ × ℝ => Real.sin (2 * p.2) := by
      funext p
      obtain ⟨z, θ⟩ := p
      show Φ z θ / Work.Construction.s2 θ = Φ z θ / Real.sin (2 * θ)
      rw [Work.Construction.s2_eq]
    rw [hfun]
    exact h1.div hs hne
  have hF0 : Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Work.Construction.s2 θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 0 (Nat.zero_le 6) hHk
  -- The `cos θ`-weighted `L²`-slice of `Φ / sin 2θ` is integrable.
  have hint : Integrable (fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hF0 hz
  -- ## The zeros of `sin (2·)` inside `Iθ` are exactly the two endpoints
  have hmeas_zero : MeasurableSet {θ : ℝ | Work.Construction.s2 θ = 0} := by
    refine (measurableSet_singleton (0 : ℝ)).preimage ?_
    show Measurable fun θ : ℝ => Real.sin (2 * θ)
    exact Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Work.Construction.s2 θ = 0} = 0 := by
    have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Work.Construction.s2 θ = 0} ⊆
        ({0, Real.pi / 2} : Set ℝ) := by
      intro θ hθ
      obtain ⟨hθI, hθ0⟩ := hθ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨hne0, hnepi⟩ := hcon
      have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hne0)
      have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hnepi
      have hs0 : Real.sin (2 * θ) = 0 := by
        rw [← Work.Construction.s2_eq]; exact hθ0
      have h1 : 0 < 2 * θ := by linarith
      have h2 : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      have h3 := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [hs0] at h3
      exact lt_irrefl 0 h3
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  have hsin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Work.Construction.s2 θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ Work.Construction.s2 a ≠ 0}
        = {a : ℝ | Work.Construction.s2 a = 0} := by
      ext a; simp
    rw [hset, MeasureTheory.Measure.restrict_apply hmeas_zero]
    refine measure_mono_null ?_ hnull
    intro θ hθ
    exact ⟨hθ.2, hθ.1⟩
  -- ## The two functions agree a.e. on `Iθ`
  have hae : (fun θ => Φ z θ ^ 2 * Real.cos θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
        * Work.Construction.s2 θ ^ 2) := by
    filter_upwards [hsin] with θ hθ
    have h1 : (Φ z θ / Work.Construction.s2 θ) * Work.Construction.s2 θ = Φ z θ :=
      div_mul_cancel₀ _ hθ
    calc Φ z θ ^ 2 * Real.cos θ
        = (((Φ z θ / Work.Construction.s2 θ) * Work.Construction.s2 θ) ^ 2)
            * Real.cos θ := by rw [h1]
      _ = ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
            * Work.Construction.s2 θ ^ 2 := by ring
  -- ## Integrability of the a.e. equal function
  have hprod : Integrable (fun θ => ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
      * Work.Construction.s2 θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    have hcont : Continuous fun θ : ℝ => Work.Construction.s2 θ ^ 2 := by
      have hfun : (fun θ : ℝ => Work.Construction.s2 θ ^ 2)
          = fun θ : ℝ => Real.sin (2 * θ) ^ 2 := by
        funext θ; rw [Work.Construction.s2_eq]
      rw [hfun]
      exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2
    refine Integrable.mono' hint (hint.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hgnn : 0 ≤ (Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ :=
      mul_nonneg (sq_nonneg _) hc
    have hs2le : Work.Construction.s2 θ ^ 2 ≤ 1 := by
      rw [Work.Construction.s2_eq]
      exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)
    rw [norm_mul, Real.norm_of_nonneg hgnn]
    calc ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
            * ‖Work.Construction.s2 θ ^ 2‖
        ≤ ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hgnn
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hs2le
      _ = ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ) := mul_one _
  exact hprod.congr hae.symm

end Work.FTS.StrongEps.EComparison
