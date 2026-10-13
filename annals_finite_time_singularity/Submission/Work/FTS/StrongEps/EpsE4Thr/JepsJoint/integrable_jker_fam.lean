/-
Copyright: work module for the Elgindi finite-time singularity project.

# `integrable_jker_fam` — integrability of the shifted kernel family

The `ε`-scheme of the `StrongEps` area integrates quantities of the shape

  `p ↦ Jker ρ ε p · U (zShift r p.1) (thShift θ' p.2) s`,

where `U` is the (jointly continuous, on the slab `[0,T] × Quad`) integrand of an energy /
`L₁₂`-functional and the two shifts transport the *base point* `(r, θ') ∈ Quad` of the mollifier.
The point of the lemma is that the kernel `Jker ρ ε` is supported in the *compact* ball of radius
`ε` (`Jker_ne_zero_support`), so the shift map

  `Φ(p) = (s, (r·e^{-p₁}, arctan(tan θ'·e^{-p₂})))`

sends that ball into a *compact* subset of the slab `Icc 0 T ×ˢ Quad` — the `z`-coordinate stays
in `[r e^{-ε}, r e^{ε}]` and the `θ`-coordinate in `[arctan(tan θ' e^{-ε}), arctan(tan θ' e^{ε})]`,
both compactly inside `(0, ∞)` resp. `(0, π/2)` because `r > 0` and `θ' ∈ (0, π/2)`.  On that
compact image `U` is bounded by some `C`, giving the domination

  `‖Jker ρ ε p · U (…)‖ ≤ max C 0 · ‖Jker ρ ε p‖`,

and `‖Jker ρ ε‖` is integrable (`Jker_integrable`: continuous with compact support).  A.e. strong
measurability of the product follows from its vanishing off the ball, where it is continuous.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

open Work.FTS.StrongEps
open Work.FTS.StrongEps.JepsHkMem (aestronglyMeasurable_of_eq_zero_off
  continuousOn_shift_right' shift_mem_Quad')

set_option autoImplicit false

theorem integrable_jker_fam {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε T : ℝ} (hε : 0 < ε) {U : ℝ → ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => U q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ∀ r θ' : ℝ, 0 < r → θ' ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc (0 : ℝ) T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * U (Work.FTS.StrongEps.zShift r p.1) (Work.FTS.StrongEps.thShift θ' p.2) s)
        MeasureTheory.volume := by
  intro r θ' hr hθ' s hs
  -- The shift map, from the plane into the slab.
  set Φ : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun p => (s, (zShift r p.1, thShift θ' p.2)) with hΦ
  have hrθ : (r, θ') ∈ Quad := ⟨hr, hθ'⟩
  have hΦmaps : MapsTo Φ (Metric.closedBall (0 : ℝ × ℝ) ε) (Set.Icc (0 : ℝ) T ×ˢ Quad) :=
    fun p _ => ⟨hs, shift_mem_Quad' hrθ⟩
  have hΦcont : ContinuousOn Φ (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (s, (zShift r p.1, thShift θ' p.2)))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      ContinuousOn.prodMk
        ((continuous_const : Continuous (fun _ : ℝ × ℝ => s)).continuousOn)
        (continuousOn_shift_right' (x := (r, θ')) (Metric.closedBall (0 : ℝ × ℝ) ε))
    simpa only [hΦ] using h1
  -- The compact image carries a bound for `U`.
  have himg : IsCompact (Φ '' Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (isCompact_closedBall (0 : ℝ × ℝ) ε).image_of_continuousOn hΦcont
  have himg_sub : Φ '' Metric.closedBall (0 : ℝ × ℝ) ε ⊆ Set.Icc (0 : ℝ) T ×ˢ Quad := by
    rintro q ⟨p, hp, rfl⟩
    exact hΦmaps hp
  obtain ⟨C, hC⟩ := himg.exists_bound_of_continuousOn (hcont.mono himg_sub)
  -- A.e. strong measurability: the product vanishes off the ball and is continuous on it.
  have hcontBall : ContinuousOn (fun p : ℝ × ℝ =>
      Jker ρ ε p * U (zShift r p.1) (thShift θ' p.2) s) (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    refine (Jker_continuous hρ ε).continuousOn.mul ?_
    have h := hcont.comp hΦcont hΦmaps
    simpa only [hΦ, Function.comp_def] using h
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Jker ρ ε p * U (zShift r p.1) (thShift θ' p.2) s) volume :=
    aestronglyMeasurable_of_eq_zero_off measurableSet_closedBall
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
      (hcontBall.aestronglyMeasurable measurableSet_closedBall)
  -- Domination by `C · ‖Jker ρ ε‖`.
  refine MeasureTheory.Integrable.mono' ((Jker_integrable hρ hε).norm.const_mul (max C 0))
    hmeas (Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
  · have hb := hC (Φ p) ⟨p, hp, rfl⟩
    simp only [hΦ] at hb
    rw [norm_mul, Real.norm_eq_abs]
    calc ‖Jker ρ ε p‖ * |U (zShift r p.1) (thShift θ' p.2) s|
        ≤ ‖Jker ρ ε p‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ ‖Jker ρ ε p‖ * max C 0 :=
          mul_le_mul_of_nonneg_left (le_max_left C 0) (norm_nonneg _)
      _ = max C 0 * ‖Jker ρ ε p‖ := by ring
  · rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul, norm_zero]
    exact mul_nonneg (le_max_right C 0) le_rfl

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
