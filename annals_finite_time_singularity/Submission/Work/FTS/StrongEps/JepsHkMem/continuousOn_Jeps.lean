/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/JepsHkMem/continuousOn_Jeps.lean`

**Continuity of the log-coordinate mollifier `J_ε` on the open quadrant**, for a profile that is
only assumed *continuous* on `Quad`:

  `continuousOn_Jeps : ContinuousOn (fun q => J_ε g q.1 q.2) Quad`.

There is no smoothing hypothesis here: the statement is the `k = 0`-regularity that the
`JepsHkMem` chapter needs for the `ε`-scheme, and the only hypotheses on the kernel are those of
`IsMollKernel ρ` (continuous, supported in the closed unit ball, nonnegative, mass one).

## The argument

On the open quadrant, `J_ε g` is the `p`-integral

  `J_ε g z θ = ∫ p, Jker ρ ε p * g (z e^{-p₁}) (arctan (tan θ · e^{-p₂}))`   (`Jeps_eq_integral`),

and the *shift map* `Φ(x, p) = (x.1 · e^{-p.1}, arctan (tan x.2 · e^{-p.2}))` sends `Quad × ℝ²`
into `Quad` (the `z`-factor stays positive, and `arctan` of a positive number is an angle in
`(0, π/2)`).  Hence the integrand is jointly continuous on `Quad × ℝ²`, and dominated convergence
in the parameter `x` gives continuity.  Everything is local, so we work with a *compact* window
around the base point:

* `W := Icc (z₀/2) (2z₀) ×ˢ Icc (θ₀/2) ((θ₀+π/2)/2) ⊆ Quad` is compact, and the image of
  `W × closedBall 0 ε` under the (jointly continuous) shift map `Φ` is a compact subset of `Quad`,
  on which `g` is bounded by some `C`; this yields the *integrable* dominating function
  `p ↦ max C 0 · ‖Jker ρ ε p‖` for all `x` in the open window `V := Ioo (z₀/2) (2z₀) ×ˢ Ioo …`,
  which is a neighbourhood of the base point (within `Quad`);
* a.e. strong measurability follows from continuity of the integrand on the closed ball
  `closedBall 0 ε` (outside it the kernel vanishes);
* the pointwise a.e. continuity in `x` is the joint continuity of `Φ` and of `g`.

The `θ`-continuity of the shift uses `Real.continuousOn_tan` on `{cos ≠ 0}` (the window lies in
`(0, π/2)`), and the `z`-continuity is immediate.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

open Work.FTS.StrongEps

/-! ## Elementary facts about the shifts -/

/-- The shift of a base point of the quadrant lies again in the quadrant: this is the reason the
whole statement is true. -/
theorem shift_mem_Quad' {x p : ℝ × ℝ} (hx : x ∈ Quad) :
    (zShift x.1 p.1, thShift x.2 p.2) ∈ Quad :=
  ⟨zShift_pos hx.1, thShift_mem hx.2⟩

/-- For a fixed base point `x`, the shift is continuous in the shift variable `p`. -/
theorem continuousOn_shift_right' {x : ℝ × ℝ} (s : Set (ℝ × ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => (zShift x.1 p.1, thShift x.2 p.2)) s := by
  refine ContinuousOn.prodMk ?_ ?_
  · simp only [zShift]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => x.1 * Real.exp (-p.1)).continuousOn
  · simp only [thShift]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.arctan (Real.tan x.2 * Real.exp (-p.2))).continuousOn

/-- **A function vanishing off `s` is a.e. strongly measurable as soon as it is a.e. strongly
measurable on `s`.**  (`AEStronglyMeasurable f (μ.restrict s)` alone does not imply
`AEStronglyMeasurable f μ` — the values of `f` off `s` are uncontrolled — so the vanishing
hypothesis is used to glue the restriction by an indicator.) -/
theorem aestronglyMeasurable_of_eq_zero_off {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (h0 : ∀ x ∉ s, f x = 0)
    (hm : AEStronglyMeasurable f (volume.restrict s)) :
    AEStronglyMeasurable f volume := by
  refine ⟨s.indicator (hm.mk f), hm.stronglyMeasurable_mk.indicator hs, ?_⟩
  have h1 : ∀ᵐ x ∂volume, x ∈ s → f x = hm.mk f x := (ae_restrict_iff' hs).mp hm.ae_eq_mk
  filter_upwards [h1] with x hx
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]; exact hx hxs
  · rw [Set.indicator_of_notMem hxs, h0 x hxs]

/-! ## The `p`-integral form: continuity in the base point -/

/-- **Continuity of the `p`-integral form of `J_ε`** at a point of the open quadrant.

All the hypotheses on the profile are `ContinuousOn (uncurry g) Quad`; the compactness of the
support of `Jker ρ ε` (ball of radius `ε`) is what makes the domination argument work. -/
theorem cw_Jeps_integral {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) Quad)
    {z₀ θ₀ : ℝ} (hz₀ : 0 < z₀) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousWithinAt (fun x : ℝ × ℝ =>
      ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) Quad (z₀, θ₀) := by
  have hq₀ : (z₀, θ₀) ∈ Quad := mem_Quad.mpr ⟨hz₀, hθ₀⟩
  -- the windows around the base point
  have hz2 : (0 : ℝ) < z₀ / 2 := by linarith
  have h2z : (0 : ℝ) < 2 * z₀ := by linarith
  have hθ2 : (0 : ℝ) < θ₀ / 2 := by linarith [hθ₀.1]
  have hθhi : (θ₀ + π / 2) / 2 < π / 2 := by linarith [hθ₀.2, Real.pi_pos]
  have hθlo : θ₀ / 2 < (θ₀ + π / 2) / 2 := by linarith [hθ₀.2, Real.pi_pos]
  let A : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ × ℝ) ε
  let W : Set (ℝ × ℝ) := Set.Icc (z₀ / 2) (2 * z₀) ×ˢ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2)
  let V : Set (ℝ × ℝ) := Set.Ioo (z₀ / 2) (2 * z₀) ×ˢ Set.Ioo (θ₀ / 2) ((θ₀ + π / 2) / 2)
  have hVmem : (z₀, θ₀) ∈ V :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hθ₀.1], by linarith [hθ₀.2, Real.pi_pos]⟩⟩
  have hVnhds : V ∈ 𝓝[Quad] (z₀, θ₀) :=
    nhdsWithin_le_nhds (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo) hVmem)
  -- the shift map on the compact window is (jointly) continuous
  have hWcomp : IsCompact W := isCompact_Icc.prod isCompact_Icc
  have hAcomp : IsCompact A := isCompact_closedBall (0 : ℝ × ℝ) ε
  have hΦcont : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) (W ×ˢ A) := by
    refine ContinuousOn.prodMk ?_ ?_
    · simp only [zShift]
      exact (by fun_prop : Continuous fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
        y.1.1 * Real.exp (-y.2.1)).continuousOn
    · have htan : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan y.1.2) (W ×ˢ A) :=
        Real.continuousOn_tan.comp (continuous_fst.snd.continuousOn) (fun y hy => by
          have hy2 : y.1.2 ∈ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2) := hy.1.2
          have hmem : y.1.2 ∈ Set.Ioo 0 (π / 2) :=
            ⟨lt_of_lt_of_le hθ2 hy2.1, lt_of_le_of_lt hy2.2 hθhi⟩
          exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hmem.1, Real.pi_pos], hmem.2⟩).ne')
      have h1 : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
          Real.tan y.1.2 * Real.exp (-y.2.2)) (W ×ˢ A) :=
        htan.mul ((Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn)
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [thShift, Function.comp_def] using h2
  have himg_compact : IsCompact ((fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) '' (W ×ˢ A)) :=
    (hWcomp.prod hAcomp).image_of_continuousOn hΦcont
  have himg_sub : ((fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) '' (W ×ˢ A)) ⊆ Quad := by
    rintro q ⟨y, hy, rfl⟩
    exact ⟨zShift_pos (lt_of_lt_of_le hz2 hy.1.1.1),
      thShift_mem ⟨lt_of_lt_of_le hθ2 hy.1.2.1, lt_of_le_of_lt hy.1.2.2 hθhi⟩⟩
  -- the bound on the profile over the compact image
  obtain ⟨C, hC⟩ := himg_compact.exists_bound_of_continuousOn (hg.mono himg_sub)
  have hbound_int : Integrable (fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖) :=
    (Jker_integrable hρ hε).norm.const_mul (max C 0)
  -- a.e. strong measurability of the integrand
  have hmeas : ∀ᶠ x in 𝓝[Quad] (z₀, θ₀),
      AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) volume := by
    filter_upwards [hVnhds] with x hxV
    have hxQ : x ∈ Quad :=
      ⟨lt_trans hz2 hxV.1.1, ⟨lt_trans hθ2 hxV.2.1, lt_trans hxV.2.2 hθhi⟩⟩
    have hcontA : ContinuousOn (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) A :=
      (Jker_continuous hρ ε).continuousOn.mul
        (hg.comp (continuousOn_shift_right' A) (fun p _ => shift_mem_Quad' hxQ))
    refine aestronglyMeasurable_of_eq_zero_off measurableSet_closedBall (fun p hp => ?_)
      (hcontA.aestronglyMeasurable measurableSet_closedBall)
    show Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2) = 0
    rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]
  -- the domination, eventually in the base point
  have hbd : ∀ᶠ x in 𝓝[Quad] (z₀, θ₀), ∀ᵐ p ∂volume,
      ‖Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)‖ ≤ max C 0 * ‖Jker ρ ε p‖ := by
    filter_upwards [hVnhds] with x hxV
    refine Eventually.of_forall fun p => ?_
    by_cases hpA : p ∈ A
    · have hxW : x ∈ W := ⟨⟨le_of_lt hxV.1.1, le_of_lt hxV.1.2⟩,
        ⟨le_of_lt hxV.2.1, le_of_lt hxV.2.2⟩⟩
      have hb := hC (zShift x.1 p.1, thShift x.2 p.2) ⟨(x, p), ⟨hxW, hpA⟩, rfl⟩
      calc ‖Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)‖
          = ‖Jker ρ ε p‖ * ‖g (zShift x.1 p.1) (thShift x.2 p.2)‖ := norm_mul _ _
        _ ≤ ‖Jker ρ ε p‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ ‖Jker ρ ε p‖ * max C 0 := mul_le_mul_of_nonneg_left (le_max_left C 0) (norm_nonneg _)
        _ = max C 0 * ‖Jker ρ ε p‖ := mul_comm _ _
    · rw [show Jker ρ ε p = 0 from Jker_eq_zero_of_not_mem hρ hε hpA, zero_mul, norm_zero]
      simp
  -- pointwise (a.e. in `p`) continuity in the base point
  have hpt : ∀ᵐ p ∂volume, ContinuousWithinAt (fun x : ℝ × ℝ =>
      Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) Quad (z₀, θ₀) := by
    refine Eventually.of_forall fun p => ?_
    refine ContinuousWithinAt.const_mul ?_ (Jker ρ ε p)
    have hψon : ContinuousOn (fun x : ℝ × ℝ => (zShift x.1 p.1, thShift x.2 p.2)) Quad := by
      refine ContinuousOn.prodMk ?_ ?_
      · simp only [zShift]
        fun_prop
      · have htan : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.2) Quad :=
          Real.continuousOn_tan.comp continuous_snd.continuousOn (fun x hx => by
            obtain ⟨-, hx2⟩ := hx
            exact (Real.cos_pos_of_mem_Ioo
              ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩).ne')
        have h1 : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.2 * Real.exp (-p.2)) Quad :=
          htan.mul_const _
        have h2 := Real.continuous_arctan.comp_continuousOn h1
        simpa only [thShift, Function.comp_def] using h2
    exact (hg.comp hψon (fun x hx => shift_mem_Quad' hx)).continuousWithinAt hq₀
  exact MeasureTheory.continuousWithinAt_of_dominated
    (F := fun (x : ℝ × ℝ) (p : ℝ × ℝ) =>
      Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2))
    (x₀ := (z₀, θ₀)) (s := Quad) (bound := fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖)
    hmeas hbd hbound_int hpt

/-! ## The statement -/

theorem continuousOn_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) Work.FTS.StrongEps.Quad := by
  rintro ⟨z₀, θ₀⟩ hq₀
  have hz₀ : 0 < z₀ := hq₀.1
  have hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2) := hq₀.2
  have hmain := cw_Jeps_integral hρ hε hg hz₀ hθ₀
  have hev : (fun x : ℝ × ℝ => Jeps ρ ε g x.1 x.2) =ᶠ[𝓝[Quad] (z₀, θ₀)]
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact Jeps_eq_integral ρ ε g hx.1 hx.2
  exact hmain.congr_of_eventuallyEq hev (Jeps_eq_integral ρ ε g hz₀ hθ₀)

end Work.FTS.StrongEps.JepsHkMem
