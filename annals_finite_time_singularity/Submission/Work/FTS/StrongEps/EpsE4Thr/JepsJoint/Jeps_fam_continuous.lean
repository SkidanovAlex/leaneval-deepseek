/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Jeps_fam_continuous` — joint continuity of `(τ, z, θ) ↦ J_ε (g · τ) z θ`

The `ε`-scheme of the StrongEps area integrates *families* `g : ℝ → ℝ → ℝ → ℝ` whose slices are
mollified: the object that occurs in the ODE is

  `(τ, z, θ) ↦ J_ε (fun z' θ' => g z' θ' τ) z θ`      (`Jeps ρ ε (slice g τ) z θ`).

This file proves that this map is continuous on `Icc 0 T ×ˢ Quad` as soon as the *unmollified*
family `(z, θ, τ) ↦ g z θ τ` is continuous there — no regularity of `g` beyond continuity, and no
smoothness of the kernel `ρ` beyond `IsMollKernel ρ` (continuous, supported in the closed unit
ball, nonnegative, mass one).

## The argument

On the open quadrant (`Quad ⊆` the domain of the integral representation), `J_ε` is the `p`-integral

  `J_ε f z θ = ∫ p, Jker ρ ε p * f (z e^{-p₁}) (arctan (tan θ · e^{-p₂}))`     (`Jeps_eq_integral`),

so it suffices to prove the continuity of the parametric integral

  `(τ, z, θ) ↦ ∫ p, Jker ρ ε p * g (z e^{-p₁}) (arctan (tan θ e^{-p₂})) τ`.

Every point of `Icc 0 T ×ˢ Quad` has `z > 0` and `θ ∈ (0, π/2)`, so the shifts

  `Φ(τ, z, θ, p) = (τ, (z e^{-p₁}, arctan (tan θ e^{-p₂})))`

map `(Icc 0 T ×ˢ W) ×ˢ closedBall 0 ε` *into* `Icc 0 T ×ˢ Quad`, where

  `W = Icc (z₀/2) (2z₀) ×ˢ Icc (θ₀/2) ((θ₀ + π/2)/2)`

is a compact window around the base point.  Hence `Φ` maps that (compact) set onto a compact
subset of `Icc 0 T ×ˢ Quad`, on which `g` is bounded by some `C`; this yields the domination

  `‖Jker ρ ε p * g (…) τ‖ ≤ max C 0 * ‖Jker ρ ε p‖`   for `(τ, z, θ)` in the open window and all `p`,

with an integrable right hand side (`Jker ρ ε` is integrable because it is continuous with compact
support).  A.e. strong measurability of the integrand follows from its continuity on the compact
ball and the *vanishing* of `Jker ρ ε` off it; the pointwise a.e. continuity in the parameter is
the joint continuity of the shift and of `g`.  `continuousWithinAt_of_dominated` then concludes.

The `θ`-continuity of the shift uses `Real.continuousOn_tan` on `{cos ≠ 0}`: the window lies inside
`(0, π/2)`, where `cos ≠ 0`.

## Contents

* `continuousOn_thShift_proj` — continuity of the `θ`-shift in the base point, jointly with τ;
* `cw_Jeps_fam_integral` — `ContinuousWithinAt` of the parametric integral;
* `Jeps_fam_continuous` — the requested statement.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

open Work.FTS.StrongEps.JepsHkMem (aestronglyMeasurable_of_eq_zero_off shift_mem_Quad')

set_option maxHeartbeats 1000000

/-! ## A continuity fact for the `θ`-shift -/

/-- **The `θ`-shift is continuous in the base point, jointly with the second variable.**  On
`Icc 0 T ×ˢ Quad` the angle `y.2.2` lies in `(0, π/2)`, so `cos y.2.2 ≠ 0` and
`Real.continuousOn_tan` applies. -/
theorem continuousOn_thShift_proj {T : ℝ} {p : ℝ × ℝ} :
    ContinuousOn (fun y : ℝ × ℝ × ℝ => thShift y.2.2 p.2) (Set.Icc (0 : ℝ) T ×ˢ Quad) := by
  have htan : ContinuousOn (fun y : ℝ × ℝ × ℝ => Real.tan y.2.2) (Set.Icc (0 : ℝ) T ×ˢ Quad) :=
    Real.continuousOn_tan.comp
      ((continuous_snd.snd : Continuous (fun y : ℝ × ℝ × ℝ => y.2.2)).continuousOn)
      (fun y hy => by
        obtain ⟨-, hy2⟩ := hy
        exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy2.2.1, Real.pi_pos], hy2.2.2⟩).ne')
  have h1 : ContinuousOn (fun y : ℝ × ℝ × ℝ => Real.tan y.2.2 * Real.exp (-p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Quad) := htan.mul_const _
  simpa only [thShift, Function.comp_def] using Real.continuous_arctan.comp_continuousOn h1

/-! ## Continuity of the parametric integral at an interior point -/

/-- **Continuity at a point of the parametric `p`-integral form of `J_ε`.**  This is the local
(dominated convergence) step: it is stated at a single base point `(τ₀, z₀, θ₀)` with
`τ₀ ∈ Icc 0 T`, `z₀ > 0`, `θ₀ ∈ (0, π/2)`, exactly as far as `continuousWithinAt_of_dominated`
needs — a *global* domination on `Icc 0 T ×ˢ Quad` is impossible because `z` is unbounded there. -/
theorem cw_Jeps_fam_integral {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε T : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun q : ℝ × ℝ × ℝ => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Quad))
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) T) {z₀ θ₀ : ℝ} (hz₀ : 0 < z₀)
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousWithinAt (fun y : ℝ × ℝ × ℝ =>
      ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1)
      (Set.Icc (0 : ℝ) T ×ˢ Quad) (τ₀, z₀, θ₀) := by
  have hq₀ : (z₀, θ₀) ∈ Quad := ⟨hz₀, hθ₀⟩
  have hy₀ : (τ₀, z₀, θ₀) ∈ Set.Icc (0 : ℝ) T ×ˢ Quad := ⟨hτ₀, hq₀⟩
  have hz2 : (0 : ℝ) < z₀ / 2 := by linarith
  have hθ2 : (0 : ℝ) < θ₀ / 2 := by linarith [hθ₀.1]
  have hθhi : (θ₀ + π / 2) / 2 < π / 2 := by linarith [hθ₀.2, Real.pi_pos]
  let A : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ × ℝ) ε
  let W : Set (ℝ × ℝ) := Set.Icc (z₀ / 2) (2 * z₀) ×ˢ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2)
  let V : Set (ℝ × ℝ) := Set.Ioo (z₀ / 2) (2 * z₀) ×ˢ Set.Ioo (θ₀ / 2) ((θ₀ + π / 2) / 2)
  have hVmem : (z₀, θ₀) ∈ V :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hθ₀.1], by linarith [hθ₀.2, Real.pi_pos]⟩⟩
  have hVnhds : V ∈ 𝓝[Quad] (z₀, θ₀) :=
    nhdsWithin_le_nhds (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo) hVmem)
  have hNhd : Set.Icc (0 : ℝ) T ×ˢ V ∈ 𝓝[Set.Icc (0 : ℝ) T ×ˢ Quad] (τ₀, z₀, θ₀) := by
    rw [nhdsWithin_prod_eq]
    exact prod_mem_prod self_mem_nhdsWithin hVnhds
  let Φ : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ × ℝ :=
    fun y => (y.1.1, (zShift y.1.2.1 y.2.1, thShift y.1.2.2 y.2.2))
  have hKc : IsCompact ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A) := by
    have hW : IsCompact (Set.Icc (z₀ / 2) (2 * z₀) ×ˢ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2)) :=
      isCompact_Icc.prod isCompact_Icc
    have h : IsCompact ((Set.Icc (0 : ℝ) T ×ˢ (Set.Icc (z₀ / 2) (2 * z₀) ×ˢ
        Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2))) ×ˢ Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (isCompact_Icc.prod hW).prod (isCompact_closedBall (0 : ℝ × ℝ) ε)
    simpa only [A, W] using h
  have hΦcont : ContinuousOn Φ ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A) := by
    show ContinuousOn (fun y : (ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
      (y.1.1, (zShift y.1.2.1 y.2.1, thShift y.1.2.2 y.2.2))) _
    refine ContinuousOn.prodMk (continuous_fst.fst).continuousOn ?_
    refine ContinuousOn.prodMk ?_ ?_
    · exact (continuous_fst.snd.fst.mul
        (Real.continuous_exp.comp (continuous_neg.comp continuous_snd.fst))).continuousOn
    · have htan : ContinuousOn (fun y : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => Real.tan y.1.2.2)
          ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A) :=
        Real.continuousOn_tan.comp continuous_fst.snd.snd.continuousOn (fun y hy => by
          have h2 : y.1.2.2 ∈ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2) := hy.1.2.2
          exact (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [lt_of_lt_of_le hθ2 h2.1, Real.pi_pos], lt_of_le_of_lt h2.2 hθhi⟩).ne')
      have h1 : ContinuousOn (fun y : (ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
          Real.tan y.1.2.2 * Real.exp (-y.2.2)) ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A) :=
        htan.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn
      simpa only [thShift, Function.comp_def] using Real.continuous_arctan.comp_continuousOn h1
  have himg : IsCompact (Φ '' ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A)) :=
    hKc.image_of_continuousOn hΦcont
  have himg_sub : Φ '' ((Set.Icc (0 : ℝ) T ×ˢ W) ×ˢ A) ⊆ Set.Icc (0 : ℝ) T ×ˢ Quad := by
    rintro q ⟨y, hy, rfl⟩
    show ((y.1.1, (zShift y.1.2.1 y.2.1, thShift y.1.2.2 y.2.2)) : ℝ × ℝ × ℝ) ∈
      Set.Icc (0 : ℝ) T ×ˢ Quad
    exact ⟨hy.1.1, zShift_pos (lt_of_lt_of_le hz2 hy.1.2.1.1),
      thShift_mem ⟨lt_of_lt_of_le hθ2 hy.1.2.2.1, lt_of_le_of_lt hy.1.2.2.2 hθhi⟩⟩
  obtain ⟨C, hC⟩ := himg.exists_bound_of_continuousOn (hg.mono himg_sub)
  have hbound_int : Integrable (fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖) :=
    (Jker_integrable hρ hε).norm.const_mul (max C 0)
  have hmeas : ∀ᶠ y in 𝓝[Set.Icc (0 : ℝ) T ×ˢ Quad] (τ₀, z₀, θ₀),
      AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1) volume := by
    filter_upwards [hNhd] with y hyV
    have hyQ : y.2 ∈ Quad :=
      ⟨lt_trans hz2 hyV.2.1.1, ⟨lt_trans hθ2 hyV.2.2.1, lt_trans hyV.2.2.2 hθhi⟩⟩
    have hcontA : ContinuousOn (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1) A := by
      refine (Jker_continuous hρ ε).continuousOn.mul ?_
      refine hg.comp (f := fun p : ℝ × ℝ =>
        (y.1, (zShift y.2.1 p.1, thShift y.2.2 p.2))) ?_ ?_
      · exact (Continuous.prodMk continuous_const
          (Continuous.prodMk (continuous_const.mul
            (Real.continuous_exp.comp (continuous_neg.comp continuous_fst)))
            (Real.continuous_arctan.comp (continuous_const.mul
              (Real.continuous_exp.comp (continuous_neg.comp continuous_snd)))))).continuousOn
      · intro p hp
        exact ⟨hyV.1, shift_mem_Quad' hyQ⟩
    refine aestronglyMeasurable_of_eq_zero_off measurableSet_closedBall (fun p hp => ?_)
      (hcontA.aestronglyMeasurable measurableSet_closedBall)
    show Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1 = 0
    rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]
  have hbd : ∀ᶠ y in 𝓝[Set.Icc (0 : ℝ) T ×ˢ Quad] (τ₀, z₀, θ₀), ∀ᵐ p ∂volume,
      ‖Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1‖
        ≤ max C 0 * ‖Jker ρ ε p‖ := by
    filter_upwards [hNhd] with y hyV
    refine Eventually.of_forall fun p => ?_
    by_cases hpA : p ∈ A
    · have hyW : y ∈ Set.Icc (0 : ℝ) T ×ˢ W :=
        ⟨hyV.1, ⟨⟨le_of_lt hyV.2.1.1, le_of_lt hyV.2.1.2⟩,
          ⟨le_of_lt hyV.2.2.1, le_of_lt hyV.2.2.2⟩⟩⟩
      have hb := hC (Φ (y, p)) ⟨(y, p), ⟨hyW, hpA⟩, rfl⟩
      calc ‖Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1‖
          = ‖Jker ρ ε p‖ * ‖g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1‖ := norm_mul _ _
        _ ≤ ‖Jker ρ ε p‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ ‖Jker ρ ε p‖ * max C 0 := mul_le_mul_of_nonneg_left (le_max_left C 0) (norm_nonneg _)
        _ = max C 0 * ‖Jker ρ ε p‖ := mul_comm _ _
    · rw [show Jker ρ ε p = 0 from Jker_eq_zero_of_not_mem hρ hε hpA]
      simp
  have hpt : ∀ᵐ p ∂volume, ContinuousWithinAt (fun y : ℝ × ℝ × ℝ =>
      Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1)
      (Set.Icc (0 : ℝ) T ×ˢ Quad) (τ₀, z₀, θ₀) := by
    refine Eventually.of_forall fun p => ?_
    refine ContinuousWithinAt.const_mul ?_ (Jker ρ ε p)
    refine (hg.comp (f := fun y : ℝ × ℝ × ℝ =>
      (y.1, (zShift y.2.1 p.1, thShift y.2.2 p.2))) ?_ ?_).continuousWithinAt hy₀
    · have h1 : ContinuousOn (fun y : ℝ × ℝ × ℝ => y.1) (Set.Icc (0 : ℝ) T ×ˢ Quad) :=
        (continuous_fst : Continuous (fun y : ℝ × ℝ × ℝ => y.1)).continuousOn
      have h2 : ContinuousOn (fun y : ℝ × ℝ × ℝ => zShift y.2.1 p.1)
          (Set.Icc (0 : ℝ) T ×ˢ Quad) := by
        simp only [zShift]
        exact (continuous_snd.fst.mul continuous_const).continuousOn
      exact h1.prodMk (h2.prodMk continuousOn_thShift_proj)
    · intro y hy
      exact ⟨hy.1, shift_mem_Quad' hy.2⟩
  exact continuousWithinAt_of_dominated
    (F := fun (y : ℝ × ℝ × ℝ) (p : ℝ × ℝ) =>
      Jker ρ ε p * g (zShift y.2.1 p.1) (thShift y.2.2 p.2) y.1)
    (x₀ := (τ₀, z₀, θ₀)) (s := Set.Icc (0 : ℝ) T ×ˢ Quad)
    (bound := fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖) hmeas hbd hbound_int hpt

/-! ## The requested statement -/

theorem Jeps_fam_continuous {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε T : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jeps ρ ε
      (fun z θ => g z θ q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  intro q hq
  have hmain := cw_Jeps_fam_integral hρ hε hg hq.1 hq.2.1 hq.2.2
  refine hmain.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    exact Jeps_eq_integral ρ ε (fun z θ => g z θ y.1) hy.2.1 hy.2.2
  · exact Jeps_eq_integral ρ ε (fun z θ => g z θ q.1) hq.2.1 hq.2.2

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
