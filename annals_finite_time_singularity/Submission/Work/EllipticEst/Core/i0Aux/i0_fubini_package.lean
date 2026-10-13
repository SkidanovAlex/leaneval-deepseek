/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Fubini package behind the `i₀` elliptic estimate

The `i₀` (level-`0`) elliptic estimate of the project integrates the angular energy of a
radial slice against the weight `sin(2θ)^{-η}`, and it needs to know that

* the angular weight `thEta` times the radial `L²`-slice is integrable on a *compact* set
  `(δ/4, δ)` of angles (so that the angular energy is finite for a.e. angle), and that

* the two iterated integrals of `w(z)² g(z,θ)² sin(2θ)^{-η}` over `Iz × (δ/4, δ)` agree
  (the honest Tonelli/Fubini swap).

Both facts are consequences of the single hypothesis that `w² g² sin(2θ)^{-η}` is
integrable on the full quadrant `Iz × Iθ`: the compact angular set `(δ/4, δ)` is contained
in `Iθ` for `0 < δ ≤ 1/16`, so the hypothesis restricts to it, and Mathlib's
Bochner–Fubini theorem applies on the product of the restricted measures.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open MeasureTheory Set Filter

theorem i0_fubini_package (g : ℝ → ℝ → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (g p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => Work.FTS.EllipticEst.thEta s
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2))
        (Set.Ioo (δ / 4) δ) ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ s in Set.Ioo (δ / 4) δ, (g z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
        = ∫ s in Set.Ioo (δ / 4) δ, Work.FTS.EllipticEst.thEta s
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2) := by
  -- `1/16 < π/2`, so the compact angular window `(δ/4, δ)` sits inside `Iθ = [0,π/2]`.
  have hpi : (1 : ℝ) / 16 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hJsub : Set.Ioo (δ / 4) δ ⊆ Work.Spaces.Iθ := by
    intro s hs
    rw [Set.mem_Ioo] at hs
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hs.1, hδ0], by linarith [hs.2, hδ16, hpi]⟩
  -- Restrict the hypothesis to the smaller angular window.
  have hsub : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (g p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) (Work.Spaces.Iz ×ˢ Set.Ioo (δ / 4) δ) :=
    hint.mono_set (Set.prod_mono_right hJsub)
  -- Turn it into integrability for the product of the two restricted measures.
  have hrest : Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (g p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict (Set.Ioo (δ / 4) δ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    exact hsub
  -- Mathlib's Fubini: the angular slices of the double integral are integrable.
  have hright := hrest.integral_prod_right
  -- The pointwise computation of a `z`-slice: the `θ`-weight is a constant for it.
  have hpt : ∀ s : ℝ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2
        * Work.FTS.EllipticEst.thEta s)
      = Work.FTS.EllipticEst.thEta s
        * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2) := by
    intro s
    rw [MeasureTheory.integral_mul_const (r := Work.FTS.EllipticEst.thEta s)
      (f := fun z => (Work.Spaces.w z) ^ 2 * (g z s) ^ 2), mul_comm]
  -- The same computation with the other association of the product.
  have hinner : ∀ s : ℝ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((g z s) ^ 2
        * Work.FTS.EllipticEst.thEta s))
      = Work.FTS.EllipticEst.thEta s
        * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2) := by
    intro s
    rw [← MeasureTheory.integral_const_mul (r := Work.FTS.EllipticEst.thEta s)
      (f := fun z => (Work.Spaces.w z) ^ 2 * (g z s) ^ 2)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  -- Integrability of the re-associated uncurried integrand (only the bracketing differs).
  have hfint : Integrable (Function.uncurry (fun z s : ℝ =>
      (Work.Spaces.w z) ^ 2 * ((g z s) ^ 2 * Work.FTS.EllipticEst.thEta s)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict (Set.Ioo (δ / 4) δ))) := by
    refine hrest.congr (Filter.Eventually.of_forall (fun p => ?_))
    obtain ⟨z, s⟩ := p
    simp only [Function.uncurry_apply_pair]
    ring
  refine ⟨?_, ?_⟩
  · -- The angular slices are integrable, and they are the required functions.
    refine hright.congr (Filter.Eventually.of_forall (fun s => ?_))
    show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2
        * Work.FTS.EllipticEst.thEta s) = _
    exact hpt s
  · -- Fubini for the two iterated integrals over `Iz` and `(δ/4, δ)`.
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ s in Set.Ioo (δ / 4) δ, (g z s) ^ 2 * Work.FTS.EllipticEst.thEta s)
        = ∫ z in Work.Spaces.Iz, ∫ s in Set.Ioo (δ / 4) δ, (Work.Spaces.w z) ^ 2
            * ((g z s) ^ 2 * Work.FTS.EllipticEst.thEta s) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
            (fun s => (g z s) ^ 2 * Work.FTS.EllipticEst.thEta s)).symm
      _ = ∫ s in Set.Ioo (δ / 4) δ, ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ((g z s) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
          MeasureTheory.integral_integral_swap (μ := volume.restrict Work.Spaces.Iz)
            (ν := volume.restrict (Set.Ioo (δ / 4) δ)) hfint
      _ = ∫ s in Set.Ioo (δ / 4) δ, Work.FTS.EllipticEst.thEta s
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (g z s) ^ 2) := by
          simp_rw [hinner]

end Work.EllipticEst.Core.i0Aux
