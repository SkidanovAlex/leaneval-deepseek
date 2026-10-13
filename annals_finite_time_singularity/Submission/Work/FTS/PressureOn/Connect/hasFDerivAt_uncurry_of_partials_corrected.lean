/-
# `hasFDerivAt_uncurry_of_partials`, with the hypothesis that makes it true

The requested lemma `Work.FTS.PressureOn.Connect.hasFDerivAt_uncurry_of_partials` (see the
sibling file `hasFDerivAt_uncurry_of_partials.lean`) is **false** as stated: its hypothesis

`∀ᶠ y in nhds x, ∀ᶠ s in nhds t, HasDerivAt (fun s' => q y s') (deriv … s) s`

only gives, for each fixed `y`, a *neighbourhood of `t` of radius depending on `y`*, and the
mean value theorem — which is the only way to pass from the pointwise derivative to the
increment — needs a *uniform* neighbourhood: the whole segment between `t` and `s` must lie
where the slice is differentiable.  The counterexample
`q y s = if y = 0 then 0 else if s < ‖y‖/10 then 0 else 1` satisfies all four hypotheses while
the uncurried map is discontinuous at the origin; see
`hasFDerivAt_uncurry_of_partials_refute.lean`.

The present file proves the statement with the correct hypothesis: the second partial derivative
exists on a **neighbourhood of `(x,t)` in the product space**,

`∀ᶠ p in nhds (x, t), HasDerivAt (fun s' => q p.1 s') (deriv (fun s' => q p.1 s') p.2) p.2`,

which is exactly what one gets from joint differentiability/smoothness of `q` near `(x,t)`
(the intended application), and which supplies by `Metric.mem_nhds_iff` a box
`B(x,δ) × (t-δ, t+δ)` on which every slice `q y ·` (`y ∈ B(x,δ)`) is differentiable at every
point.  With that, the mean value theorem applies on the segment and the argument goes through:
write `q p.1 p.2 - q x t = (q p.1 t - q x t) + (q p.1 p.2 - q p.1 t)`, control the first term
by `hx` (composed with the projection) and the second by the mean value theorem applied to
`s ↦ q p.1 s - s * c` on `Ioo (t-δ) (t+δ)` (note there is a *single* `δ` for all `y` in the
box), the derivative being `deriv (fun s' => q p.1 s') s - c`, which is `< ε` on the box by
`hcont2` and `ht.deriv`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Asymptotics
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

/-- **The corrected form of `hasFDerivAt_uncurry_of_partials`.**  If

* `y ↦ q y t` is differentiable at `x` with derivative `L`;
* `s ↦ q x s` is differentiable at `t` with derivative `c`;
* `s ↦ q p.1 s` is differentiable for `p` in a *neighbourhood of `(x,t)` in the product space*,
  with derivative `deriv (fun s' => q p.1 s') p.2`;
* that derivative function is continuous at `(x,t)`,

then the uncurried map `p ↦ q p.1 p.2` is differentiable at `(x,t)` with derivative
`L ∘ fst + smulRight snd c`. -/
theorem hasFDerivAt_uncurry_of_partials'
    {q : R3 → ℝ → ℝ} {x : R3} {t : ℝ} {L : R3 →L[ℝ] ℝ} {c : ℝ}
    (hx : HasFDerivAt (fun y => q y t) L x) (ht : HasDerivAt (fun s => q x s) c t)
    (h2 : ∀ᶠ p in nhds (x, t),
      HasDerivAt (fun s' => q p.1 s') (deriv (fun s' => q p.1 s') p.2) p.2)
    (hcont2 : ContinuousAt (fun p : R3 × ℝ => deriv (fun s' => q p.1 s') p.2) (x, t)) :
    HasFDerivAt (fun p : R3 × ℝ => q p.1 p.2)
      (L.comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) c) (x, t) := by
  -- * the `x`-direction: compose `hx` with the projection
  have hA : HasFDerivAt (fun p : R3 × ℝ => q p.1 t)
      (L.comp (ContinuousLinearMap.fst ℝ R3 ℝ)) (x, t) := by
    have h := hx.comp (x, t) (hasFDerivAt_fst (𝕜 := ℝ) (E := R3) (F := ℝ) (p := (x, t)))
    simpa [Function.comp_def] using h
  have hAlo : (fun p : R3 × ℝ => q p.1 t - q x t - L (p.1 - x))
      =o[nhds (x, t)] (fun p : R3 × ℝ => p - (x, t)) := by
    have h := hasFDerivAt_iff_isLittleO.mp hA
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', Prod.fst_sub] using h
  -- * the `t`-direction: mean value theorem on a *uniform* box around `(x,t)`
  have hBlo : (fun p : R3 × ℝ => q p.1 p.2 - q p.1 t - (p.2 - t) * c)
      =o[nhds (x, t)] (fun p : R3 × ℝ => p - (x, t)) := by
    refine IsLittleO.of_bound fun ε hε => ?_
    -- a uniform differentiability box for the slices
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.mem_nhds_iff.mp h2
    -- a uniform continuity radius for the derivative of the slices
    obtain ⟨δ₂, hδ₂0, hδ₂raw⟩ := (Metric.continuousAt_iff.mp hcont2) ε hε
    have hδ₂ : ∀ p : R3 × ℝ, dist p (x, t) < δ₂ →
        dist (deriv (fun s' => q p.1 s') p.2) c < ε := by
      intro p hp
      have := hδ₂raw hp
      simpa [ht.deriv] using this
    have hδmin : 0 < min δ₁ δ₂ := lt_min hδ₁0 hδ₂0
    filter_upwards [Metric.ball_mem_nhds (x, t) (ε := min δ₁ δ₂) hδmin] with p hp
    rw [Metric.mem_ball, Prod.dist_eq] at hp
    have hp1 : dist p.1 x < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hp
    have hp2 : dist p.2 t < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hp
    have hp1₁ : dist p.1 x < δ₁ := lt_of_lt_of_le hp1 (min_le_left _ _)
    have hp1₂ : dist p.1 x < δ₂ := lt_of_lt_of_le hp1 (min_le_right _ _)
    have hmem₁ : ∀ u : ℝ, |u - t| < min δ₁ δ₂ → dist (p.1, u) (x, t) < δ₁ := by
      intro u hu
      rw [Prod.dist_eq]
      exact max_lt hp1₁ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_left _ _))
    have hmem₂ : ∀ u : ℝ, |u - t| < min δ₁ δ₂ → dist (p.1, u) (x, t) < δ₂ := by
      intro u hu
      rw [Prod.dist_eq]
      exact max_lt hp1₂ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_right _ _))
    have hmvt : ‖(q p.1 p.2 - p.2 * c) - (q p.1 t - t * c)‖ ≤ ε * ‖p.2 - t‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun u : ℝ => q p.1 u - u * c)
        (s := Set.Ioo (t - min δ₁ δ₂) (t + min δ₁ δ₂)) (x := t) (y := p.2) (C := ε) ?_ ?_
        (convex_Ioo _ _) ?_ ?_
      · -- differentiability of the slice, shifted by `c * ·`, on the whole interval
        intro u hu
        rw [Set.mem_Ioo] at hu
        have hu' : |u - t| < min δ₁ δ₂ := by
          rw [abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hm : (p.1, u) ∈ Metric.ball (x, t) δ₁ := by
          rw [Metric.mem_ball]; exact hmem₁ u hu'
        exact ((hδ₁ hm).sub ((hasDerivAt_id u).mul_const c)).differentiableAt
      · -- bound on the derivative on the interval
        intro u hu
        rw [Set.mem_Ioo] at hu
        have hu' : |u - t| < min δ₁ δ₂ := by
          rw [abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hm : (p.1, u) ∈ Metric.ball (x, t) δ₁ := by
          rw [Metric.mem_ball]; exact hmem₁ u hu'
        have hu1 : HasDerivAt (fun s' : ℝ => q p.1 s') (deriv (fun s' : ℝ => q p.1 s') u) u :=
          hδ₁ hm
        have hfun : (fun u' : ℝ => q p.1 u' - u' * c)
            = ((fun s' : ℝ => q p.1 s') - fun y : ℝ => y * c) := by funext u'; rfl
        have hder' : deriv ((fun s' : ℝ => q p.1 s') - fun y : ℝ => y * c) u
            = deriv (fun s' : ℝ => q p.1 s') u - c := by
          have h := (hu1.sub ((hasDerivAt_id u).mul_const c)).deriv
          simpa [id_eq] using h
        rw [hfun, hder', Real.norm_eq_abs]
        exact le_of_lt (hδ₂ ⟨p.1, u⟩ (hmem₂ u hu'))
      · exact ⟨by linarith, by linarith⟩
      · rw [Set.mem_Ioo]
        have : |p.2 - t| < min δ₁ δ₂ := by rwa [Real.dist_eq] at hp2
        obtain ⟨h1, h2'⟩ := abs_lt.mp this
        exact ⟨by linarith, by linarith⟩
    have heq : (q p.1 p.2 - p.2 * c) - (q p.1 t - t * c)
        = q p.1 p.2 - q p.1 t - (p.2 - t) * c := by ring
    rw [heq] at hmvt
    have hnorm : ‖p.2 - t‖ ≤ ‖p - (x, t)‖ := by
      calc ‖p.2 - t‖ = |p.2 - t| := Real.norm_eq_abs _
        _ = dist p.2 t := by rw [Real.dist_eq]
        _ ≤ dist p (x, t) := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ = ‖p - (x, t)‖ := dist_eq_norm p (x, t)
    exact le_trans hmvt (mul_le_mul_of_nonneg_left hnorm (le_of_lt hε))
  -- * assemble the two little-o estimates
  rw [hasFDerivAt_iff_isLittleO]
  refine (hAlo.add hBlo).congr_left fun p => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

end Work.FTS.PressureOn.Connect
