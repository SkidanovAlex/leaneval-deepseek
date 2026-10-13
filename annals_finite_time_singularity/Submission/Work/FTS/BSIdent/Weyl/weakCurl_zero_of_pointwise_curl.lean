/-
# The weak vanishing of the curl, from a *pointwise* curl identity

`Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl`: a continuous field `D : ℝ³ → ℝ³` which is
differentiable off the two coordinate planes `x 0 = 0`, `x 2 = 0`, and whose (pointwise) vorticity
vanishes off those planes, pairs to zero with the curl of every smooth compactly supported field:

  `∫ x, ⟪D x, ∇×Ψ x⟫ = 0`.

This is the *weak* (distributional) form of `curl D = 0`, one of the two Weyl/Liouville inputs of
the physical identification (route C of `FTS_HARD_DESIGN.md` §(C)).  It is the sibling
`Work.FTS.BSIdent.Weyl.weakCurl_eq_zero_of_vorticity_eq_zero` with the hypothesis
`LocallyIntegrable (fderiv ℝ D)` **removed** — that hypothesis is never used: the only place where
integrability of a derivative enters is the divergence theorem for the *compactly supported* field
`D × Ψ`, and there the divergence is supplied by the pointwise Weyl identity, which exhibits it
(almost everywhere) as the continuous compactly supported function `-⟪D x, ∇×Ψ x⟫`.

## Proof

Nothing here needs a potential: the divergence theorem on the complement of the two planes does all
the work.

* the pointwise Weyl identity for the curl (`Work.FTS.BSSwirl.inner_vorticity_sub_eq_div`)

    `div (D × Ψ) x = ⟪∇×D x, Ψ x⟫ - ⟪D x, ∇×Ψ x⟫`

  holds at every point where `D` and `Ψ` are differentiable, i.e. off the two planes;
* the hypothesis `∇×D = 0` off the planes therefore gives
  `div (D × Ψ) = -⟪D x, ∇×Ψ x⟫` almost everywhere.  *This is what replaces the missing local
  integrability of `fderiv ℝ D`*: the right-hand side is continuous and compactly supported (the
  curl of a smooth compactly supported field is compactly supported), hence integrable, and so is
  `div (D × Ψ)` (they agree off the null set `{x 0 = 0} ∪ {x 2 = 0}`);
* the field `D × Ψ` is continuous (both factors are), compactly supported (`Ψ` is) and
  differentiable with derivative `fderiv` off the two planes (product rule for the cross product,
  `Work.FTS.BSSwirl.hasFDerivAt_crossR3`);
* hence `∫ div (D × Ψ) = 0` by `Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes` (the
  divergence theorem with the faces along the two planes matched pairwise: the field is continuous
  across them, so the two face contributions cancel);
* combining the two displays gives `∫ ⟪D, ∇×Ψ⟫ = 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.BSSwirl.integral_vorticity_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Filter
open scoped Topology

namespace Work.FTS.BSIdent.Weyl

theorem weakCurl_zero_of_pointwise_curl {D : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hDcont : Continuous D)
    (hDdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt D (fderiv ℝ D x) x)
    (hcurl0 : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → FiniteTimeSingularity.vorticity D x = 0)
    {Ψ : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hΨcs : HasCompactSupport Ψ) :
    ∫ x, inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x) = 0 := by
  -- the field `D × Ψ` whose divergence is the difference of the two curl pairings
  have hWdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y))
        (fderiv ℝ (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x) x := by
    intro x hx0 hx2
    have h := Work.FTS.BSSwirl.hasFDerivAt_crossR3 (hDdiff x hx0 hx2)
      (((hΨ 1).differentiable_one x).hasFDerivAt)
    simpa only [h.fderiv] using h
  have hWcont : Continuous (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) :=
    (Work.FTS.BSSwirl.contDiff_crossR3 (contDiff_zero.mpr hDcont) (hΨ 0)).continuous
  have hWcs : HasCompactSupport (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  -- the pointwise Weyl identity, with `∇×D = 0` off the planes
  have hpt : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 →
      FiniteTimeSingularity.div (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x
        = - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x) := by
    intro x hx0 hx2
    have h := Work.FTS.BSSwirl.inner_vorticity_sub_eq_div (V := D) (Ψ := Ψ) (x := x)
      (hDdiff x hx0 hx2).differentiableAt ((hΨ 1).differentiable_one x)
    rw [hcurl0 x hx0 hx2, inner_zero_left, zero_sub] at h
    exact h.symm
  have hae : (fun x => FiniteTimeSingularity.div
        (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x)
      =ᵐ[volume] (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with x hx
    exact hpt x hx.1 hx.2
  -- the curl of a compactly supported smooth field is compactly supported
  have hvortcs : HasCompactSupport (FiniteTimeSingularity.vorticity Ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    refine hx ?_
    have h0 : Ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport Ψ).isOpen_compl.mem_nhds hcon] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hd : fderiv ℝ Ψ x = 0 := by rw [h0.fderiv_eq]; simp
    rw [Work.FTS.BSSwirl.vorticity_eq_sum_crossR3]
    simp [hd]
  -- `div (D × Ψ)` is integrable: it agrees a.e. with the continuous compactly supported
  -- `-⟪D, ∇×Ψ⟫` (this is where the local integrability of `fderiv ℝ D` would have been used)
  have hint : Integrable (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) := by
    have hcont : Continuous (fun x => - inner ℝ (D x) (FiniteTimeSingularity.vorticity Ψ x)) :=
      (continuous_inner.comp (hDcont.prodMk (Work.FTS.BSSwirl.continuous_vorticity (hΨ 1)))).neg
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact hvortcs ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  have hWint : Integrable
      (fun x => FiniteTimeSingularity.div (fun y => Work.FTS.BSSwirl.crossR3 (D y) (Ψ y)) x) :=
    hint.congr hae.symm
  -- the divergence theorem off the two planes, and the conclusion
  have h0 := Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes hWcont hWcs hWdiff hWint
  rw [MeasureTheory.integral_congr_ae hae] at h0
  rw [MeasureTheory.integral_neg] at h0
  exact neg_eq_zero.mp h0

end Work.FTS.BSIdent.Weyl
