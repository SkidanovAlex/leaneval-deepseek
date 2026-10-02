import Mathlib
import Submission.Work.LandLeaves.exists_local_repelling_branch

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Clash-free copy of `exists_local_repelling_branch_cont` (see `V2Anchor/Helpers.lean`).
The imported module `exists_rayAccum_singleton_of_isRepelling` of the original is unused here and
is dropped, so that the file carries no `AnchorHelpers` dependency. -/

/-!
# The local repelling branch at a repelling periodic point, with continuity

`Work.LandLeaves.exists_local_repelling_branch` produces the contracting local inverse branch `g`
of `τ = (T_c)^{2k}` at a repelling periodic point `y` of odd period `k`, but it does *not* record
that `g` is continuous.  For the bead/branch containment argument
(`Submission/Work/LandLeaves/image_subset_paramRay_of_connected.lean`) the continuity of `g` on a
ball around `y` is needed, so here we redo the construction keeping it.

## The argument

`τ = (Tsq c)^[k] = (T_c)^{2k}` is a polynomial, hence entire, and it fixes `y`; its multiplier
`deriv τ y = multiplier2 c k y` has modulus `> 1` because `y` is repelling.  Writing
`e` for the `OpenPartialHomeomorph` that the (strict) inverse function theorem attaches to `τ`
at `y`, the local inverse branch `g` is `e.symm`.  Hence `g` is continuous on `e.target`, an open
set containing `τ y = y`, so on some ball `B(y, δt)`; the ball is one of the finitely many
constraints used to choose the radii `r < r'`.  The remaining three clauses are exactly the
contents of `Work.LandLeaves.exists_local_repelling_branch`, obtained as usual from the strict
derivative `(deriv τ y)⁻¹` of modulus `< 1` (contraction estimate
`exists_contraction_ball_cont`) and from the eventual left/right inverse identities.

## Main result

* `Work.LandLeaves.V2Anchor.exists_local_repelling_branch_cont`.
-/

open Filter Asymptotics
open scoped Topology

namespace Work.LandLeaves.V2Anchor

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Contraction estimate for a fixed point of multiplier of modulus `< 1`.**  (Copy of the
private lemma of `Submission/Work/LandLeaves/exists_local_repelling_branch.lean`.) -/
private theorem exists_contraction_ball_cont {g : ℂ → ℂ} {c y : ℂ} (hg : HasDerivAt g c y)
    (hgy : g y = y) (hc : ‖c‖ < 1) :
    ∃ (κ δ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧
      ∀ w : ℂ, ‖w - y‖ ≤ δ → ‖g w - y‖ ≤ κ * ‖w - y‖ := by
  set κ : ℝ := (1 + ‖c‖) / 2 with hκdef
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hκ1 : κ < 1 := by rw [hκdef]; linarith
  have hεpos : 0 < κ - ‖c‖ := by rw [hκdef]; linarith
  have hF : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℂ c) y :=
    hasDerivAt_iff_hasFDerivAt.mp hg
  have hlit : (fun w : ℂ => g w - g y - (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y))
      =o[nhds y] (fun w : ℂ => w - y) := hF.isLittleO
  have hbound : ∀ᶠ w in nhds y,
      ‖g w - g y - (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y)‖ ≤
        (κ - ‖c‖) * ‖w - y‖ := IsLittleO.def hlit hεpos
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hbound
  refine ⟨κ, δ₀ / 2, hκ0, hκ1, by positivity, fun w hw => ?_⟩
  have hw' : dist w y < δ₀ := by rw [dist_eq_norm]; linarith
  have h1 := hδ₀ hw'
  have h2 : (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y) = c * (w - y) := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have heq : g w - y = (g w - g y - (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y))
      + (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y) := by
    rw [hgy]; ring
  calc ‖g w - y‖
      = ‖(g w - g y - (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y))
          + (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y)‖ := by rw [heq]
    _ ≤ ‖g w - g y - (ContinuousLinearMap.toSpanSingleton ℂ c) (w - y)‖
          + ‖(ContinuousLinearMap.toSpanSingleton ℂ c) (w - y)‖ := norm_add_le _ _
    _ ≤ (κ - ‖c‖) * ‖w - y‖ + ‖c‖ * ‖w - y‖ := by
          apply add_le_add h1
          rw [h2, norm_mul]
    _ = κ * ‖w - y‖ := by ring

/-- **The local repelling branch, with continuity.**  Everything
`Work.LandLeaves.exists_local_repelling_branch` gives, plus `g` is continuous on the ball
`Metric.ball y r'` on which it inverts `τ = (T_c)^{2k}`. -/
theorem exists_local_repelling_branch_cont {c : ℂ} {k : ℕ} {y : ℂ}
    (h : Work.Landing.IsRepelling c k y) :
    ∃ (r r' κ : ℝ) (g : ℂ → ℂ), 0 < r ∧ r < r' ∧ 0 ≤ κ ∧ κ < 1 ∧ g y = y ∧
      ContinuousOn g (Metric.ball y r') ∧
      (∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖) ∧
      (∀ w : ℂ, ‖w - y‖ ≤ r' →
        (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w) ∧
      (∀ z : ℂ, ‖z - y‖ ≤ r → ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z - y‖ ≤ r' →
        g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z) = z) := by
  obtain ⟨hper, hmult⟩ := h
  have hf_diff : Differentiable ℂ ((Work.Landing.Tsq c)^[k]) := by
    have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
      show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
      fun_prop
    exact h1.iterate k
  have hiter : (Work.Landing.Tsq c)^[k] = (Tantibar c)^[2 * k] := by
    rw [Tsq_eq_iterate_two, Function.iterate_mul]
  have hfy : ((Work.Landing.Tsq c)^[k]) y = y := by
    rw [hiter]
    rw [show 2 * k = k * 2 from by ring, Function.iterate_mul]
    exact (show Function.IsFixedPt ((Tantibar c)^[k]) y from hper.2).iterate 2
  have hstrict : HasStrictDerivAt ((Work.Landing.Tsq c)^[k])
      (deriv ((Work.Landing.Tsq c)^[k]) y) y :=
    (hf_diff.analyticAt y).hasStrictDerivAt
  have hderiv_ne : deriv ((Work.Landing.Tsq c)^[k]) y ≠ 0 := by
    intro h0
    have hmult0 : Work.Landing.multiplier2 c k y = 0 := h0
    rw [hmult0, norm_zero] at hmult
    linarith
  set g : ℂ → ℂ := HasStrictDerivAt.localInverse ((Work.Landing.Tsq c)^[k])
      (deriv ((Work.Landing.Tsq c)^[k]) y) y hstrict hderiv_ne with hgdef
  have hone : g = ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).symm := by
    rw [hgdef]; rfl
  have hg_strict : HasStrictDerivAt g (deriv ((Work.Landing.Tsq c)^[k]) y)⁻¹ y := by
    simpa [hgdef, hfy] using hstrict.to_localInverse hderiv_ne
  have hg_left : ∀ᶠ u in nhds y, g (((Work.Landing.Tsq c)^[k]) u) = u := by
    have h' := hstrict.eventually_left_inverse hderiv_ne
    filter_upwards [h'] with u hu
    rwa [hgdef]
  have hg_right : ∀ᶠ z in nhds y, ((Work.Landing.Tsq c)^[k]) (g z) = z := by
    have h' := hstrict.eventually_right_inverse hderiv_ne
    rw [hfy] at h'
    filter_upwards [h'] with z hz
    rwa [hgdef]
  have hgy : g y = y := by
    have h' := (hstrict.eventually_left_inverse hderiv_ne).self_of_nhds
    rw [hfy] at h'
    exact h'
  have hc_lt : ‖(deriv ((Work.Landing.Tsq c)^[k]) y)⁻¹‖ < 1 := by
    rw [norm_inv]
    refine inv_lt_one_of_one_lt₀ ?_
    have hd : deriv ((Work.Landing.Tsq c)^[k]) y = Work.Landing.multiplier2 c k y := rfl
    rw [hd]; exact hmult
  obtain ⟨κ, δc, hκ0, hκ1, hδc, hcontr⟩ :=
    exists_contraction_ball_cont hg_strict.hasDerivAt hgy hc_lt
  obtain ⟨δr, hδr_pos, hδr⟩ := Metric.mem_nhds_iff.mp hg_right
  obtain ⟨δl, hδl_pos, hδl⟩ := Metric.mem_nhds_iff.mp hg_left
  -- the ball on which `g` is continuous
  have hcont_target : ContinuousOn g ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).target := by
    rw [hone]
    exact ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).continuousOn_symm
  have hmem_target : y ∈ ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).target := by
    have h2 := (hstrict.hasStrictFDerivAt_equiv hderiv_ne).image_mem_toOpenPartialHomeomorph_target
    simpa [hfy] using h2
  have hopen_target : IsOpen ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).target :=
    ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).open_target
  obtain ⟨δt, hδt_pos, hδt⟩ := Metric.mem_nhds_iff.mp (hopen_target.mem_nhds hmem_target)
  set r' : ℝ := min (min δc δr) δt / 2 with hr'def
  set r : ℝ := min r' δl / 2 with hrdef
  have hr'pos : 0 < r' := by rw [hr'def]; positivity
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hr_lt : r < r' := by
    rw [hrdef]
    have : min r' δl ≤ r' := min_le_left _ _
    linarith
  have hr_lt_dl : r < δl := by
    rw [hrdef]
    have : min r' δl ≤ δl := min_le_right _ _
    linarith
  have hr'_lt_dc : r' < δc := by
    rw [hr'def]
    have : min (min δc δr) δt ≤ min δc δr := min_le_left _ _
    have : min δc δr ≤ δc := min_le_left _ _
    linarith
  have hr'_lt_dr : r' < δr := by
    rw [hr'def]
    have : min (min δc δr) δt ≤ min δc δr := min_le_left _ _
    have : min δc δr ≤ δr := min_le_right _ _
    linarith
  have hr'_lt_dt : r' < δt := by
    rw [hr'def]
    have : min (min δc δr) δt ≤ δt := min_le_right _ _
    linarith
  have hball_sub : Metric.ball y r' ⊆ ((hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      ((Work.Landing.Tsq c)^[k])).target := by
    intro z hz
    exact hδt (by rw [Metric.mem_ball, dist_eq_norm] at hz ⊢; exact lt_of_lt_of_le hz (le_of_lt hr'_lt_dt))
  refine ⟨r, r', κ, g, hrpos, hr_lt, hκ0, hκ1, hgy, ?_, ?_, ?_, ?_⟩
  · exact hcont_target.mono hball_sub
  · intro w hw
    exact hcontr w (le_trans hw (le_of_lt hr'_lt_dc))
  · intro w hw
    rw [← hiter]
    exact hδr (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hw hr'_lt_dr)
  · intro z hz _
    rw [← hiter]
    exact hδl (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hz hr_lt_dl)
end Work.LandLeaves.V2Anchor

