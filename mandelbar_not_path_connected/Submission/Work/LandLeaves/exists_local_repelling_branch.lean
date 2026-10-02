import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.LandLeaves.attractingCyclesInner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A local repelling branch at a repelling periodic point of the tricorn

Let `T_c z = z̄² + c` be the antiholomorphic quadratic (the tricorn family) and let
`Tsq c = T_c ∘ T_c` be its holomorphic second iterate, so that the `k`-th iterate of the
*second return map* is `(Tsq c)^[k] = (T_c)^[2k]`.

If `y` is a repelling periodic point of odd period `k` (`Work.Landing.IsRepelling c k y`), then
`y` is a repelling fixed point of the holomorphic `τ = (T_c)^[2k]` whose multiplier
`deriv τ y = Work.Landing.multiplier2 c k y` has modulus `> 1`.  By the (strict) inverse function
theorem `τ` is locally biholomorphic at `y`; its inverse branch `g` is defined and holomorphic on
some ball `B(y, r')`, contracts distances to `y` by a fixed factor `κ < 1` there, and inverts `τ`
on `B(y, r')` and on the part of a smaller ball `B(y, r)` that `τ` maps into `B(y, r')`.

This is the local model of the repelling dynamics used by the landing/Snail-lemma arguments
(`Submission/Work/LandLeaves/SnailLemma.lean`, `.../snailDichotomy_of_noNeutral.lean`,
`.../goldbergMilnorB1.lean`): a repelling periodic point of `T_c` looks, through the holomorphic
second return map, exactly like a repelling fixed point of a polynomial.

## The construction

`τ` is a polynomial, hence entire; `AnalyticAt.hasStrictDerivAt` upgrades its derivative at `y` to
a *strict* derivative, and Mathlib's one-dimensional inverse function theorem
`HasStrictDerivAt.localInverse` produces the inverse branch.  Its derivative at `y` is the inverse
`(deriv τ y)⁻¹` of the multiplier, of modulus `< 1`, so the elementary contraction estimate
(`exists_contraction_ball` below) turns the little-o form of the derivative at `y` into a genuine
contraction estimate on a small closed ball.

## Main result

* `Work.LandLeaves.exists_local_repelling_branch`.
-/

open Filter Asymptotics
open scoped Topology

namespace Work.LandLeaves

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Contraction estimate for a fixed point of multiplier of modulus `< 1`.**

If `g : ℂ → ℂ` is differentiable at `y` with derivative `c`, fixes `y` (`g y = y`), and
`‖c‖ < 1`, then on some closed ball `B(y, δ)` the map `g` contracts distances to `y` by a fixed
factor `κ < 1`: `‖g w - y‖ ≤ κ * ‖w - y‖`.

This is the elementary estimate behind `Work.LandLeaves.exists_local_repelling_branch`: it is the
same computation as `Work.LandLeaves.exists_ball_iterate_norm_sub_lt`, except that here the
Lipschitz constant `κ = (1 + ‖c‖)/2 < 1` is recorded, since the inverse branch of a repelling
fixed point is only *locally* the restriction of a suitable iterate. -/
private theorem exists_contraction_ball {g : ℂ → ℂ} {c y : ℂ} (hg : HasDerivAt g c y)
    (hgy : g y = y) (hc : ‖c‖ < 1) :
    ∃ (κ δ : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧
      ∀ w : ℂ, ‖w - y‖ ≤ δ → ‖g w - y‖ ≤ κ * ‖w - y‖ := by
  -- the contraction factor `κ = (1 + ‖c‖)/2 ∈ [0, 1)`
  set κ : ℝ := (1 + ‖c‖) / 2 with hκdef
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hκ1 : κ < 1 := by rw [hκdef]; linarith
  have hεpos : 0 < κ - ‖c‖ := by rw [hκdef]; linarith
  -- the derivative in `F`-form, and its little-o statement
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

/-- Local repelling structure at a repelling periodic point of the tricorn: the holomorphic
second return map `τ z = (Tantibar c)^[2 * k] z` (which fixes `y` with
`‖deriv τ y‖ = ‖multiplier2 c k y‖ > 1`) is a bijection from a small ball onto a larger ball and
its inverse branch contracts toward `y`.

  ∃ r r' κ g, 0 < r ∧ r < r' ∧ 0 ≤ κ ∧ κ < 1 ∧ g y = y
    ∧ (∀ w, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖)
    ∧ (∀ w, ‖w - y‖ ≤ r' → (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w)
    ∧ (∀ z, ‖z - y‖ ≤ r → ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z - y‖ ≤ r' →
        g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z) = z).

Useful ingredients already in the tree: `Tsq_iterate_eq_Tantibar` and `differentiable_Tsq_iterate`
in `Submission/Work/LandLeaves/attractingCyclesInner.lean` identify `(Tantibar c)^[2*k]` with
`(Tsq c)^[k]` and give its differentiability, so `deriv ((Tantibar c)^[2*k]) y = multiplier2 c k y`
has norm `> 1`; the quantitative inverse function result then applies. -/
theorem exists_local_repelling_branch {c : ℂ} {k : ℕ} {y : ℂ}
    (h : Work.Landing.IsRepelling c k y) :
    ∃ (r r' κ : ℝ) (g : ℂ → ℂ), 0 < r ∧ r < r' ∧ 0 ≤ κ ∧ κ < 1 ∧ g y = y ∧
      (∀ w : ℂ, ‖w - y‖ ≤ r' → ‖g w - y‖ ≤ κ * ‖w - y‖) ∧
      (∀ w : ℂ, ‖w - y‖ ≤ r' →
        (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w) ∧
      (∀ z : ℂ, ‖z - y‖ ≤ r → ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z - y‖ ≤ r' →
        g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z) = z) := by
  obtain ⟨hper, hmult⟩ := h
  -- `τ = (Tsq c)^[k]` is the `k`-th iterate of the holomorphic second return map
  have hf_diff : Differentiable ℂ ((Work.Landing.Tsq c)^[k]) := by
    have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
      show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
      fun_prop
    exact h1.iterate k
  -- `(Tsq c)^[k] = (T_c)^[2k]`
  have hiter : (Work.Landing.Tsq c)^[k] = (Tantibar c)^[2 * k] := by
    rw [Tsq_eq_iterate_two, Function.iterate_mul]
  -- the periodic point of `T_c` is a fixed point of the second return map
  have hfy : ((Work.Landing.Tsq c)^[k]) y = y := by
    rw [hiter]
    rw [show 2 * k = k * 2 from by ring, Function.iterate_mul]
    exact (show Function.IsFixedPt ((Tantibar c)^[k]) y from hper.2).iterate 2
  -- `τ` is entire, hence strictly differentiable at `y`
  have hstrict : HasStrictDerivAt ((Work.Landing.Tsq c)^[k])
      (deriv ((Work.Landing.Tsq c)^[k]) y) y :=
    (hf_diff.analyticAt y).hasStrictDerivAt
  -- the multiplier is nonzero, since its modulus is `> 1`
  have hderiv_ne : deriv ((Work.Landing.Tsq c)^[k]) y ≠ 0 := by
    intro h0
    have hmult0 : Work.Landing.multiplier2 c k y = 0 := h0
    rw [hmult0, norm_zero] at hmult
    linarith
  -- the inverse branch produced by the inverse function theorem
  set g : ℂ → ℂ := HasStrictDerivAt.localInverse ((Work.Landing.Tsq c)^[k])
      (deriv ((Work.Landing.Tsq c)^[k]) y) y hstrict hderiv_ne with hgdef
  have hg_strict : HasStrictDerivAt g (deriv ((Work.Landing.Tsq c)^[k]) y)⁻¹ y := by
    have h' := HasStrictDerivAt.to_localInverse hstrict hderiv_ne
    rw [hfy] at h'
    simpa [hgdef] using h'
  have hg_left : ∀ᶠ u in nhds y, g (((Work.Landing.Tsq c)^[k]) u) = u := by
    have h' := hstrict.eventually_left_inverse hderiv_ne
    simpa [hgdef] using h'
  have hg_right : ∀ᶠ z in nhds y, ((Work.Landing.Tsq c)^[k]) (g z) = z := by
    have h' : ∀ᶠ z in nhds (((Work.Landing.Tsq c)^[k]) y),
        ((Work.Landing.Tsq c)^[k]) (g z) = z := by
      have h'' := hstrict.eventually_right_inverse hderiv_ne
      simpa [hgdef] using h''
    rwa [hfy] at h'
  have hgy : g y = y := by
    have h' := (hstrict.eventually_left_inverse hderiv_ne).self_of_nhds
    rwa [hfy] at h'
  -- the derivative of the inverse branch has modulus `< 1`
  have hc_lt : ‖(deriv ((Work.Landing.Tsq c)^[k]) y)⁻¹‖ < 1 := by
    rw [norm_inv]
    refine inv_lt_one_of_one_lt₀ ?_
    have hd : deriv ((Work.Landing.Tsq c)^[k]) y = Work.Landing.multiplier2 c k y := rfl
    rw [hd]; exact hmult
  -- the contraction estimate for `g`
  obtain ⟨κ, δc, hκ0, hκ1, hδc, hcontr⟩ :=
    exists_contraction_ball hg_strict.hasDerivAt hgy hc_lt
  -- balls on which `g` is the right and the left inverse of `τ`
  obtain ⟨δr, hδr_pos, hδr⟩ := Metric.mem_nhds_iff.mp hg_right
  obtain ⟨δl, hδl_pos, hδl⟩ := Metric.mem_nhds_iff.mp hg_left
  -- choose the two radii: `r'` for the range ball, `r < r'` for the domain ball
  set r' : ℝ := min δc δr / 2 with hr'def
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
    have : min δc δr ≤ δc := min_le_left _ _
    linarith
  have hr'_lt_dr : r' < δr := by
    rw [hr'def]
    have : min δc δr ≤ δr := min_le_right _ _
    linarith
  refine ⟨r, r', κ, g, hrpos, hr_lt, hκ0, hκ1, hgy, ?_, ?_, ?_⟩
  · -- contraction
    intro w hw
    exact hcontr w (le_trans hw (le_of_lt hr'_lt_dc))
  · -- right inverse: `τ (g w) = w` on `B(y, r')`
    intro w hw
    rw [← hiter]
    exact hδr (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hw hr'_lt_dr)
  · -- left inverse: `g (τ z) = z` on `B(y, r)`
    intro z hz _
    rw [← hiter]
    exact hδl (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hz hr_lt_dl)

end Work.LandLeaves
