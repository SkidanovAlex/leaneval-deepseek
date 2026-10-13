/-
# `Work.FTS.FireFix.BundleNeg` — the admissible-strip bundle of a negated vorticity

The design's **correction 1** (`FTS_PHYS_BRIDGE.md` §0) takes the physical vorticity of the
reconstruction to be `ω := −physOmega α A B g C`, because the workspace's curl identity for a swirl
field carries a minus sign (`Physical/SignConvention.lean`).  Consequently every *bundle* statement
about the vorticity has to be transported across the sign.

This module does that transport, for each of the three groups of clauses of
`Work.CoreResiduals.BSAdmissibleStripFull α ω R S`:

* `BSAdmissibleStrip α ω R S` — support, uniform bound, slicewise `HolderWith`, time-Hölder,
  a.e. strong measurability: all invariant under `ω ↦ −ω` (the norm and the distance are;
  `−x ≠ 0 ↔ x ≠ 0`);
* `TimeDerivStrip ω S` — the slices are differentiable in `t` with `timeDeriv` as derivative, a
  uniform bound and a.e. strong measurability of the derivative slices: the derivative of `−ω` is
  `−∂_tω` (`timeDeriv_neg_field`), so the clauses transport;
* `TimeDerivStripHolder α ω S` — the time-Hölder continuity of `∂_tω`: invariant.

The upshot, `BSAdmissibleStripFull_neg`, is the form in which the firing theorem consumes the
per-strip bundles produced by `Work.FTS.FireFix.physOmega_bundle`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.FTS.Physical.SignConvention

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.CoreResiduals (BSAdmissibleStrip BSAdmissibleStripFull TimeDerivStrip
  TimeDerivStripHolder)

/-- **The time derivative of a negated space-time field**: `∂ₜ(−f) = −∂ₜf`.  This is
`Work.FTS.Physical.timeDeriv_neg` (the frozen physical layer's instance of `deriv.neg`). -/
theorem timeDeriv_neg_field (f : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    timeDeriv (fun y s => - f y s) x t = - timeDeriv f x t :=
  Work.FTS.Physical.timeDeriv_neg f x t

/-- **The strip admissibility of a negated vorticity.**  Every clause of `BSAdmissibleStrip` is
invariant under `ω ↦ −ω`: `‖−a‖ = ‖a‖`, `dist (−a) (−b) = dist a b`, `−a ≠ 0 ↔ a ≠ 0`, and
negation preserves a.e. strong measurability. -/
theorem BSAdmissibleStrip_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {R S : ℝ}
    (h : BSAdmissibleStrip α ω R S) :
    BSAdmissibleStrip α (fun x t => - ω x t) R S := by
  obtain ⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩ := h
  refine ⟨hR, ?_, ⟨M, ?_⟩, ⟨H, ?_⟩, ⟨N, ?_⟩, ?_⟩
  · intro t ht x hx
    exact hsupp t ht x (by simpa using hx)
  · intro t ht y
    simpa using hM t ht y
  · intro t ht
    refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
    rw [dist_neg_neg]
    exact (hH t ht).dist_le x y
  · intro y t ht t' ht'
    rw [show - ω y t - - ω y t' = - (ω y t - ω y t') by abel, norm_neg]
    exact hN y t ht t' ht'
  · intro t ht
    exact (hmeas t ht).neg

/-- **The time-regularity of the slices of a negated vorticity**: `∂ₜ(−ω) = −∂ₜω`, so the
differentiability, the uniform bound and the measurability of the derivative slices all transport. -/
theorem TimeDerivStrip_neg {ω : R3 → ℝ → R3} {S : ℝ} (h : TimeDerivStrip ω S) :
    TimeDerivStrip (fun x t => - ω x t) S := by
  obtain ⟨hdiff, ⟨M₁, hM₁⟩, hmeas⟩ := h
  refine ⟨fun t ht y => ?_, ⟨M₁, fun t ht y => ?_⟩, fun t ht => ?_⟩
  · have h2 : timeDeriv (fun x s => - ω x s) y t = - timeDeriv ω y t :=
      timeDeriv_neg_field ω y t
    rw [h2]
    exact (hdiff t ht y).neg
  · rw [timeDeriv_neg_field, norm_neg]
    exact hM₁ t ht y
  · have h' : (fun y : R3 => timeDeriv (fun x s => - ω x s) y t)
        = fun y : R3 => - timeDeriv ω y t := by
      funext y
      rw [timeDeriv_neg_field]
    rw [h']
    exact (hmeas t ht).neg

/-- **The time-Hölder continuity of `∂_tω` for a negated vorticity**: invariant. -/
theorem TimeDerivStripHolder_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {S : ℝ}
    (h : TimeDerivStripHolder α ω S) :
    TimeDerivStripHolder α (fun x t => - ω x t) S := by
  obtain ⟨N₁, hN₁⟩ := h
  refine ⟨N₁, fun y t ht t' ht' => ?_⟩
  rw [timeDeriv_neg_field, timeDeriv_neg_field,
    show - timeDeriv ω y t - - timeDeriv ω y t' = - (timeDeriv ω y t - timeDeriv ω y t')
      by abel, norm_neg]
  exact hN₁ y t ht t' ht'

/-- **The full admissible-strip bundle of a negated vorticity** (design correction 1). -/
theorem BSAdmissibleStripFull_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {R S : ℝ}
    (h : BSAdmissibleStripFull α ω R S) :
    BSAdmissibleStripFull α (fun x t => - ω x t) R S := by
  obtain ⟨hstrip, htd, htdh⟩ := h
  exact ⟨BSAdmissibleStrip_neg hstrip, TimeDerivStrip_neg htd, TimeDerivStripHolder_neg htdh⟩

end Work.FTS.FireFix
