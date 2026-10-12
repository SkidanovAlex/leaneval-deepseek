import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vanishing on the box from a vanishing boxed `L²`-norm

`Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero`: a **continuous** state
`ψ` on the `m`-particle configuration space `X m` with vanishing boxed `L²`-norm
square `sqNormB m ℓ ψ = ∫_{abox m ℓ} ψ² = 0` (for `ℓ > 0`) vanishes *pointwise* on
the centred box.

## Route

* `convex_acube` / `convex_abox` — the centred cube `acube ℓ ⊆ ℝ³` (coordinatewise
  convexity, `Icc` being an interval and `smul`/`add` acting coordinatewise on
  `EuclideanSpace ℝ (Fin 3)`) and hence its `m`-fold power `abox m ℓ`
  (`abox_eq_pi_acube` + `convex_pi`).
* `interior_abox_nonempty` — the box has nonempty interior since `abox m ℓ`
  contains the ball of radius `ℓ/2` around the origin (`mem_acube_of_norm_le` and
  `norm_le_pi_norm`).
* `abox_subset_closure_interior` — `abox m ℓ ⊆ closure (interior (abox m ℓ))`,
  because the box is closed and convex with nonempty interior
  (`Convex.closure_interior_eq_closure_of_nonempty_interior`).
* the theorem: `ψ²` is continuous and nonnegative, hence integrable on the compact
  box; `setIntegral_eq_zero_iff_of_nonneg_ae` turns the vanishing integral into
  `ψ = 0` a.e. on the box, and `Measure.eqOn_of_ae_eq` upgrades this to pointwise
  vanishing using the regularity of the box.
-/

noncomputable section

open MeasureTheory
open scoped Topology ENNReal Real

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

/-! ## Convexity and regularity of the centred box -/

/-- The centred cube `acube ℓ ⊆ ℝ³` is convex: it is a coordinatewise `Icc` and both
`•` and `+` on `EuclideanSpace ℝ (Fin 3)` act coordinatewise. -/
lemma convex_acube (ℓ : ℝ) : Convex ℝ (acube ℓ) := by
  intro y hy z hz a b ha hb hab
  rw [mem_acube_iff] at hy hz ⊢
  intro k
  have hyk := hy k
  have hzk := hz k
  rw [Set.mem_Icc] at hyk hzk ⊢
  rw [show (a • y + b • z).ofLp k = a * y.ofLp k + b * z.ofLp k by simp]
  exact ⟨by nlinarith [hyk.1, hzk.1, ha, hb, hab],
         by nlinarith [hyk.2, hzk.2, ha, hb, hab]⟩

/-- The `m`-particle centred box is convex (it is the `m`-fold power of a convex set). -/
lemma convex_abox (m : ℕ) (ℓ : ℝ) : Convex ℝ (abox m ℓ) := by
  rw [abox_eq_pi_acube]
  exact convex_pi (fun _ _ => convex_acube ℓ)

/-- The centred box has nonempty interior (for `ℓ > 0`): it contains the ball of radius
`ℓ/2` around the origin. -/
lemma interior_abox_nonempty {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (interior (abox m ℓ)).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : X m) (show (0 : ℝ) < ℓ / 2 by positivity)) ?_
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [mem_abox_iff]
  intro i
  exact mem_acube_of_norm_le hℓ.le (le_trans (norm_le_pi_norm x i) hx.le)

/-- Every point of the closed box lies in the closure of its interior: the box is closed
and convex with nonempty interior. -/
lemma abox_subset_closure_interior {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    abox m ℓ ⊆ closure (interior (abox m ℓ)) := by
  have h := (convex_abox m ℓ).closure_interior_eq_closure_of_nonempty_interior
    (interior_abox_nonempty hℓ)
  rw [h, (abox_isClosed m ℓ).closure_eq]

/-! ## The vanishing theorem -/

theorem eq_zero_on_abox_of_sqNormB_eq_zero {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ψ : Submission.BoseGases.X m → ℝ} (hψ : Continuous ψ)
    (h0 : Work.BoseKinLoc.sqNormB m ℓ ψ = 0) :
    ∀ x ∈ Submission.BoseGases.abox m ℓ, ψ x = 0 := by
  have h0' : ∫ x in Submission.BoseGases.abox m ℓ, (ψ x) ^ 2 = 0 := by
    simpa [Work.BoseKinLoc.sqNormB] using h0
  -- `ψ²` is integrable on the compact box
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X m => (ψ x) ^ 2)
      (Submission.BoseGases.abox m ℓ) volume :=
    ContinuousOn.integrableOn_compact (abox_compact m hℓ) (hψ.pow 2).continuousOn
  -- vanishing integral + nonnegativity gives `ψ = 0` a.e. on the box
  have hae : (fun x : Submission.BoseGases.X m => ψ x)
      =ᵐ[volume.restrict (Submission.BoseGases.abox m ℓ)] 0 := by
    have h : (fun x : Submission.BoseGases.X m => (ψ x) ^ 2)
        =ᵐ[volume.restrict (Submission.BoseGases.abox m ℓ)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hInt).mp h0'
    filter_upwards [h] with x hx using sq_eq_zero_iff.mp hx
  -- a.e. equality plus continuity and the closure-of-interior regularity of the box
  exact fun x hx => Measure.eqOn_of_ae_eq hae hψ.continuousOn continuous_zero.continuousOn
    (abox_subset_closure_interior hℓ) hx

end Work.BoseKinLoc.Sector
