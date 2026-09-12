import Mathlib
import Submission.Work.Lattice.CnormDataBdd
import Submission.Work.Lattice.PolygonLipschitz
import Submission.Commons.Analysis.Calculus.exists_sum_mul_deriv_ge_neg

/-!
# The max-norm Grayson polygon of the §3 flow, and its Lipschitz continuity

For the §3 accounting (`Submission.AccountingOneSided`) the polygon must be built with the
**max-norm** data (`FlowDataMax.flowMaxData`), not the Euclidean one (see the roadmap, STATUS
162 §3).  This module fixes the layer:

* `maxData Λ₀ ℓ t` — the rank data at time `t` as a function `ℕ → ℝ` (with the harmless
  convention `0` outside `1 ≤ j ≤ d`, in particular at `j = 0` where the data is `0` anyway);
* `maxPolygon Λ₀ ℓ t := largestConvexMinorant d (maxData Λ₀ ℓ t)` — the Grayson polygon;
* `maxSlope Λ₀ ℓ t i := dslope (maxPolygon Λ₀ ℓ t) i` — its slopes `Λ_i(t)`;
* `maxEnergy Λ₀ ℓ t := Σ_{i<d} (maxSlope Λ₀ ℓ t i)²` — the energy `E(t) ≥ 0`.

and proves the Lipschitz bounds in `t` for `Λ₀ = g(ℤᵈ)`, `g` a linear isometry (from
`CnormLevel.flowMaxData_lipschitz` + `CnormDataBdd.bddBelow_flowMaxDataSet_imageSpan` +
`Polygon.abs_largestConvexMinorant_sub_le` / `abs_dslope_largestConvexMinorant_sub_le`).

The energy together with the good-time atom
`Commons.Analysis.Calculus.exists_sum_mul_deriv_ge_neg` yields the good time
`Σ_i Λ_i(t)·Λ_i'(t) ≥ −1` used by the accounting.

Module `Submission.Work.Lattice.MaxNormPolygon`, namespace `Submission.MaxNormPolygon`.
-/

noncomputable section

open LinearSubspaces Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.CnormLevel
open Submission.CnormDataBdd
open Submission.Polygon

namespace Submission.MaxNormPolygon

variable {d : ℕ}

/-- The max-norm rank data of the flow at time `t`, as a function of the rank (with the value
`0` outside `1 ≤ j ≤ d`; at `j = 0` the true data is `0` as well). -/
noncomputable def maxData (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) : ℕ → ℝ :=
  fun j => if h : 1 ≤ j ∧ j ≤ d then flowMaxData Λ₀ ℓ t j h.2 else 0

/-- The **max-norm Grayson polygon** of the flow at time `t`. -/
noncomputable def maxPolygon (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) : ℕ → ℝ :=
  largestConvexMinorant d (maxData (d := d) Λ₀ ℓ t)

/-- The **slopes** `Λ_i(t) = dslope c_t i` of the max-norm polygon. -/
noncomputable def maxSlope (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  dslope (maxPolygon (d := d) Λ₀ ℓ t) i

/-- The **energy** `E(t) = Σ_{i<d} Λ_i(t)² ≥ 0`. -/
noncomputable def maxEnergy (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, (maxSlope (d := d) Λ₀ ℓ t i) ^ 2

lemma maxData_apply_of {Λ₀ : Submodule ℤ (RD d)} {ℓ : ℕ} {t : ℝ} {j : ℕ}
    (hj : 1 ≤ j) (hjd : j ≤ d) :
    maxData (d := d) Λ₀ ℓ t j = flowMaxData Λ₀ ℓ t j hjd := by
  rw [maxData, dif_pos ⟨hj, hjd⟩]

lemma maxData_apply_of_not {Λ₀ : Submodule ℤ (RD d)} {ℓ : ℕ} {t : ℝ} {j : ℕ}
    (hj : ¬ (1 ≤ j ∧ j ≤ d)) :
    maxData (d := d) Λ₀ ℓ t j = 0 := by
  rw [maxData, dif_neg hj]

/-- The Lipschitz constant of the max-norm data. -/
noncomputable def lipConst (d ℓ : ℕ) : ℝ :=
  (d : ℝ) * max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ))

lemma lipConst_nonneg (d ℓ : ℕ) : 0 ≤ lipConst d ℓ := by
  rw [lipConst]
  positivity

/-- **The max-norm data is Lipschitz in `t`** (for the isometry-image lattice of §3). -/
theorem maxData_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) (j : ℕ) :
    |maxData (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ s j -
        maxData (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j| ≤
      lipConst d ℓ * |s - t| := by
  classical
  by_cases h : 1 ≤ j ∧ j ≤ d
  · rw [maxData_apply_of h.1 h.2, maxData_apply_of h.1 h.2]
    have hlip := flowMaxData_lipschitz (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd h.2 _
      (fun u => bddBelow_flowMaxDataSet_imageSpan (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd h.2 h.1 g u)
      s t
    refine le_trans hlip ?_
    have h1 : (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ)) ≤ lipConst d ℓ := by
      rw [lipConst]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.2) (by positivity)
    have h2 : 0 ≤ max (1 / (ℓ : ℝ)) (1 / (((d - ℓ : ℕ)) : ℝ)) := by positivity
    have h3 : 0 ≤ |s - t| := abs_nonneg _
    exact mul_le_mul_of_nonneg_right h1 h3
  · rw [maxData_apply_of_not h, maxData_apply_of_not h, sub_self, abs_zero]
    exact mul_nonneg (lipConst_nonneg d ℓ) (abs_nonneg _)

/-- **The max-norm polygon is Lipschitz in `t`.** -/
theorem maxPolygon_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) {i : ℕ} (hi : i ≤ d) :
    |maxPolygon (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ s i -
        maxPolygon (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t i| ≤
      lipConst d ℓ * |s - t| := by
  refine abs_largestConvexMinorant_sub_le _ _ (fun j hj => ?_) hi
  exact maxData_lipschitz (d := d) hℓ0 hℓd g s t j

/-- **The slopes of the max-norm polygon are Lipschitz in `t`.** -/
theorem maxSlope_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) {i : ℕ} (hi : i + 1 ≤ d) :
    |maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ s i -
        maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t i| ≤
      2 * (lipConst d ℓ * |s - t|) := by
  refine abs_dslope_largestConvexMinorant_sub_le (i := i) _ _ (fun j hj => ?_) hi
  exact maxData_lipschitz (d := d) hℓ0 hℓd g s t j

lemma maxEnergy_nonneg (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    0 ≤ maxEnergy (d := d) Λ₀ ℓ t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **The slopes form a Lipschitz family** (the hypothesis of the good-time atom). -/
theorem maxSlope_lipschitz_family {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) :
    ∀ (i : Fin d) (s t : ℝ),
      |maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
          ℓ s i.val -
        maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
          ℓ t i.val| ≤
      (2 * lipConst d ℓ) * |s - t| := by
  intro i s t
  have h := maxSlope_lipschitz (d := d) hℓ0 hℓd g s t (i := i.val) (by omega)
  rwa [← mul_assoc] at h

/-- **The good time of the max-norm polygon.**  For every `c > 0` and every `T` there is `t ≥ T`
at which all the slopes `Λ_i` are differentiable and
`Σ_i Λ_i(t)·Λ_i'(t) ≥ −c`.  (This is the input of the accounting
`Submission.AccountingOneSided.lemma4_identity` via `Σ_i Λ_i ∂Λ_i = Σ_s Λ_s·Δr_s`.) -/
theorem maxSlope_good_time {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∀ i : Fin d, DifferentiableAt ℝ
        (fun u => maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
          ℓ u i.val) t) ∧
      -c ≤ ∑ i : Fin d,
        maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
          ℓ t i.val *
        deriv (fun u => maxSlope (d := d)
          (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ u i.val) t := by
  have hC : 0 ≤ 2 * lipConst d ℓ := by
    have := lipConst_nonneg d ℓ
    linarith
  exact Commons.Analysis.Calculus.exists_sum_mul_deriv_ge_neg (d := d) hC
    (fun i => maxSlope_lipschitz_family (d := d) hℓ0 hℓd g i) hc T


end Submission.MaxNormPolygon

end
