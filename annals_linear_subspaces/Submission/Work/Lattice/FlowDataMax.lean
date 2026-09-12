import Mathlib
import Submission.Work.Lattice.MaxNorm
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.MaxNormPosition
import Submission.Work.Lattice.FlowRateAsymptotic
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.GeometryOfNumbers.ModelCone
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# The max-norm ("paper") rank data along the flow — definitions and first facts

The Grayson polygon of de Saxcé's §3 is built with the **sup norm** `cnorm` on `⋀^k ℝᵈ`
(`Submission.MaxNorm.cnorm`), because for that norm the flow acts by exact exponential
scaling of the blocks (`Submission.MaxNorm.cnorm_map_flow`):

    `cnorm (⋀^k a_t w) = maxᵤ exp (t·σ_u) · cnorm (blockElem w u)`,

so that for large `t` the value is *exactly* `exp (t·σ_{u₀}) · cnorm (blockElem w u₀)` with
`u₀ = topBlockIndex ℓ w` (`Submission.MaxNormFlow.eventually_cnorm_map_flow_eq_top`) — i.e. the
flowed log-covolume of a fixed subgroup is, for large `t`, an **affine function of `t`** with
slope `σ_{u₀}`.  This exact affinity is what the time-selection argument consumes
(`Submission.GoodTime.sum_mul_ge_of_good_of_affine`).

Here we set up the two data functions for a lattice `Λ₀ ≤ ℝᵈ` and the exponential two-scale
flow `a_t` (`a = e^{−t/ℓ}`, `b = e^{t/(d−ℓ)}`):

* `flowMaxDataSet Λ₀ ℓ t j` / `flowMaxData Λ₀ ℓ t j` — the infimum of `log (cnorm (⋀^j (a_t ∘ v)))`
  over `ℝ`-independent families `v : Fin j → Λ₀` (the "presentations" of the rank-`j`
  subgroups; for an integer family the value depends on the subgroup only through the ℤ-basis
  choice, cf. `Commons.LinearAlgebra.Alternating.iMulti_unit_smul_of_intSpan_eq`);
* `flowEuclidDataSet Λ₀ ℓ t j` / `flowEuclidData Λ₀ ℓ t j` — the same with the Euclidean norm
  (the flowed covolumes, related to `LatticePolygon.rankData` of the flowed lattice `Λ_t = a_t Λ₀`).

First facts proved here: `flowMaxData ≤ flowEuclidData` (`cnorm ≤ ‖·‖`), the exact block formula,
and the **eventual exact affinity** for a fixed family.

Module `Submission.Work.Lattice.FlowDataMax`, namespace `Submission.FlowDataMax`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.FlowDataMax

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic

variable {d : ℕ}

/-- The exponential two-scale flow map of the §3 route (`d > ℓ > 0`), as a plain linear map:
`diag (e^{−t/ℓ})` on the first `ℓ` coordinates and `diag (e^{t/(d−ℓ)})` on the rest. -/
def eFlow (ℓ : ℕ) (t : ℝ) : RD d →ₗ[ℝ] RD d :=
  scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ)

@[simp] lemma eFlow_apply (ℓ : ℕ) (t : ℝ) (v : RD d) :
    eFlow (d := d) ℓ t v =
      scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ) v := rfl

lemma eFlow_eq (ℓ : ℕ) (t : ℝ) :
    eFlow (d := d) ℓ t =
      scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ) := rfl

/-- The max-norm rank-`j` data set of `Λ₀` at time `t`: `log cnorm` of the flowed wedges of
`ℝ`-independent families in `Λ₀`. -/
def flowMaxDataSet (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (j : ℕ) (hjd : j ≤ d) : Set ℝ :=
  {r | ∃ v : Fin j → RD d, (∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v ∧
    r = Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t)
      (exteriorPower.ιMulti ℝ j v)))}

/-- The max-norm rank-`j` data of `Λ₀` at time `t`. -/
def flowMaxData (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (j : ℕ) (hjd : j ≤ d) : ℝ :=
  sInf (flowMaxDataSet Λ₀ ℓ t j hjd)

/-- The Euclidean rank-`j` data set of `Λ₀` at time `t` (the flowed covolumes). -/
def flowEuclidDataSet (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (j : ℕ) : Set ℝ :=
  {r | ∃ v : Fin j → RD d, (∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v ∧
    r = Real.log ‖exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)‖}

/-- The Euclidean rank-`j` data of `Λ₀` at time `t`. -/
def flowEuclidData (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  sInf (flowEuclidDataSet Λ₀ ℓ t j)

/-! ### The exact block formula and the norms' comparison -/

/-- **The block formula for the flowed max-norm wedge** (exact identity). -/
theorem cnorm_eFlow_iMulti {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d) (t : ℝ)
    (v : Fin j → RD d) :
    cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)) =
      (Finset.range (j + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
        (fun u => Real.exp (t * sig (d := d) j ℓ u) *
          cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j v) u)) := by
  rw [eFlow_eq]
  exact cnorm_map_flow (d := d) (k := j) (ℓ := ℓ) hℓ0 hℓd t hjd
    (exteriorPower.ιMulti ℝ j v)

/-- The exponential flow map (as a plain diagonal map with positive coefficients) is
injective. -/
lemma eFlow_injective (ℓ : ℕ) (t : ℝ) : Function.Injective (eFlow (d := d) ℓ t) := by
  have ha : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hb : Real.exp (t / ((d - ℓ : ℕ) : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hleft : (scaleMap (fun i : Fin d =>
      (twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ i)⁻¹)) ∘ₗ
      (eFlow (d := d) ℓ t) = LinearMap.id := by
    rw [eFlow_eq]
    exact Submission.ModelCone.scaleMap_twoScale_comp_inv (d := d) _ _ ℓ ha hb
  refine Function.LeftInverse.injective (g := fun x : RD d =>
    scaleMap (fun i : Fin d =>
      (twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ i)⁻¹) x)
    (fun x => ?_)
  have := congrArg (fun φ : RD d →ₗ[ℝ] RD d => φ x) hleft
  simpa [LinearMap.comp_apply] using this

/-- The flowed wedge of a `ℝ`-independent family is nonzero. -/
lemma map_eFlow_iMulti_ne_zero {j ℓ : ℕ} (t : ℝ) {v : Fin j → RD d} (hv : LinearIndependent ℝ v) :
    exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v) ≠ 0 := by
  rw [exteriorPower.map_apply_ιMulti]
  refine Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ ?_
  have hker : LinearMap.ker (eFlow (d := d) ℓ t) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (eFlow_injective (d := d) ℓ t)
  have hmap : LinearIndependent ℝ (eFlow (d := d) ℓ t ∘ v) :=
    hv.map (f := eFlow (d := d) ℓ t) (by rw [hker]; exact disjoint_bot_right)
  simpa [Function.comp_def] using hmap

/-- The max-norm flowed wedge is dominated by the Euclidean one. -/
lemma cnorm_eFlow_le_norm {j ℓ : ℕ} (hjd : j ≤ d) (t : ℝ) (v : Fin j → RD d) :
    cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)) ≤
      ‖exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)‖ :=
  cnorm_le_norm hjd _

/-- **The eventual exact affinity of the flowed log-covolume of a fixed family.**  For an
`ℝ`-independent family `v : Fin j → Λ₀` and all sufficiently large `t`, the flowed max-norm
log-covolume is *exactly* affine in `t` with slope `σ_{u₀}`, `u₀ = topBlockIndex ℓ (⋀v)`:

    `log cnorm (⋀^j a_t (⋀v)) = log cnorm (blockElem (⋀v) u₀) + t · σ_{u₀}`.

This is the form consumed by the time-selection argument
(`Submission.GoodTime.sum_mul_ge_of_good_of_affine`). -/
theorem eventually_log_cnorm_eFlow_iMulti_eq {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    {v : Fin j → RD d} (hv : LinearIndependent ℝ v) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t)
          (exteriorPower.ιMulti ℝ j v))) =
        Real.log (cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ)
            (exteriorPower.ιMulti ℝ j v) (topBlockIndex (d := d) ℓ (exteriorPower.ιMulti ℝ j v)))) +
          t * sig (d := d) j ℓ (topBlockIndex (d := d) ℓ (exteriorPower.ιMulti ℝ j v)) := by
  have hw : exteriorPower.ιMulti ℝ j v ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hv
  have hblk : cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j v)
      (topBlockIndex (d := d) ℓ (exteriorPower.ιMulti ℝ j v))) ≠ 0 :=
    ne_of_gt (cnorm_pos_of_ne_zero hjd _ (blockElem_topBlockIndex_ne_zero (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j v) hw))
  obtain ⟨T, hT⟩ := eventually_cnorm_map_flow_eq_top (d := d) (k := j) (ℓ := ℓ) hℓ0 hℓd hjd
    (exteriorPower.ιMulti ℝ j v) hw
  refine ⟨T, fun t ht => ?_⟩
  rw [eFlow_eq, hT t ht,
    Real.log_mul (Real.exp_ne_zero _) hblk, Real.log_exp]
  ring

end Submission.FlowDataMax
