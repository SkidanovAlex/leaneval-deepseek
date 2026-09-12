import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarBoundary
import Submission.ModelStarBoundary2

noncomputable section
open scoped Real BigOperators Topology
open Filter Set Complex
open Submission.ModelStarMap
open Submission.ModelStarBoundary2

/-!
# ModelStarBoundary3 -- boundary continuity & junction-zero limits of the
# model map (milestone (a) part 3, stage 3a: PROVED)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound]; unimported module (does NOT import
`Submission.lean`).  Builds on Submission.ModelStarMap (norm/boundary
identities of `F`), Submission.ModelStarBoundary (slitPlane factor lemmas)
and Submission.ModelStarBoundary2 (`eAngle`, per-`t` ray identity).

CONTENT (stage 3a: the analytic shell of the boundary map):
  * `modelF_differentiableAt_circle`: with unit junctions `z₀`, `modelF` is
    complex-differentiable at every unit-circle point `z` away from all
    junctions (each factor base lies in the slit plane there, by
    `one_sub_inv_mem_slitPlane_of_unit_ne` + `DifferentiableAt.cpow_const`).
  * `boundaryMap_continuousAt`: `t ↦ modelF z₀ r (eAngle t)` is continuous
    at `t₀` when the circle point `eAngle t₀` avoids all junctions.
  * `rho`/`rho_eq_norm_boundary`: the nonnegative real sweep factor
    `ρ(t) := ∏_k ‖1 − eAngle(φ k − t)‖^(2 r k)` equals `‖modelF z₀ r
    (eAngle t)‖` on the boundary, for `z₀ k = eAngle (φ k)`.
  * `rho_continuousAt` / `rho_junction_value_zero` /
    `rho_tendsto_junction_zero`: `ρ` is continuous everywhere (real `rpow`
    continuity at 0 with nonnegative exponent), and vanishes at each
    junction `φ j` with `0 < r j` (the `j`-factor is `0^(2 r j) = 0`, the
    others finite), so `ρ(t) → 0` as `t → φ j`.
  * `boundaryMap_tendsto_junction_zero`: `modelF z₀ r (eAngle t) → 0` as
    `t → φ j` (norm → 0 + `tendsto_zero_iff_norm_tendsto_zero`), provided
    the junctions are distinct.
Together with stage 2's `modelF_boundary_ray` this is stage 3b (next
milestone): on each open arc between consecutive junctions the boundary map
is continuous, vanishes at both junctions, and lies on the fixed ray of that
arc, so (IVT) the arc sweeps the segment `[0, m_j·e^{iΘ_j}]`,
`m_j := sup over the arc of ρ(t)`.
-/

namespace Submission.ModelStarBoundary3

/-- Complex-differentiability of the model map at a unit-circle point away
from all junctions. -/
theorem modelF_differentiableAt_circle {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    {z : ℂ} (hz₀ : ∀ k : Fin n, ‖z₀ k‖ = 1) (hz : ‖z‖ = 1)
    (hzj : ∀ k : Fin n, z₀ k ≠ z) :
    DifferentiableAt ℂ (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z) z := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hfac : ∀ k : Fin n, DifferentiableAt ℂ
      (fun w : ℂ => Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) w) z := by
    intro k
    have hg : DifferentiableAt ℂ (fun w : ℂ => 1 - z₀ k * w⁻¹) z := by
      have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := by
        simpa using (differentiableAt_inv (𝕜 := ℂ) (R := ℂ) hz0)
      exact (hinv.const_mul (z₀ k)).const_sub 1
    have h0 : 1 - z₀ k * z⁻¹ ∈ Complex.slitPlane :=
      Submission.ModelStarBoundary.one_sub_inv_mem_slitPlane_of_unit_ne (hz₀ k) hz (hzj k)
    simpa [Submission.ModelStarMap.modelFactor] using
      (DifferentiableAt.cpow_const (f := fun w : ℂ => (1 - z₀ k * w⁻¹)) (x := z)
        (c := ((2 * r k : ℝ) : ℂ)) hg h0)
  have hfacMem : ∀ k : Fin n, k ∈ (Finset.univ : Finset (Fin n)) → DifferentiableAt ℂ
      (fun w : ℂ => Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) w) z := by
    intro k hk
    exact hfac k
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) z := by
    simpa using (hasDerivAt_id z).differentiableAt
  have hprod' := DifferentiableAt.finsetProd (u := (Finset.univ : Finset (Fin n))) hfacMem
  have hfun : (∏ k ∈ (Finset.univ : Finset (Fin n)),
        (fun w : ℂ => Submission.ModelStarMap.modelFactor (z₀ k) (2 * r k) w)) =
        (fun w : ℂ => Submission.ModelStarMap.modelProduct z₀ r w) := by
    funext w
    rw [Finset.prod_apply]
    rfl
  have hprod : DifferentiableAt ℂ
      (fun w : ℂ => Submission.ModelStarMap.modelProduct z₀ r w) z := by
    simpa [hfun] using hprod'
  have hmul : DifferentiableAt ℂ (fun w : ℂ => w * Submission.ModelStarMap.modelProduct z₀ r w) z :=
    DifferentiableAt.mul hid hprod
  simpa [Submission.ModelStarMap.modelF] using hmul

/-- Continuity of the circle parametrisation `t ↦ eAngle t`. -/
lemma eAngle_continuousAt (t₀ : ℝ) : ContinuousAt (fun t : ℝ => eAngle t) t₀ := by
  unfold eAngle
  fun_prop

/-- Continuity of the boundary map `t ↦ modelF z₀ r (eAngle t)` away from
junctions. -/
theorem boundaryMap_continuousAt {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hz₀ : ∀ k : Fin n, ‖z₀ k‖ = 1) {t₀ : ℝ}
    (hzj : ∀ k : Fin n, z₀ k ≠ eAngle t₀) :
    ContinuousAt (fun t : ℝ => Submission.ModelStarMap.modelF z₀ r (eAngle t)) t₀ := by
  have hF : ContinuousAt (fun z : ℂ => Submission.ModelStarMap.modelF z₀ r z) (eAngle t₀) :=
    (modelF_differentiableAt_circle z₀ r hz₀ (by simp [eAngle]) hzj).continuousAt
  have hc : ContinuousAt (fun t : ℝ => eAngle t) t₀ := eAngle_continuousAt t₀
  exact hF.comp hc

/-- The nonnegative real sweep factor `ρ(t) = ∏_k ‖1 − e^{i(φ k−t)}‖^(2 r k)`. -/
def rho {n : ℕ} (φ : Fin n → ℝ) (r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ k : Fin n, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)

/-- `‖eAngle t − eAngle θ‖ = ‖1 − eAngle (θ − t)‖` (unit-circle rotation
identity). -/
lemma norm_eAngle_sub {t : ℝ} {θ : ℝ} :
    ‖eAngle t - eAngle θ‖ = ‖1 - eAngle (θ - t)‖ := by
  have hθ : eAngle θ = eAngle t * eAngle (θ - t) := by
    unfold eAngle
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h : eAngle t - eAngle θ = eAngle t * (1 - eAngle (θ - t)) := by
    rw [hθ]
    ring
  rw [h, norm_mul]
  have hnorm : ‖eAngle t‖ = 1 := by
    unfold eAngle
    simp
  rw [hnorm, one_mul]

/-- `ρ(t) = ‖modelF z₀ r (eAngle t)‖` whenever `z₀ k = eAngle (φ k)` and
all junctions are unit. -/
theorem rho_eq_norm_boundary {n : ℕ} (z₀ : Fin n → ℂ) (φ : Fin n → ℝ) (r : Fin n → ℝ)
    (hz₀e : ∀ k : Fin n, z₀ k = eAngle (φ k)) {t : ℝ} :
    rho φ r t = ‖Submission.ModelStarMap.modelF z₀ r (eAngle t)‖ := by
  have hz : ‖eAngle t‖ = 1 := by unfold eAngle; simp
  have hnorm := Submission.ModelStarMap.norm_modelF_unit z₀ r hz
  have heq1 : (∏ k : Fin n, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)) =
      (∏ k : Fin n, ‖eAngle t - z₀ k‖ ^ (2 * r k)) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [hz₀e k]
    rw [← norm_eAngle_sub (t := t) (θ := φ k)]
  unfold rho
  rw [heq1]
  rw [hnorm]

/-- Continuity of the sweep factor (with nonnegative exponents; a factor
whose base vanishes at the point is handled by
`Real.continuousAt_rpow_const` with `0 ≤ exponent`). -/
lemma rho_continuousAt {n : ℕ} (φ : Fin n → ℝ) (r : Fin n → ℝ)
    (hr : ∀ k : Fin n, 0 ≤ r k) (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ => rho φ r t) t₀ := by
  have hfac : ∀ k : Fin n, ContinuousAt (fun t : ℝ =>
      ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)) t₀ := by
    intro k
    have hc' : ContinuousAt (fun t : ℝ => eAngle (φ k - t)) t₀ := by
      unfold eAngle
      fun_prop
    have hsub : ContinuousAt (fun t : ℝ => (1 : ℂ) - eAngle (φ k - t)) t₀ := by
      fun_prop
    have hbase : ContinuousAt (fun t : ℝ => ‖1 - eAngle (φ k - t)‖) t₀ := by
      fun_prop
    have hq : 0 ≤ 2 * r k := by nlinarith [hr k]
    exact (Real.continuousAt_rpow_const (‖1 - eAngle (φ k - t₀)‖) (2 * r k)
      (Or.inr hq)).tendsto.comp hbase.tendsto
  have hfin := tendsto_finsetProd (s := (Finset.univ : Finset (Fin n))) (f := fun k : Fin n =>
    fun t : ℝ => ‖1 - eAngle (φ k - t)‖ ^ (2 * r k)) (x := 𝓝 t₀)
    (a := fun k : Fin n => ‖1 - eAngle (φ k - t₀)‖ ^ (2 * r k))
  have hall : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Tendsto (fun t : ℝ => ‖1 - eAngle (φ i - t)‖ ^ (2 * r i)) (𝓝 t₀)
        (𝓝 (‖1 - eAngle (φ i - t₀)‖ ^ (2 * r i))) := by
    intro i hi
    exact (hfac i).tendsto
  have hlim := hfin hall
  change Tendsto (fun t : ℝ => ∏ k : Fin n, ‖1 - eAngle (φ k - t)‖ ^ (2 * r k))
    (𝓝 t₀) (𝓝 (∏ k : Fin n, ‖1 - eAngle (φ k - t₀)‖ ^ (2 * r k)))
  simpa using hlim

/-- The sweep factor vanishes at a junction of positive weight:
`ρ(φ j) = 0` when `0 < r j`. -/
lemma rho_junction_value_zero {n : ℕ} (φ : Fin n → ℝ) (r : Fin n → ℝ)
    {j : Fin n} (hrj : 0 < r j) :
    rho φ r (φ j) = 0 := by
  unfold rho
  have hzero : ‖1 - eAngle (φ j - φ j)‖ ^ (2 * r j) = 0 := by
    have hdiff : φ j - φ j = 0 := by ring
    rw [hdiff]
    unfold eAngle
    simp
    rw [Real.zero_rpow]
    exact ne_of_gt (mul_pos (by norm_num) hrj)
  simpa using (Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin n)))
    (f := fun k : Fin n => ‖1 - eAngle (φ k - φ j)‖ ^ (2 * r k))
    (i := j) (Finset.mem_univ j) hzero)

/-- **Sweep factor tends to zero at a junction of positive weight.** -/
theorem rho_tendsto_junction_zero {n : ℕ} (φ : Fin n → ℝ) (r : Fin n → ℝ)
    (hr : ∀ k : Fin n, 0 ≤ r k) {j : Fin n} (hrj : 0 < r j) :
    Tendsto (fun t : ℝ => rho φ r t) (𝓝 (φ j)) (𝓝 0) := by
  have hc := rho_continuousAt φ r hr (φ j)
  have hlim : Tendsto (fun t : ℝ => rho φ r t) (𝓝 (φ j)) (𝓝 (rho φ r (φ j))) := hc.tendsto
  simpa [rho_junction_value_zero φ r (j := j) hrj] using hlim

/-- **Boundary map vanishes at a junction**: as `t → φ j`, the boundary
value `modelF z₀ r (eAngle t)` tends to `0`, provided the junctions are
unit, distinct (`z₀ k ≠ z₀ j` for `k ≠ j`), `z₀ k = eAngle (φ k)`,
weights nonnegative and `0 < r j`. -/
theorem boundaryMap_tendsto_junction_zero {n : ℕ} (z₀ : Fin n → ℂ) (φ : Fin n → ℝ)
    (r : Fin n → ℝ) (hz₀e : ∀ k : Fin n, z₀ k = eAngle (φ k))
    {j : Fin n}
    (hr : ∀ k : Fin n, 0 ≤ r k) (hrj : 0 < r j) :
    Tendsto (fun t : ℝ => Submission.ModelStarMap.modelF z₀ r (eAngle t)) (𝓝 (φ j)) (𝓝 0) := by
  have hnormlim : Tendsto (fun t : ℝ => ‖Submission.ModelStarMap.modelF z₀ r (eAngle t)‖)
      (𝓝 (φ j)) (𝓝 0) := by
    have hzlim := rho_tendsto_junction_zero φ r hr (j := j) hrj
    have hpoint : ∀ t : ℝ, rho φ r t = ‖Submission.ModelStarMap.modelF z₀ r (eAngle t)‖ :=
      fun t => rho_eq_norm_boundary z₀ φ r hz₀e (t := t)
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall hpoint) hzlim
  exact tendsto_zero_iff_norm_tendsto_zero.2 hnormlim

end Submission.ModelStarBoundary3

end
