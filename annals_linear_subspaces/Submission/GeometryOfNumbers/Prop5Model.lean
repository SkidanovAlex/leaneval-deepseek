import Mathlib
import Submission.GeometryOfNumbers.WedgeContract
import Submission.GeometryOfNumbers.BlockCovering
import Submission.GeometryOfNumbers.Lemma5Model
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Work.Polygon.ContractPolygon

/-!
# Prop 5 in the model: directions → annulus vectors with π₀ control and log upper

Paper §3 Prop 5 produces, for the flow lattice, vectors `v₁,…,v_k` with
`‖π₀(v₁∧…∧v_k)‖ ≽ ‖v₁∧…∧v_k‖` and a log upper bound in terms of the polygon slopes.  In
the coordinate model the construction is the contracting-block chain:

* Lemma-5-model directions `u` (an orthonormal family inside the contracting block's real
  span `blockSpan ℓ ⊆ x₀`) → `BlockCovering.exists_blockFamily_annulus_exp` gives an
  annulus family `w : Fin k → smallFlow (exp flow)` with
  `‖wᵢ − 11·(ℓ:ℝ)e^{−t/ℓ}·uᵢ‖ ≤ (ℓ:ℝ)e^{−t/ℓ}` and `‖wᵢ‖ ∈ [10C, 12C]`,
  `C = (ℓ:ℝ)e^{−t/ℓ}`;
* `WedgeContract.wedgeContract_blockAnnulus_lower` gives the `π₀`-lower bound
  `(∏ᵢ‖wᵢ‖)(1 − k/5) ≤ ‖π₀(ιMulti w)‖`; combined with the Commons wedge-≤-product bound
  and `norm_pi0_le` this is the two-sided π₀ control
  `(1 − k/5)‖ιMulti w‖ ≤ ‖π₀(ιMulti w)‖ ≤ ‖ιMulti w‖`;
* the log upper `log‖ιMulti w‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ` follows from
  `log_wedge_le_sum_log` (`log‖wedge‖ ≤ Σᵢ log‖wᵢ‖`, wedge ≤ product, positivity via the
  π₀ lower bound) plus the contracting-block log interval.

The assembled statement is **`prop5_model_contracting`** (the annulus family in the
contracting sublattice `smallFlow`), and **`prop5_model_lift`** lifts it to the full flow
lattice `a_t ℤᵈ` of Prop 5 (`smallFlow ≤ flowLattice`).

All results are Mathlib-only (besides the Submission geometry modules).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice

set_option maxHeartbeats 3000000

namespace Submission.Prop5Model

/-- **`log‖wedge‖ ≤ Σᵢ log‖vᵢ‖`**: for a family of nonzero vectors with nonzero wedge,
the log of the wedge norm is at most the sum of the logs of the norms (wedge ≤ product of
norms, log monotone, `Real.log_prod`). -/
lemma log_wedge_le_sum_log {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) (v : Fin k → E) (hv0 : ∀ i : Fin k, 0 < ‖v i‖)
    (hw0 : 0 < ‖exteriorPower.ιMulti ℝ k v‖) :
    Real.log ‖exteriorPower.ιMulti ℝ k v‖ ≤ ∑ i : Fin k, Real.log ‖v i‖ := by
  have hwle : ‖exteriorPower.ιMulti ℝ k v‖ ≤ (∏ i : Fin k, ‖v i‖) :=
    Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod v
  have hlog := Real.log_le_log hw0 hwle
  rw [Real.log_prod (s := Finset.univ) (f := fun i : Fin k => ‖v i‖)
    (by intro i hi; exact ne_of_gt (hv0 i))] at hlog
  exact hlog

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Prop 5 in the model (contracting chain, annulus family)**: for the exponential flow
(`0 < ℓ < d`, any real `t`), an orthonormal family `u : Fin k → ℝᵈ` of Lemma-5 directions
inside the contracting block's real span (`u i ∈ blockSpan ℓ`, `1 ≤ k ≤ 4`) yields an
annulus family `w : Fin k → smallFlow (a_t)` of the contracting sublattice with
`(1 − k/5)·‖ιMulti w‖ ≤ ‖π₀(ιMulti w)‖ ≤ ‖ιMulti w‖` and
`log‖ιMulti w‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`. -/
theorem prop5_model_contracting {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (u : Fin k → ℝᵈ) (hu_mem : ∀ i : Fin k, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) :
    ∃ w : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      (1 - (k : ℝ) / 5) * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ ≤
          ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ ∧
        ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ ≤
          ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ ∧
        Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ ≤
          (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
  classical
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  obtain ⟨w, hwann⟩ := Submission.BlockCovering.exists_blockFamily_annulus_exp (d := d) ℓ
    hℓd (m := k) (u := u) hu_mem (fun i => huON.1 i)
  refine ⟨w, ?_, ?_, ?_⟩
  · -- (1 − k/5)·‖wedge‖ ≤ ‖π₀ wedge‖ : wedge ≤ product, then block-annulus lower
    have hlower := Submission.WedgeContract.wedgeContract_blockAnnulus_lower (d := d) (k := k)
      ℓ (le_of_lt hℓd) (a := Real.exp (-t / (ℓ : ℝ)))
      (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) (Real.exp_pos _) hℓ0 u hu_mem huON hk0 w hwann
    have hle : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ ≤
        (∏ i : Fin k, ‖(w i : ℝᵈ)‖) :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
        (fun i : Fin k => (w i : ℝᵈ))
    have h1m : 0 ≤ 1 - (k : ℝ) / 5 := by
      have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
      nlinarith
    calc
      (1 - (k : ℝ) / 5) * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖
          ≤ (1 - (k : ℝ) / 5) * (∏ i : Fin k, ‖(w i : ℝᵈ)‖) :=
            mul_le_mul_of_nonneg_left hle h1m
      _ = (∏ i : Fin k, ‖(w i : ℝᵈ)‖) * (1 - (k : ℝ) / 5) := by rw [mul_comm]
      _ ≤ ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ := hlower
  · -- π₀ wedge ≤ wedge : projection cannot increase the norm
    exact Submission.WedgeContract.norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
  · -- log upper
    have hv0 : ∀ i : Fin k, 0 < ‖(w i : ℝᵈ)‖ := by
      intro i
      have hCpos : 0 < (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) :=
        mul_pos (by exact_mod_cast hℓ0) (Real.exp_pos _)
      have hann : (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(w i : ℝᵈ)‖ :=
        (hwann i).2.1
      have h10 : 0 < (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by nlinarith
      exact lt_of_lt_of_le h10 hann
    have hprod0 : 0 < (∏ i : Fin k, ‖(w i : ℝᵈ)‖) :=
      Finset.prod_pos (fun i hi => hv0 i)
    have h1mp : 0 < 1 - (k : ℝ) / 5 := by
      have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
      nlinarith
    have hlower0 := Submission.WedgeContract.wedgeContract_blockAnnulus_lower (d := d) (k := k)
      ℓ (le_of_lt hℓd) (a := Real.exp (-t / (ℓ : ℝ)))
      (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) (Real.exp_pos _) hℓ0 u hu_mem huON hk0 w hwann
    have hpi0pos : 0 < ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ :=
      lt_of_lt_of_le (mul_pos hprod0 h1mp) hlower0
    have hpi0le := Submission.WedgeContract.norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
    have hwedgepos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ :=
      lt_of_lt_of_le hpi0pos hpi0le
    have hstep1 := log_wedge_le_sum_log (E := ℝᵈ) k (fun i : Fin k => (w i : ℝᵈ)) hv0 hwedgepos
    have hlo : ∀ i : Fin k, (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(w i : ℝᵈ)‖ := by
      intro i
      exact (hwann i).2.1
    have hhi : ∀ i : Fin k, ‖(w i : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
      intro i
      exact (hwann i).2.2
    have hint := Submission.WedgeContract.wedgeContract_blockAnnulus_log_exp_interval (d := d)
      (k := k) ℓ hℓd hℓ0 (t := t) w hlo hhi
    exact le_trans hstep1 hint.2

/-- **Prop 5 in the model (lifted to the full flow lattice)**: the annulus family of
`prop5_model_contracting` lies in the contracting sublattice `smallFlow ≤ flowLattice`, so
its ambient values give vectors `v : Fin k → a_t ℤᵈ` of the full flow lattice with the same
`π₀`-control and log upper bound. -/
theorem prop5_model_lift {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (u : Fin k → ℝᵈ) (hu_mem : ∀ i : Fin k, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) :
    ∃ v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      (1 - (k : ℝ) / 5) * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ ∧
        ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ ≤
          ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ∧
        Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
  classical
  rcases prop5_model_contracting (d := d) hℓ0 hℓd (t := t) hk1 hk4 u hu_mem huON
    with ⟨w, hlow, hup, hlog⟩
  let v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ := fun i =>
    ⟨(w i : ℝᵈ), (Submission.BlockMinima.smallFlow_le_flowLattice (d := d)
      (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd)) (w i).2⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · simpa [v] using hlow
  · simpa [v] using hup
  · simpa [v] using hlog


/-! ### Chaining to the polygon slope sums (Prop-5 log bound in polygon form)

The model's contracting block has log-scale `−t/ℓ` per direction: the polygon drop
`c(k) − c(0) = −t·(k/ℓ)` equals the first-`k` slope sum `Σᵢ log(e^{−t/ℓ})`
(`Submission.WedgeContract.wedgeContract_firstBlock_slope_sum`,
`Submission.ContractPolygon`).  Chaining the `prop5_model_lift` log upper through that
drop makes the exponent's `t`-coefficient explicit:

* `vee_drop_contracting` — for `k ≤ ℓ`, `modelVeePolygon t d ℓ k − modelVeePolygon t d ℓ 0 =
  −t·(k/ℓ)` (the contracting segment of the V-polygon);
* **`prop5_model_log_upper_polygon`** — Prop 5 in the model with the π₀ two-sided control
  AND the log bound in polygon form:
  `log‖ιMulti v‖ ≤ k·log(12·(ℓ:ℝ)) + (c(k) − c(0))`;
* `prop5_model_log_upper_slope` — the slope-sum form of the same bound
  (`log‖ιMulti v‖ ≤ k·log(12·(ℓ:ℝ)) + Σᵢ log(e^{−t/ℓ})`), ready for the height/★ chase
  (`H ≲ e^{t·k/ℓ}`).
-/

/-- The V-polygon drops by `−t·(k/ℓ)` on its contracting segment: for `k ≤ ℓ`,
`modelVeePolygon t d ℓ k − modelVeePolygon t d ℓ 0 = −t·(k/ℓ)`. -/
lemma vee_drop_contracting {t : ℝ} (d ℓ : ℕ) {k : ℕ} (hkl : k ≤ ℓ) :
    Submission.ContractPolygon.modelVeePolygon t d ℓ k -
      Submission.ContractPolygon.modelVeePolygon t d ℓ 0 = -(t * ((k : ℝ) / (ℓ : ℝ))) := by
  have hv := Submission.ContractPolygon.modelVeePolygon_eq_contractPolygon t d ℓ hkl
  have h0 := Submission.ContractPolygon.modelVeePolygon_zero t d ℓ
  rw [hv, h0]
  unfold Submission.ContractPolygon.modelContractPolygon
  ring

/-- **Prop 5 in the model (polygon-slope log bound)**: the `prop5_model_lift` annulus
family `v : Fin k → a_t ℤᵈ` additionally satisfies the log bound in polygon form
`log‖ιMulti v‖ ≤ k·log(12·(ℓ:ℝ)) + (c(k) − c(0))` with `c = modelVeePolygon t d ℓ` (whose
drop `c(k) − c(0) = −t·(k/ℓ)` is the first-`k` slope sum of the contracting segment). -/
theorem prop5_model_log_upper_polygon {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hkl : k ≤ ℓ)
    (u : Fin k → ℝᵈ) (hu_mem : ∀ i : Fin k, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) :
    ∃ v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      (1 - (k : ℝ) / 5) * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ ∧
        ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ ≤
          ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ∧
        Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) +
            (Submission.ContractPolygon.modelVeePolygon t d ℓ k -
              Submission.ContractPolygon.modelVeePolygon t d ℓ 0) := by
  classical
  rcases prop5_model_lift (d := d) hℓ0 hℓd (t := t) hk1 hk4 u hu_mem huON
    with ⟨v, hlow, hup, hlog⟩
  refine ⟨v, hlow, hup, ?_⟩
  have hdrop := vee_drop_contracting (t := t) d ℓ hkl
  have heq : (k : ℝ) * (t / (ℓ : ℝ)) = t * ((k : ℝ) / (ℓ : ℝ)) := by
    rw [div_eq_mul_inv]
    ring
  calc
    Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
        ≤ (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := hlog
    _ = (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) + -(t * ((k : ℝ) / (ℓ : ℝ))) := by
          rw [heq]
          ring
    _ = (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) +
          (Submission.ContractPolygon.modelVeePolygon t d ℓ k -
            Submission.ContractPolygon.modelVeePolygon t d ℓ 0) := by
          rw [← hdrop]

/-- **Prop 5 in the model (slope-sum log bound)**: the polygon drop is the first-`k` slope
sum `Σᵢ log(e^{−t/ℓ})`, so `log‖ιMulti v‖ ≤ k·log(12·(ℓ:ℝ)) + Σᵢ log(e^{−t/ℓ})` — the
bound Prop 5 hands to the height/★ chase (exponent `t·(k/ℓ)`). -/
theorem prop5_model_log_upper_slope {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hkl : k ≤ ℓ)
    (u : Fin k → ℝᵈ) (hu_mem : ∀ i : Fin k, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) :
    ∃ v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      (1 - (k : ℝ) / 5) * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          ‖Submission.WedgeContract.pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ ∧
        Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
          (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) +
            (∑ _ : Fin k, Real.log (Real.exp (-t / (ℓ : ℝ)))) := by
  classical
  rcases prop5_model_log_upper_polygon (d := d) hℓ0 hℓd (t := t) hk1 hk4 hkl u hu_mem huON
    with ⟨v, hlow, hup, hlog⟩
  refine ⟨v, hlow, ?_⟩
  have hsum := Submission.WedgeContract.wedgeContract_firstBlock_slope_sum (ℓ := ℓ) (t := t)
    (k := k)
  have hdrop := vee_drop_contracting (t := t) d ℓ hkl
  calc
    Real.log ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
        ≤ (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) +
            (Submission.ContractPolygon.modelVeePolygon t d ℓ k -
              Submission.ContractPolygon.modelVeePolygon t d ℓ 0) := hlog
    _ = (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) + -(t * ((k : ℝ) / (ℓ : ℝ))) := by
          rw [hdrop]
    _ = (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) +
          (∑ _ : Fin k, Real.log (Real.exp (-t / (ℓ : ℝ)))) := by
          rw [← hsum]

end Submission.Prop5Model
