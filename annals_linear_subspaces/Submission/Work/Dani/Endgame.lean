import Submission.Work.Lattice.FlowRate

/-!
# Prop 1 part 2: the block endgame of the Dani correspondence

Coordinate model `ℝᵈ = EuclideanSpace ℝ (Fin d)`, `L = modelX ℓ` and `w ∈ ⋀^k ℝᵈ`; the *blocks*
`blockElem w u` (`Submission.ExteriorCoordinates`) are the components with `u` factors in `Lᗮ`.
The exponential two-scale flow `a_t` (`eFlow d ℓ t`) contracts `L` by `e^{-t/ℓ}` and expands `Lᗮ`
by `e^{t/(d-ℓ)}`; block `u` of a `k`-vector is an eigenvector with eigenvalue `exp (t * σ_u)`,
`σ_u = -(k-u)/ℓ + u/(d-ℓ)`.

This module formalises the analytic core of de Saxcé's Proposition 1, part 2: from the
**`π₊`-dominance hypothesis** "the `L`-block (`u = 0`) of the flowed vector dominates its norm"
one deduces

* every block of the *unflowed* vector is exponentially small compared with block `0`:
  `‖blockElem w u‖ ≤ c⁻¹ * exp (-(t * (u * S))) * ‖blockElem w 0‖`, `S = 1/ℓ + 1/(d-ℓ)`;
* in particular `‖blockElem w 1‖ ≤ c⁻¹ * exp (-(t * S)) * ‖blockElem w 0‖` — the estimate that
  becomes the *distance* bound `d (plane w) L ≲ e^{-tS}` via Lemma 1;
* the **height bound** `‖w‖ ≤ (k+1) * c⁻¹ * exp (t * k/ℓ) * ‖a_t w‖` (the metric core of
  `H (v) ≲ e^{t k/ℓ} ‖a_t s_x v‖`).

All declarations are Mathlib plus `Submission.GeometryOfNumbers.{ExteriorCoordinates,
DiagonalFlow}` and `Submission.Work.Lattice.FlowRate`.
-/

noncomputable section

open Module exteriorPower
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Submission.DaniEndgame

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowRate

variable {d : ℕ}

/-- Logarithmic eigenvalue `σ_u = -(k-u)/ℓ + u/(d-ℓ)` of block `u` of the exponential
two-scale flow on `⋀^k ℝᵈ`. -/
def sig (d k ℓ u : ℕ) : ℝ := -(((k - u : ℕ) : ℝ) / ↑ℓ) + ((u : ℝ) / ↑(d - ℓ))

/-- The exponential rate `S = 1/ℓ + 1/(d-ℓ)`: `σ_u - σ_v = (u - v) * S`. -/
def rate (d ℓ : ℕ) : ℝ := 1 / ↑ℓ + 1 / ↑(d - ℓ)

lemma sig_zero (d k ℓ : ℕ) : sig d k ℓ 0 = -(((k : ℕ) : ℝ) / ↑ℓ) := by
  simp [sig]

lemma rate_pos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) : 0 < rate d ℓ := by
  have h1 : (0 : ℝ) < ↑ℓ := by exact_mod_cast hℓ0
  have h2 : (0 : ℝ) < ↑(d - ℓ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  simp only [rate]
  positivity

lemma sig_sub_sig_zero {k ℓ : ℕ} {u : ℕ} (hu : u ≤ k) :
    sig d k ℓ u - sig d k ℓ 0 = (u : ℝ) * rate d ℓ := by
  have hku : (((k - u : ℕ) : ℝ)) = (k : ℝ) - (u : ℝ) := by
    rw [Nat.cast_sub hu]
  simp only [sig, rate, hku, Nat.sub_zero]
  ring

/-- The exponential two-scale flow `a_t` on `ℝᵈ`. -/
def eFlow (d ℓ : ℕ) (t : ℝ) : RD d →ₗ[ℝ] RD d :=
  scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)

/-- The flow action on `k`-vectors. -/
def eFlowK (d ℓ k : ℕ) (t : ℝ) : WK d k →ₗ[ℝ] WK d k :=
  exteriorPower.map k (eFlow d ℓ t)

/-- **Block eigenvector identity** for the exponential flow. -/
theorem blockElem_eFlowK {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (w : WK d k)
    {u : ℕ} (hu : u ≤ k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) u =
      Real.exp (t * sig d k ℓ u) • blockElem (d := d) (k := k) (ℓ := ℓ) w u := by
  rw [eFlowK, eFlow, blockElem_map_scaleMap_twoScale (d := d) (k := k) (ℓ := ℓ) _ _ w hu]
  simp only [sig]
  rw [← eigen_exp (d := d) (k := k) (u := u) (ℓ := ℓ) hℓ0 hℓd t]

/-- **Norm form** of the block eigenvector identity. -/
theorem norm_blockElem_eFlowK {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (w : WK d k)
    {u : ℕ} (hu : u ≤ k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) u‖ =
      Real.exp (t * sig d k ℓ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ := by
  rw [blockElem_eFlowK (d := d) (hℓ0 := hℓ0) (hℓd := hℓd) t w hu, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- The **`π₊`-dominance hypothesis**: the `L`-block of the flowed vector dominates its norm. -/
def Dominates (d ℓ k : ℕ) (t c : ℝ) (w : WK d k) : Prop :=
  c * ‖eFlowK d ℓ k t w‖ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) 0‖

/-- **The blocks of the unflowed vector are exponentially small compared with block `0`.**
This is the block-level content of "`‖π₊(a_t v)‖ ≥ c ‖a_t v‖` forces `v` to be a graph with a
contracting graph map", and yields both the distance bound (`u = 1`) and the height bound. -/
theorem block_le_of_dominated {k ℓ u : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    {t c : ℝ} (hc : 0 < c) {w : WK d k} (hdom : Dominates d ℓ k t c w) (hu : u ≤ k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
      c⁻¹ * Real.exp (-(t * ((u : ℝ) * rate d ℓ))) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
  set B : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ with hB
  have hnorm : ‖eFlowK d ℓ k t w‖ ≤
      c⁻¹ * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) 0‖ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    have h : c * ‖eFlowK d ℓ k t w‖ ≤
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) 0‖ := hdom
    rw [mul_comm c (‖eFlowK d ℓ k t w‖)] at h
    exact h
  have hstep : Real.exp (t * sig d k ℓ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
      c⁻¹ * (Real.exp (t * sig d k ℓ 0) * B) := by
    have h0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) u‖ ≤
        c⁻¹ * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) 0‖ :=
      le_trans (norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) hu) hnorm
    rw [norm_blockElem_eFlowK (d := d) (hℓ0 := hℓ0) (hℓd := hℓd) t w hu,
      norm_blockElem_eFlowK (d := d) (hℓ0 := hℓ0) (hℓd := hℓd) t w (Nat.zero_le k), ← hB] at h0
    exact h0
  have hstep' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ * Real.exp (t * sig d k ℓ u) ≤
      c⁻¹ * (Real.exp (t * sig d k ℓ 0) * B) := by
    rw [mul_comm]; exact hstep
  have hpos : 0 < Real.exp (t * sig d k ℓ u) := Real.exp_pos _
  have hkey : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
      c⁻¹ * (Real.exp (t * sig d k ℓ 0) * B) / Real.exp (t * sig d k ℓ u) :=
    (le_div_iff₀ hpos).mpr hstep'
  refine hkey.trans (le_of_eq ?_)
  have hexp : t * sig d k ℓ 0 + -(t * sig d k ℓ u) = -(t * ((u : ℝ) * rate d ℓ)) := by
    have h := sig_sub_sig_zero (d := d) (k := k) (ℓ := ℓ) (u := u) hu
    rw [← h]; ring
  have hrew : c⁻¹ * (Real.exp (t * sig d k ℓ 0) * B) / Real.exp (t * sig d k ℓ u) =
      c⁻¹ * (Real.exp (t * sig d k ℓ 0) * Real.exp (-(t * sig d k ℓ u))) * B := by
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    ring
  rw [hrew, ← Real.exp_add, hexp]

/-- Specialisation of `block_le_of_dominated` to block `1`: the **distance bound**. -/
theorem ratio_one_le {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : 1 ≤ k)
    {t c : ℝ} (hc : 0 < c) {w : WK d k} (hdom : Dominates d ℓ k t c w) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ ≤
      c⁻¹ * Real.exp (-(t * rate d ℓ)) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
  have h := block_le_of_dominated (d := d) (k := k) (ℓ := ℓ) (u := 1) hℓ0 hℓd hc hdom hk
  simpa using h

/-- **The height bound**: `‖w‖ ≤ (k+1) * c⁻¹ * exp (t k/ℓ) * ‖a_t w‖` under `π₊`-dominance. -/
theorem norm_le_of_dominated {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : 0 < k)
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) {w : WK d k} (hdom : Dominates d ℓ k t c w) :
    ‖w‖ ≤ ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / ↑ℓ) * ‖eFlowK d ℓ k t w‖ := by
  have hS : 0 ≤ rate d ℓ := le_of_lt (rate_pos (d := d) hℓ0 hℓd)
  have hb : ∀ u ∈ Finset.range (k + 1),
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
        c⁻¹ * Real.exp (-(t * ((u : ℝ) * rate d ℓ))) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    intro u hu
    exact block_le_of_dominated (d := d) (k := k) (ℓ := ℓ) (u := u) hℓ0 hℓd hc hdom
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
  have hsum : (Finset.range (k + 1)).sum (fun u : ℕ =>
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖) ≤
        ((k : ℝ) + 1) * (c⁻¹ * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) := by
    calc (Finset.range (k + 1)).sum (fun u : ℕ =>
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖)
        ≤ (Finset.range (k + 1)).sum (fun u : ℕ =>
            c⁻¹ * Real.exp (-(t * ((u : ℝ) * rate d ℓ))) *
              ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) := Finset.sum_le_sum hb
      _ = c⁻¹ * ((Finset.range (k + 1)).sum (fun u : ℕ =>
            Real.exp (-(t * ((u : ℝ) * rate d ℓ))))) *
              ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ c⁻¹ * ((k : ℝ) + 1) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
            have hle1 : ∀ u ∈ Finset.range (k + 1),
                Real.exp (-(t * ((u : ℝ) * rate d ℓ))) ≤ 1 := by
              intro u hu
              rw [Real.exp_le_one_iff]
              have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
              nlinarith [mul_nonneg hu0 hS, ht]
            have hsum1 : (Finset.range (k + 1)).sum (fun u : ℕ =>
                Real.exp (-(t * ((u : ℝ) * rate d ℓ)))) ≤ (k : ℝ) + 1 := by
              have h1 := Finset.sum_le_sum hle1
              rw [Finset.sum_const, Finset.card_range] at h1
              simpa using h1
            have hc0 : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
            have hB : 0 ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum1 hc0) hB
      _ = ((k : ℝ) + 1) * (c⁻¹ * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) := by ring
  have hB : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ =
      Real.exp (t * (k : ℝ) / ↑ℓ) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) 0‖ := by
    rw [norm_blockElem_eFlowK (d := d) (hℓ0 := hℓ0) (hℓd := hℓd) t w (Nat.zero_le k)]
    rw [sig_zero]
    rw [show t * (-((k : ℝ) / ↑ℓ)) = -(t * (k : ℝ) / ↑ℓ) by ring, Real.exp_neg]
    field_simp
  have hBle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≤
      Real.exp (t * (k : ℝ) / ↑ℓ) * ‖eFlowK d ℓ k t w‖ := by
    rw [hB]
    exact mul_le_mul_of_nonneg_left
      (norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) (eFlowK d ℓ k t w) (Nat.zero_le k))
      (le_of_lt (Real.exp_pos _))
  have hdec : (Finset.range (k + 1)).sum (fun u : ℕ =>
      blockElem (d := d) (k := k) (ℓ := ℓ) w u) = w := sum_blockElem (d := d) (k := k) w
  calc ‖w‖ = ‖(Finset.range (k + 1)).sum (fun u : ℕ =>
        blockElem (d := d) (k := k) (ℓ := ℓ) w u)‖ := by rw [hdec]
    _ ≤ (Finset.range (k + 1)).sum (fun u : ℕ =>
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖) := norm_sum_le _ _
    _ ≤ ((k : ℝ) + 1) * (c⁻¹ * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) := hsum
    _ ≤ ((k : ℝ) + 1) * (c⁻¹ * (Real.exp (t * (k : ℝ) / ↑ℓ) * ‖eFlowK d ℓ k t w‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBle (le_of_lt (inv_pos.mpr hc)))
          (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    _ = ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / ↑ℓ) * ‖eFlowK d ℓ k t w‖ := by ring

end Submission.DaniEndgame
