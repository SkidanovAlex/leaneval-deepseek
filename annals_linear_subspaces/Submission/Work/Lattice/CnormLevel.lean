import Mathlib
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.FlowDataMax
import Submission.Work.Lattice.FlowDataShift

/-!
# The max-norm level function of a wedge, and its one-sided flow bound

For the §3 accounting (`Submission.AccountingOneSided`) the relevant framework is the **max
norm** `cnorm` of `Submission.MaxNorm`: with it, the level function of a wedge,

  `L_w(t) := log cnorm (⋀^j a_t (⋀ v))`,

is a *max of exponentials* `max_u e^{tσ_u}·cnorm_u(w)` (`MaxNorm.cnorm_map_flow`), so everything is
exactly piecewise affine, with slopes the block eigenvalues `σ_u`.  This module records the
resulting **one-sided level bound**:

* `cnorm_blockElem_le_cnorm` — `cnorm` of a block is at most `cnorm` of the vector;
* **`cnorm_map_eFlow_le_exp_top`** — for `h ≥ 0` and `u = topBlockIndex ℓ w`,
  `cnorm (⋀^k a_h w) ≤ e^{h·sig k ℓ u}·cnorm w` (the max-norm analogue of
  `Submission.FlowRateUniform.norm_map_twoScale_le_eigen_top`, and the sharp statement: the
  sup of `e^{hσ_u}cnorm_u` is attained at the *top* block);
* **`log_cnorm_eFlow_le`** — the log form: `log cnorm (⋀^j a_{t+h}(⋀v)) ≤
  log cnorm (⋀^j a_t(⋀v)) + h·σ_{u₀}`, `u₀ = topBlockIndex` of the time-`t` wedge.

The last is the *level* (not derivative) inequality consumed by the accounting: it says that for
the flowed lattice `Λ_t = a_t Λ₀` and a flag member `V_t ≤ Λ_t`,

  `flowMaxData(t+h, j) ≤ log cnorm (⋀^j a_h w_t) ≤ flowMaxData(t, j) + h·σ_{u₀}(w_t)`,

i.e. the level derivative `r := (d/dt) flowMaxData` satisfies `r ≤ σ_{u₀}` where `u₀` is the
argmax block of the *minimising* member's wedge.  (The reverse inequality — the one the
accounting needs to identify the effective capacity `effPos` with the number of directions the
member can supply — needs the *continuity/piecewise affinity* of `t ↦ flowMaxData(t, j)`, which
follows from the per-family eventual affinity `FlowDataMax.eventually_log_cnorm_eFlow_iMulti_eq`
plus the finiteness of the bounded-covolume spectrum; that is the next step.)

Module `Submission.Work.Lattice.CnormLevel`, namespace `Submission.CnormLevel`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRate
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax

namespace Submission.CnormLevel

variable {d : ℕ}

/-- `cnorm` of a block is at most `cnorm` of the vector. -/
lemma cnorm_blockElem_le_cnorm {k ℓ u : ℕ} (hk : k ≤ d) (w : WK d k) :
    cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≤ cnorm hk w := by
  refine cnorm_le_of_forall hk _ (fun I => ?_)
  rw [wcoord_blockElem]
  by_cases hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) u
  · rw [if_pos hI]
    exact le_cnorm hk w I
  · rw [if_neg hI, abs_zero]
    exact cnorm_nonneg hk w

/-- **The sharp max-norm flow bound**: the sup norm of the flowed `k`-vector is at most the
eigenvalue of its *top* block times the sup norm of the vector, for `h ≥ 0`. -/
theorem cnorm_map_eFlow_le_exp_top {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk : k ≤ d)
    {h : ℝ} (hh : 0 ≤ h) (w : WK d k) :
    cnorm hk (exteriorPower.map k (eFlow (d := d) ℓ h) w) ≤
      Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) * cnorm hk w := by
  classical
  rw [eFlow_eq, cnorm_map_flow (d := d) hℓ0 hℓd h hk w]
  refine Finset.sup'_le _ _ (fun u hu => ?_)
  have huk : u ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
  by_cases hle : u ≤ topBlockIndex (d := d) ℓ w
  · have hsig : sig (d := d) k ℓ u ≤ sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w) :=
      sig_mono (d := d) hℓ0 hℓd hle
    have hexp : Real.exp (h * sig (d := d) k ℓ u) ≤
        Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsig hh)
    calc Real.exp (h * sig (d := d) k ℓ u) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)
        ≤ Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) *
            cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) :=
          mul_le_mul_of_nonneg_right hexp (cnorm_nonneg hk _)
      _ ≤ Real.exp (h * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) * cnorm hk w :=
          mul_le_mul_of_nonneg_left (cnorm_blockElem_le_cnorm hk w)
            (le_of_lt (Real.exp_pos _))
  · have hlt : topBlockIndex (d := d) ℓ w < u := lt_of_not_ge hle
    have hz : blockElem (d := d) (k := k) (ℓ := ℓ) w u = 0 :=
      blockElem_eq_zero_of_topBlockIndex_lt (d := d) (ℓ := ℓ) w hlt huk
    rw [hz, cnorm_zero, mul_zero]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (cnorm_nonneg hk w)

/-- **The one-sided level bound** (log form): for `h ≥ 0`, the level function of the flowed
wedge at time `t + h` is bounded by the level at time `t` plus `h` times the top-block
eigenvalue of the time-`t` wedge. -/
theorem log_cnorm_eFlow_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d) {t h : ℝ}
    (hh : 0 ≤ h) {v : Fin j → RD d} (hv : LinearIndependent ℝ v) :
    Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
        (exteriorPower.ιMulti ℝ j v))) ≤
      Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t)
          (exteriorPower.ιMulti ℝ j v))) +
        h * sig (d := d) j ℓ (topBlockIndex (d := d) ℓ
          (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v))) := by
  set w : WK d j := exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)
    with hwdef
  have hw : w ≠ 0 := map_eFlow_iMulti_ne_zero (d := d) (ℓ := ℓ) t hv
  have hposw : 0 < cnorm hjd w := cnorm_pos_of_ne_zero hjd _ hw
  have hflowne : exteriorPower.map j (eFlow (d := d) ℓ h) w ≠ 0 := by
    rw [hwdef, ← Submission.FlowDataShift.eFlow_iMulti_add (d := d) (j := j) (ℓ := ℓ) t h v]
    exact map_eFlow_iMulti_ne_zero (d := d) (ℓ := ℓ) (t + h) hv
  have hpos' : 0 < cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ h) w) :=
    cnorm_pos_of_ne_zero hjd _ hflowne
  rw [Submission.FlowDataShift.eFlow_iMulti_add]
  have hbound := cnorm_map_eFlow_le_exp_top (d := d) (k := j) (ℓ := ℓ) hℓ0 hℓd hjd hh w
  calc Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ h) w))
      ≤ Real.log (Real.exp (h * sig (d := d) j ℓ (topBlockIndex (d := d) ℓ w)) * cnorm hjd w) :=
        Real.log_le_log hpos' hbound
    _ = h * sig (d := d) j ℓ (topBlockIndex (d := d) ℓ w) + Real.log (cnorm hjd w) := by
        rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hposw), Real.log_exp]
    _ = Real.log (cnorm hjd w) + h * sig (d := d) j ℓ (topBlockIndex (d := d) ℓ w) := by ring

/-! ## The block-partition identity and the Lipschitz bounds for the max-norm data

The sup norm is the maximum of the sup norms of the blocks (the blocks partition the
coordinates), which turns `cnorm_map_flow` into a two-sided level bound:

* `cnorm_eq_sup'_blockElem` — `cnorm w = sup'_u cnorm (block_u w)`;
* `cnorm_exp_neg_le` — `e^{−h·j/ℓ}·cnorm w ≤ cnorm (⋀^j a_h w)` (`h ≥ 0`, `j ≤ d`);
* `log_cnorm_eFlow_le_shift` / `log_cnorm_eFlow_ge_shift` — the per-family Lipschitz bounds
  `log cnorm (⋀^j a_{t+h}(⋀v)) ≤ log cnorm (⋀^j a_t(⋀v)) + h·j/(d−ℓ)` and
  `≥ log cnorm (⋀^j a_t(⋀v)) − h·j/ℓ`;
* **`flowMaxData_shift_le` / `flowMaxData_shift_ge`** — the same for the max-norm data function
  `flowMaxData` (max-norm analogue of `FlowDataShift.flowEuclidData_shift_le/ge`): the max-norm
  Grayson polygon of the flow is Lipschitz in `t`, hence continuous — the continuity input of
  the time-selection argument for the *correct* (max-norm) framework.
-/

/-- The sup norm is the maximum of the sup norms of the blocks. -/
lemma cnorm_eq_sup'_blockElem {k ℓ : ℕ} (hk : k ≤ d) (w : WK d k) :
    cnorm hk w = (Finset.range (k + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
      (fun u => cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
  refine le_antisymm ?_ ?_
  · refine cnorm_le_of_forall hk w (fun I => ?_)
    have hIle : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≤ k :=
      card_filter_high_le I
    have hIrange : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ∈
        Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hIle)
    have hmem : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ)
        ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by simp [blockFinset]
    have h1 : wcoord (d := d) (k := k) (blockElem (d := d) (k := k) (ℓ := ℓ) w
        ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) I =
        wcoord (d := d) (k := k) w I := by rw [wcoord_blockElem, if_pos hmem]
    calc |wcoord (d := d) (k := k) w I|
        = |wcoord (d := d) (k := k) (blockElem (d := d) (k := k) (ℓ := ℓ) w
            ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) I| := by rw [h1]
      _ ≤ cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w
            ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) :=
          le_cnorm hk _ I
      _ ≤ _ := Finset.le_sup'
            (f := fun u => cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) hIrange
  · refine Finset.sup'_le _ _ (fun u _ => cnorm_blockElem_le_cnorm hk w)

/-- The `ℓ`-contraction bound: for `h ≥ 0`, `e^{−h·j/ℓ}·cnorm w ≤ cnorm (⋀^j a_h w)`. -/
lemma cnorm_exp_neg_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d) {h : ℝ}
    (hh : 0 ≤ h) (w : WK d j) :
    Real.exp (-(h * (j : ℝ) / (ℓ : ℝ))) * cnorm hjd w ≤
      cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ h) w) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  -- the exponent bound at every block index
  have hexp : ∀ u ∈ Finset.range (j + 1),
      Real.exp (-(h * (j : ℝ) / (ℓ : ℝ))) ≤ Real.exp (h * sig (d := d) j ℓ u) := by
    intro u hu
    have huk : u ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    rw [Real.exp_le_exp]
    have hsig : -(j : ℝ) / (ℓ : ℝ) ≤ sig (d := d) j ℓ u := by
      have h := sig_mono (d := d) hℓ0 hℓd (k := j) (Nat.zero_le u)
      have h0 : sig (d := d) j ℓ 0 = -(j : ℝ) / (ℓ : ℝ) := by
        have hsl : slope (d := d) ℓ = 1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ)) := rfl
        rw [sig, hsl]
        ring
      rwa [h0] at h
    have h1 : -(h * (j : ℝ) / (ℓ : ℝ)) = h * (-(j : ℝ) / (ℓ : ℝ)) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hsig hh
  rw [eFlow_eq, cnorm_map_flow (d := d) hℓ0 hℓd h hjd w, cnorm_eq_sup'_blockElem hjd w]
  obtain ⟨u0, hu0mem, hu0eq⟩ := Finset.exists_mem_eq_sup'
    (⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ : (Finset.range (j + 1)).Nonempty)
    (fun u => cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) w u))
  rw [hu0eq]
  refine le_trans (mul_le_mul_of_nonneg_right (hexp u0 hu0mem) (cnorm_nonneg hjd _)) ?_
  exact Finset.le_sup'
    (f := fun u => Real.exp (h * sig (d := d) j ℓ u) *
      cnorm hjd (blockElem (d := d) (k := j) (ℓ := ℓ) w u)) hu0mem

/-- `sig` at the full block index is the maximal flow rate `j/(d−ℓ)`. -/
lemma sig_self {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) :
    sig (d := d) j ℓ j = (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (((d - ℓ : ℕ)) : ℝ) = (d : ℝ) - (ℓ : ℝ) := Nat.cast_sub (le_of_lt hℓd)
  have hd' : (d : ℝ) - (ℓ : ℝ) ≠ 0 := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hsl : slope (d := d) ℓ = 1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ)) := rfl
  rw [sig, hsl, hdmR]
  field_simp
  ring

/-- **The per-family Lipschitz upper bound** for the max-norm level of the flowed wedge. -/
theorem log_cnorm_eFlow_le_shift {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    {t h : ℝ} (hh : 0 ≤ h) {v : Fin j → RD d} (hv : LinearIndependent ℝ v) :
    Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
        (exteriorPower.ιMulti ℝ j v))) ≤
      Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t)
        (exteriorPower.ιMulti ℝ j v))) + h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
  have h1 := log_cnorm_eFlow_le (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd (t := t) hh hv
  have hsig : sig (d := d) j ℓ (topBlockIndex (d := d) ℓ
      (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v))) ≤
      (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
    rw [← sig_self (d := d) (j := j) hℓ0 hℓd]
    exact sig_mono (d := d) hℓ0 hℓd (topBlockIndex_le (d := d) ℓ _)
  have hthis := mul_le_mul_of_nonneg_left hsig hh
  have hrw : h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) = h * ((j : ℝ) / ((d - ℓ : ℕ) : ℝ)) := by ring
  rw [hrw]
  linarith [h1, hthis]

/-- **The per-family Lipschitz lower bound** for the max-norm level of the flowed wedge. -/
theorem log_cnorm_eFlow_ge_shift {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    {t h : ℝ} (hh : 0 ≤ h) {v : Fin j → RD d} (hv : LinearIndependent ℝ v) :
    Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ t)
        (exteriorPower.ιMulti ℝ j v))) - h * (j : ℝ) / (ℓ : ℝ) ≤
      Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
        (exteriorPower.ιMulti ℝ j v))) := by
  set w : WK d j := exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)
    with hwdef
  have hw : w ≠ 0 := map_eFlow_iMulti_ne_zero (d := d) (ℓ := ℓ) t hv
  have hposw : 0 < cnorm hjd w := cnorm_pos_of_ne_zero hjd _ hw
  have hflowne : exteriorPower.map j (eFlow (d := d) ℓ h) w ≠ 0 := by
    rw [hwdef, ← Submission.FlowDataShift.eFlow_iMulti_add (d := d) (j := j) (ℓ := ℓ) t h v]
    exact map_eFlow_iMulti_ne_zero (d := d) (ℓ := ℓ) (t + h) hv
  have hpos' : 0 < cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ h) w) :=
    cnorm_pos_of_ne_zero hjd _ hflowne
  rw [Submission.FlowDataShift.eFlow_iMulti_add]
  have hlow := cnorm_exp_neg_le (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hh w
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hposw) hlow
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hposw), Real.log_exp] at hlog
  linarith [hlog]

/-- **The max-norm data is Lipschitz in the time (upper bound).** -/
theorem flowMaxData_shift_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (Λ₀ : Submodule ℤ (RD d)) (hbd : ∀ t : ℝ, BddBelow (flowMaxDataSet Λ₀ ℓ t j hjd))
    {t h : ℝ} (hh : 0 ≤ h) :
    flowMaxData Λ₀ ℓ (t + h) j hjd ≤
      flowMaxData Λ₀ ℓ t j hjd + h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
  have hC : 0 ≤ h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
    have hdmR : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hℓd)]
      have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
      linarith
    positivity
  have hset : ∀ s : ℝ, {r | ∃ v : Fin j → RD d,
        ((∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v) ∧
          r = Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ s)
            (exteriorPower.ιMulti ℝ j v)))} = flowMaxDataSet Λ₀ ℓ s j hjd := by
    intro s
    ext r
    constructor
    · rintro ⟨v, ⟨hv, hli⟩, rfl⟩
      exact ⟨v, hv, hli, rfl⟩
    · rintro ⟨v, hv, hli, rfl⟩
      exact ⟨v, ⟨hv, hli⟩, rfl⟩
  simp only [flowMaxData]
  rw [← hset (t + h), ← hset t]
  refine Submission.FlowDataShift.sInf_setOf_le_add hC ?_ ?_
  · intro v
    by_cases hX : exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v) = 0
    · rw [Submission.FlowDataShift.eFlow_iMulti_add, hX]
      simp only [map_zero, cnorm_zero, Real.log_zero]
      linarith
    · have hli : LinearIndependent ℝ v :=
        Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero v
          (fun hz => hX (by rw [hz, map_zero]))
      exact log_cnorm_eFlow_le_shift (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hh hli
  · rw [hset (t + h)]
    exact hbd (t + h)

/-- **The max-norm data is Lipschitz in the time (lower bound).** -/
theorem flowMaxData_shift_ge {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (Λ₀ : Submodule ℤ (RD d)) (hbd : ∀ t : ℝ, BddBelow (flowMaxDataSet Λ₀ ℓ t j hjd))
    {t h : ℝ} (hh : 0 ≤ h) :
    flowMaxData Λ₀ ℓ t j hjd ≤
      flowMaxData Λ₀ ℓ (t + h) j hjd + h * (j : ℝ) / (ℓ : ℝ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hC : 0 ≤ h * (j : ℝ) / (ℓ : ℝ) := by positivity
  have hset : ∀ s : ℝ, {r | ∃ v : Fin j → RD d,
        ((∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v) ∧
          r = Real.log (cnorm hjd (exteriorPower.map j (eFlow (d := d) ℓ s)
            (exteriorPower.ιMulti ℝ j v)))} = flowMaxDataSet Λ₀ ℓ s j hjd := by
    intro s
    ext r
    constructor
    · rintro ⟨v, ⟨hv, hli⟩, rfl⟩
      exact ⟨v, hv, hli, rfl⟩
    · rintro ⟨v, hv, hli, rfl⟩
      exact ⟨v, ⟨hv, hli⟩, rfl⟩
  simp only [flowMaxData]
  rw [← hset t, ← hset (t + h)]
  refine Submission.FlowDataShift.sInf_setOf_le_add hC ?_ ?_
  · intro v
    by_cases hX : exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v) = 0
    · rw [Submission.FlowDataShift.eFlow_iMulti_add, hX]
      simp only [map_zero, cnorm_zero, Real.log_zero]
      linarith
    · have hli : LinearIndependent ℝ v :=
        Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero v
          (fun hz => hX (by rw [hz, map_zero]))
      have hg := log_cnorm_eFlow_ge_shift (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd (t := t) hh hli
      linarith
  · rw [hset t]
    exact hbd t

/-- The max-norm data is Lipschitz in `t`. -/
theorem flowMaxData_lipschitz {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (Λ₀ : Submodule ℤ (RD d)) (hbd : ∀ t : ℝ, BddBelow (flowMaxDataSet Λ₀ ℓ t j hjd)) :
    ∀ s t : ℝ, |flowMaxData Λ₀ ℓ s j hjd - flowMaxData Λ₀ ℓ t j hjd| ≤
      ((j : ℝ) * max (1 / (ℓ : ℝ)) (1 / ((d - ℓ : ℕ) : ℝ))) * |s - t| := by
  intro s t
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  set L : ℝ := (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / ((d - ℓ : ℕ) : ℝ)) with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hLge1 : (j : ℝ) / ((d - ℓ : ℕ) : ℝ) ≤ L := by
    have h1 : (j : ℝ) * (1 / ((d - ℓ : ℕ) : ℝ)) ≤
        (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / ((d - ℓ : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_max_right (α := ℝ) _ _) hj0
    rw [hL, div_eq_mul_one_div]
    exact h1
  have hLge2 : (j : ℝ) / (ℓ : ℝ) ≤ L := by
    have h1 : (j : ℝ) * (1 / (ℓ : ℝ)) ≤
        (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / ((d - ℓ : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_max_left (α := ℝ) _ _) hj0
    rw [hL, div_eq_mul_one_div]
    exact h1
  have key : ∀ u v : ℝ, u ≤ v →
      flowMaxData Λ₀ ℓ v j hjd ≤ flowMaxData Λ₀ ℓ u j hjd + L * (v - u) ∧
      flowMaxData Λ₀ ℓ u j hjd ≤ flowMaxData Λ₀ ℓ v j hjd + L * (v - u) := by
    intro u v huv
    have huv0 : 0 ≤ v - u := by linarith
    have h2a : (v - u) * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) ≤ L * (v - u) := by
      rw [mul_div_assoc, mul_comm L (v - u)]
      exact mul_le_mul_of_nonneg_left hLge1 huv0
    have h2b : (v - u) * (j : ℝ) / (ℓ : ℝ) ≤ L * (v - u) := by
      rw [mul_div_assoc, mul_comm L (v - u)]
      exact mul_le_mul_of_nonneg_left hLge2 huv0
    constructor
    · have h1 := flowMaxData_shift_le (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd Λ₀ hbd
        (t := u) (h := v - u) huv0
      rw [show u + (v - u) = v by ring] at h1
      linarith
    · have h1 := flowMaxData_shift_ge (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd Λ₀ hbd
        (t := u) (h := v - u) huv0
      rw [show u + (v - u) = v by ring] at h1
      linarith
  rcases le_total t s with h | h
  · have hst : 0 ≤ s - t := by linarith
    have habs : |s - t| = s - t := abs_of_nonneg hst
    obtain ⟨h1, h2⟩ := key t s h
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · rw [habs]; linarith
    · rw [habs]; linarith
  · have hts : s - t ≤ 0 := by linarith
    have habs : |s - t| = t - s := by
      rw [abs_of_nonpos hts]
      ring
    obtain ⟨h1, h2⟩ := key s t h
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · rw [habs]; linarith
    · rw [habs]; linarith

/-- **The max-norm data along the flow is continuous in `t`** (the continuity input of the
time-selection argument, in the correct max-norm framework). -/
theorem continuous_flowMaxData {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hjd : j ≤ d)
    (Λ₀ : Submodule ℤ (RD d)) (hbd : ∀ t : ℝ, BddBelow (flowMaxDataSet Λ₀ ℓ t j hjd)) :
    Continuous fun t : ℝ => flowMaxData Λ₀ ℓ t j hjd := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  set L : ℝ := (j : ℝ) * max (1 / (ℓ : ℝ)) (1 / ((d - ℓ : ℕ) : ℝ)) with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  rw [Metric.continuous_iff]
  intro t ε hε
  refine ⟨ε / (L + 1), by positivity, fun s hs => ?_⟩
  have h1 := flowMaxData_lipschitz (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd Λ₀ hbd s t
  rw [Real.dist_eq] at hs ⊢
  have h2 : L * |s - t| ≤ L * (ε / (L + 1)) := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hs) hL0
  have h3 : L * (ε / (L + 1)) < ε := by
    have hL1 : 0 < L + 1 := by linarith
    rw [← mul_div_assoc, div_lt_iff₀ hL1]
    nlinarith
  linarith [h1, h2, h3]

end Submission.CnormLevel

end
