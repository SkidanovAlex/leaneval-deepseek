import Mathlib
import Submission.Work.Lattice.FlowDataMax
import Submission.Work.Lattice.MaxNormFlow

/-!
# The max-norm and Euclidean flow data differ by a bounded constant

The §3 Grayson polygon may be built with the paper's **sup norm** `cnorm` (`flowMaxData`) or with
the Euclidean norm (`flowEuclidData`); the two data functions differ by at most
`½ log (choose d j)` (the `A₂` norm-comparability constant, which is `0` only for `j ∈ {0, d}`).
This module proves

* `log_cnorm_le_log_norm` — `log (cnorm w) ≤ log ‖w‖`;
* `log_norm_le_log_cnorm_add` — `log ‖w‖ ≤ log (cnorm w) + ½ log (choose d j)`;
* `flowMaxData_le_flowEuclidData` and `flowEuclidData_le_flowMaxData_add` — the corresponding
  inequalities for the rank-`j` data of the flow.

Consequently the two Grayson polygons differ by at most `A₂(d) := max_{j ≤ d} ½log(choose d j)`,
so the `φ`-slack `A > 0` of the flag argument can absorb the norm change — this is the
"fallback" recorded in the roadmap (STATUS session 162 §3), which lets the Euclidean
`PhiFlag.exists_tight_flag` serve the max-norm accounting.

Module `Submission.Work.Lattice.MaxEuclidData`, namespace `Submission.MaxEuclidData`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowDataMax

namespace Submission.MaxEuclidData

variable {d : ℕ}

/-- The sup norm is at most the Euclidean norm, in logarithms. -/
lemma log_cnorm_le_log_norm {j : ℕ} (hjd : j ≤ d) (w : WK d j) :
    Real.log (cnorm (d := d) hjd w) ≤ Real.log ‖w‖ := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    rw [cnorm_zero, norm_zero]
  · have hcn : 0 < cnorm (d := d) hjd w := cnorm_pos_of_ne_zero hjd w hw
    exact Real.log_le_log hcn (cnorm_le_norm (d := d) hjd w)

/-- The Euclidean norm is at most the sup norm times `√(choose d j)`, in logarithms. -/
lemma log_norm_le_log_cnorm_add {j : ℕ} (hjd : j ≤ d) (w : WK d j) :
    Real.log ‖w‖ ≤ Real.log (cnorm (d := d) hjd w) +
      (1 / 2) * Real.log (Nat.choose d j : ℝ) := by
  have hch : 0 < Nat.choose d j := Nat.choose_pos hjd
  have hchR : (0 : ℝ) < (Nat.choose d j : ℝ) := by exact_mod_cast hch
  have hlog : 0 ≤ (1 / 2) * Real.log (Nat.choose d j : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nat.choose d j by omega)))
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    rw [norm_zero, cnorm_zero, Real.log_zero]
    simpa using hlog
  · have hcn : 0 < cnorm (d := d) hjd w := cnorm_pos_of_ne_zero hjd w hw
    have hle := norm_le_sqrt_card_mul_cnorm (d := d) hjd w
    have hsqrt : 0 < Real.sqrt (Nat.choose d j) := Real.sqrt_pos.mpr hchR
    have hprod : 0 < Real.sqrt (Nat.choose d j) * cnorm (d := d) hjd w := mul_pos hsqrt hcn
    have h1 : Real.log ‖w‖ ≤ Real.log (Real.sqrt (Nat.choose d j) * cnorm (d := d) hjd w) :=
      Real.log_le_log (norm_pos_iff.mpr hw) hle
    have h2 : Real.log (Real.sqrt (Nat.choose d j) * cnorm (d := d) hjd w) =
        Real.log (Real.sqrt (Nat.choose d j)) + Real.log (cnorm (d := d) hjd w) :=
      Real.log_mul (ne_of_gt hsqrt) (ne_of_gt hcn)
    rw [h2, Real.log_sqrt hchR.le] at h1
    linarith [h1]

/-- **The max-norm data is at most the Euclidean data.** -/
theorem flowMaxData_le_flowEuclidData {j ℓ : ℕ} (hjd : j ≤ d)
    {Λ₀ : Submodule ℤ (RD d)} {t : ℝ}
    (hBdd : BddBelow (flowMaxDataSet (d := d) Λ₀ ℓ t j hjd))
    (hne : (flowEuclidDataSet (d := d) Λ₀ ℓ t j).Nonempty) :
    flowMaxData (d := d) Λ₀ ℓ t j hjd ≤ flowEuclidData (d := d) Λ₀ ℓ t j := by
  refine le_csInf hne (fun r hr => ?_)
  obtain ⟨v, _, _, rfl⟩ := hr
  exact le_trans (csInf_le hBdd ⟨v, ‹∀ i, v i ∈ Λ₀›, ‹LinearIndependent ℝ v›, rfl⟩)
    (log_cnorm_le_log_norm hjd _)

/-- **The Euclidean data is at most the max-norm data plus `½log(choose d j)`.** -/
theorem flowEuclidData_le_flowMaxData_add {j ℓ : ℕ} (hjd : j ≤ d)
    {Λ₀ : Submodule ℤ (RD d)} {t : ℝ}
    (hBddM : BddBelow (flowMaxDataSet (d := d) Λ₀ ℓ t j hjd))
    (hneM : (flowMaxDataSet (d := d) Λ₀ ℓ t j hjd).Nonempty)
    (hBddE : BddBelow (flowEuclidDataSet (d := d) Λ₀ ℓ t j)) :
    flowEuclidData (d := d) Λ₀ ℓ t j ≤ flowMaxData (d := d) Λ₀ ℓ t j hjd +
      (1 / 2) * Real.log (Nat.choose d j : ℝ) := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hlt : flowMaxData (d := d) Λ₀ ℓ t j hjd <
      flowMaxData (d := d) Λ₀ ℓ t j hjd + ε := by linarith
  obtain ⟨b, hb, hb_lt⟩ := (csInf_lt_iff hBddM hneM).mp hlt
  obtain ⟨v, hvmem, hvli, rfl⟩ := hb
  refine le_trans (csInf_le hBddE ⟨v, hvmem, hvli, rfl⟩) ?_
  have h := log_norm_le_log_cnorm_add (d := d) hjd
    (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v))
  linarith [h, hb_lt]

end Submission.MaxEuclidData

end
