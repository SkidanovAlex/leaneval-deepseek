import Mathlib
import Submission.Work.Haupt.qp_defs

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- The partial products `(a;q)_m` converge to the infinite product `(a;q)_∞`
whenever `‖q‖ < 1`. -/
lemma qpNat_tendsto_qpInf (a q : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun m : ℕ => qpNat a q m) Filter.atTop (nhds (qpInf a q)) := by
  have hgeo : Summable fun n : ℕ => ‖a‖ * ‖q‖ ^ n :=
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  have hsum : Summable fun n : ℕ => ‖-(a * q ^ n)‖ := by
    refine hgeo.congr fun n => ?_
    simp [norm_pow]
  have hmul : Multipliable fun n : ℕ => 1 + (-(a * q ^ n)) :=
    multipliable_one_add_of_summable hsum
  have h := hmul.tendsto_prod_tprod_nat
  simpa [qpNat, qpInf, sub_eq_add_neg] using h

theorem semifinite_rhs_limit {q z : ℂ} (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun m : ℕ => qpNat q q m * qpNat (-q/z) q m * qpInf (-z) q) Filter.atTop
      (nhds (qpInf q q * qpInf (-q/z) q * qpInf (-z) q)) := by
  have h1 := qpNat_tendsto_qpInf q q hq
  have h2 := qpNat_tendsto_qpInf (-q/z) q hq
  have h3 : Tendsto (fun _ : ℕ => qpInf (-z) q) atTop (nhds (qpInf (-z) q)) :=
    tendsto_const_nhds
  simpa [mul_assoc] using (h1.mul h2).mul h3

end Work.Haupt
