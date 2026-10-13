import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData.HkSqAux

/-- **`∫_{z ≥ L} (1+z)^{-2} ≤ 1/L`** (with the integrability needed to use it), for `L > 0`.
The integrand is dominated by `z^{-2}` on `z ≥ L > 0`, whose tail integral is `1/L`. -/
theorem integrableOn_and_integral_Ici_oneAdd_rpow_neg_two (L : ℝ) (hL : 0 < L) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ici L) ∧
      ∫ z in Set.Ici L, (1 + z) ^ (-2 : ℝ) ≤ 1 / L := by
  have hIntIoi : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ioi L) := by
    have hbase := integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := L) (m := 1)
      (by norm_num) (by linarith)
    refine hbase.congr_fun (fun z _ => ?_) measurableSet_Ioi
    rw [show (1 + z : ℝ) = z + 1 by ring]
  have hIntIci : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ici L) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIntIoi
  refine ⟨hIntIci, ?_⟩
  have hcmp : ∫ z in Set.Ioi L, (1 + z) ^ (-2 : ℝ) ≤ ∫ z in Set.Ioi L, z ^ (-2 : ℝ) := by
    refine MeasureTheory.integral_mono_ae hIntIoi
      (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hL) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : (0 : ℝ) < z := by linarith [Set.mem_Ioi.mp hz, hL]
    rw [show (1 + z : ℝ) = z + 1 by ring]
    exact Real.rpow_le_rpow_of_nonpos hz0 (by linarith) (by norm_num)
  have hval : ∫ z in Set.Ioi L, z ^ (-2 : ℝ) = 1 / L := by
    rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hL]
    have : -L ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) = 1 / L := by
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    simpa using this
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  linarith

end Work.FTS.LocData.HkSqAux
