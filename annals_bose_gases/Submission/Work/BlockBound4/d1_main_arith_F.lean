import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BlockBound4.DiagWF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open scoped Real BigOperators Topology

/-- Faithful main-term scalar comparison.  `hM1 : 1 ≤ M` gives `M * (M+1) ≥ 0` and
`0 < 4 * s ^ 3`; multiply `hZ` by the nonnegative coefficient
`M * ((M+1)/(4*s^3)) * (1 + 6*c0*av)`, rewrite the resulting expression as
`(M*(M+1)/(2*s^3)) * GW * ((1+6*c0*av)*(1+6*Ct*(R/s)^2))` and use
`Submission.BoseGases.d1_K1` (from `Submission.Work.SmallBoxD1Scalar`) for
`(1+6*c0*av)*(1+6*Ct*(R/s)^2) ≤ (1+C*(R/s))*(1+C*c0*av)`. -/
lemma d1_main_arith_F {M s R c0 Ct av C chi0 Z GW : ℝ}
    (hs : 0 < s) (hM1 : 1 ≤ M) (hRs : R / s ≤ chi0) (hRs0 : 0 ≤ R / s)
    (hav : 0 ≤ av) (hc0 : 0 ≤ c0) (hCt : 0 ≤ Ct) (hGW : 0 ≤ GW)
    (hC6 : 6 ≤ C) (hCchi : 6 * Ct * chi0 ≤ C) (hCchi2 : 36 * Ct * chi0 ≤ C ^ 2)
    (hZ : Z ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * GW) :
    M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * av) * Z
      ≤ (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * av) * GW * (M * (M + 1) / s ^ 3) := by
  -- the pointwise bracket comparison
  have hK1 : (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)
      ≤ (1 + C * (R / s)) * (1 + C * c0 * av) :=
    Submission.BoseGases.d1_K1 (s := s) (R := R) (c0 := c0) (Ct := Ct) (av := av)
      (C := C) (chi0 := chi0) hRs hRs0 hCt hav hc0 hC6 hCchi hCchi2
  -- nonnegativity of the various factors
  have hMpos : (0 : ℝ) < M := by linarith
  have hc0av : 0 ≤ c0 * av := mul_nonneg hc0 hav
  have hA : 0 ≤ 1 + 6 * c0 * av := by nlinarith [hc0av]
  have hcoef : 0 ≤ M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * av) := by positivity
  have hcoef2 : 0 ≤ (M * (M + 1) / (2 * s ^ 3)) * GW := by positivity
  calc M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * av) * Z
      ≤ M * ((M + 1) / (4 * s ^ 3)) * (1 + 6 * c0 * av) * (2 * (1 + 6 * Ct * (R / s) ^ 2) * GW) :=
        mul_le_mul_of_nonneg_left hZ hcoef
    _ = (M * (M + 1) / (2 * s ^ 3)) * GW * ((1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)) := by
        ring
    _ ≤ (M * (M + 1) / (2 * s ^ 3)) * GW * ((1 + C * (R / s)) * (1 + C * c0 * av)) :=
        mul_le_mul_of_nonneg_left hK1 hcoef2
    _ = (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * av) * GW * (M * (M + 1) / s ^ 3) := by
        ring

end Work.BlockBound4
