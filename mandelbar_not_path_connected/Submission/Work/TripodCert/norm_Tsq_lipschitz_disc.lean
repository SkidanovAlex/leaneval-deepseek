import Mathlib
import Submission.Work.TripodCert.UniqueDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay
open Work.Landing

/-! ## Two elementary disc bounds

The Lipschitz estimate for `Tsq c` on the disc of radius `UREq` around `z₀` needs two facts:

* every point of that disc has norm at most `UMq`;
* on that disc `‖z² + c̄‖ ≤ US0q + UDcq + 2·UMq·UREq`, i.e. the quadratic factor stays small
  because `‖z² - z₀²‖ = ‖z - z₀‖·‖z + z₀‖ ≤ UREq · 2·UMq`. -/

/-- Every point of the disc of radius `UREq` about `z₀` has norm at most `UMq`. -/
theorem norm_le_UMq_of_disc {z : ℂ} (hz : ‖z - uZ0‖ ≤ (UREq : ℝ)) :
    ‖z‖ ≤ (UMq : ℝ) := by
  have hURE : (0 : ℝ) ≤ (UREq : ℝ) := by norm_num [UREq]
  have h1 : ‖z‖ ≤ ‖uZ0‖ + ‖z - uZ0‖ := by
    calc ‖z‖ = ‖uZ0 + (z - uZ0)‖ := by congr 1; ring
      _ ≤ ‖uZ0‖ + ‖z - uZ0‖ := norm_add_le uZ0 (z - uZ0)
  linarith [hUMe, hz]

/-- On the disc of radius `UREq` about `z₀` and the parameter box `Xb`, the quadratic factor
`z² + c̄` is bounded by `US0q + UDcq + 2·UMq·UREq`. -/
theorem norm_sq_add_conj_le {c z : ℂ} (hc : Xb.mem c) (hz : ‖z - uZ0‖ ≤ (UREq : ℝ)) :
    ‖z ^ 2 + star c‖ ≤ (US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ) := by
  have hURE : (0 : ℝ) ≤ (UREq : ℝ) := by norm_num [UREq]
  have hUMnn : (0 : ℝ) ≤ (UMq : ℝ) := by norm_num [UMq]
  have hzp : ‖z + uZ0‖ ≤ 2 * (UMq : ℝ) := by
    have h1 : ‖z + uZ0‖ ≤ ‖z‖ + ‖uZ0‖ := norm_add_le z uZ0
    have h2 : ‖z‖ ≤ (UMq : ℝ) := norm_le_UMq_of_disc hz
    have h4 : ‖uZ0‖ ≤ (UMq : ℝ) := by linarith [hUMe, hURE]
    linarith
  have hz2 : ‖z ^ 2 - uZ0 ^ 2‖ ≤ 2 * (UMq : ℝ) * (UREq : ℝ) := by
    have hfac : z ^ 2 - uZ0 ^ 2 = (z - uZ0) * (z + uZ0) := by ring
    rw [hfac, norm_mul]
    calc ‖z - uZ0‖ * ‖z + uZ0‖ ≤ (UREq : ℝ) * (2 * (UMq : ℝ)) :=
          mul_le_mul hz hzp (norm_nonneg _) hURE
      _ = 2 * (UMq : ℝ) * (UREq : ℝ) := by ring
  have hstar : ‖star c - star c0T‖ ≤ (UDcq : ℝ) := by
    rw [← star_sub, norm_star]
    exact hDc hc
  have hcomb : z ^ 2 + star c
      = (z ^ 2 - uZ0 ^ 2) + (uZ0 ^ 2 + star c0T) + (star c - star c0T) := by ring
  rw [hcomb]
  calc ‖(z ^ 2 - uZ0 ^ 2) + (uZ0 ^ 2 + star c0T) + (star c - star c0T)‖
      ≤ ‖(z ^ 2 - uZ0 ^ 2) + (uZ0 ^ 2 + star c0T)‖ + ‖star c - star c0T‖ := norm_add_le _ _
    _ ≤ (‖z ^ 2 - uZ0 ^ 2‖ + ‖uZ0 ^ 2 + star c0T‖) + ‖star c - star c0T‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ) := by
        linarith [hz2, hUS0, hstar]

/-! ## The Lipschitz estimate -/

/-- `Tsq c` is Lipschitz with constant `ULq` on the disc of radius `UREq` about `z₀`, uniformly
for `c` in the parameter box `Xb`.

Indeed `Tsq c u - Tsq c v = (u - v)(u + v)(u² + v² + 2 c̄)`, the first factor is `u - v`, the
second is bounded by `2·UMq` and the third by `2·(US0q + UDcq + 2·UMq·UREq)`, so the product is
bounded by `4·UMq·(US0q + UDcq + 2·UMq·UREq) = ULq`. -/
theorem norm_Tsq_lipschitz_disc {c : ℂ} (hc : Work.SeedCertRay.Xb.mem c) {u v : ℂ}
    (hu : ‖u - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ))
    (hv : ‖v - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) :
    ‖Work.Landing.Tsq c u - Work.Landing.Tsq c v‖ ≤ (Work.TripodCert.ULq : ℝ) * ‖u - v‖ := by
  have hUMnn : (0 : ℝ) ≤ (UMq : ℝ) := by norm_num [UMq]
  have hfac : Tsq c u - Tsq c v = (u - v) * (u + v) * (u ^ 2 + v ^ 2 + 2 * star c) := by
    unfold Tsq; ring
  rw [hfac, norm_mul, norm_mul]
  have hup : ‖u + v‖ ≤ 2 * (UMq : ℝ) := by
    have h1 : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
    have h2 := norm_le_UMq_of_disc hu
    have h3 := norm_le_UMq_of_disc hv
    linarith
  have hquad : ‖u ^ 2 + v ^ 2 + 2 * star c‖
      ≤ 2 * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)) := by
    have h1 := norm_sq_add_conj_le hc hu
    have h2 := norm_sq_add_conj_le hc hv
    have hre : u ^ 2 + v ^ 2 + 2 * star c = (u ^ 2 + star c) + (v ^ 2 + star c) := by ring
    rw [hre]
    calc ‖(u ^ 2 + star c) + (v ^ 2 + star c)‖ ≤ ‖u ^ 2 + star c‖ + ‖v ^ 2 + star c‖ :=
          norm_add_le _ _
      _ ≤ 2 * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)) := by linarith
  have hUL : (2 * (UMq : ℝ)) * (2 * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ)))
      = (ULq : ℝ) := by
    rw [ULq]; push_cast; ring
  calc (‖u - v‖ * ‖u + v‖) * ‖u ^ 2 + v ^ 2 + 2 * star c‖
      = ‖u - v‖ * (‖u + v‖ * ‖u ^ 2 + v ^ 2 + 2 * star c‖) := by ring
    _ ≤ ‖u - v‖ * (ULq : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc ‖u + v‖ * ‖u ^ 2 + v ^ 2 + 2 * star c‖
            ≤ (2 * (UMq : ℝ)) * (2 * ((US0q : ℝ) + (UDcq : ℝ) + 2 * (UMq : ℝ) * (UREq : ℝ))) :=
              mul_le_mul hup hquad (norm_nonneg _) (by linarith)
          _ = (ULq : ℝ) := hUL
    _ = (ULq : ℝ) * ‖u - v‖ := by ring

end Work.TripodCert
