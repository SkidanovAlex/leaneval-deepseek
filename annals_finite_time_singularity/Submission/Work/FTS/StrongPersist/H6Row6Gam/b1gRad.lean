/-
# `H6Row6Gam/b1gRad` — the radial pair facts of the `b1fiveGamRowDz` row

The radial (`z`-side) facts about the two slice functionals

* `b1fiveMX α A z = (4/π)∫_θ(D_z^5A z ·)² + (200/(γ-1))∫_θ σ^{-γ}(D_z^5D_θA z ·)²` and
* `b1fiveQz α f z = ∫_θ σ^{-γ}(D_z^5D_θf z ·)²`

that the pairing estimate of `b1fiveGamRowDz` consumes: nonnegativity, the AM–GM inequality for
the product of their square roots, a.e. strong measurability of the square roots, integrability
of the AM–GM majorant `√3 M (w√MX)(w√Qz)`, and the radial Cauchy–Schwarz for the pair
`(w√MX, w√Qz)`.

Everything here rests on the already-proved `xProdIntLe`, `zProdIntLe` (the two integral bounds
`∫ w²MX ≤ (4/π + 200/(γ-1))·HkSq α 6 A`, `∫ w²Qz ≤ HkSq α 6 f`) and the generic radial
Cauchy–Schwarz `H6Pair6Aux.cs_sqrt_le_fts`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- `b1fiveMX` is nonnegative (for `α > 0`). -/
theorem b1gMXnn (α : ℝ) (A : ℝ → ℝ → ℝ) (hα0 : 0 < α) (z : ℝ) :
    0 ≤ b1fiveMX α A z := by
  rw [b1fiveMX_apply]
  refine add_nonneg (mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
    (mul_nonneg (div_nonneg (by norm_num) (by
        rw [hgam_const]; linarith))
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg
          (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))))

/-- `b1fiveQz` is nonnegative. -/
theorem b1gQznn (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ b1fiveQz α f z := by
  rw [b1fiveQz_apply]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))

/-- The AM–GM inequality for the product of the two square roots. -/
theorem b1gAMall (α : ℝ) (A f : ℝ → ℝ → ℝ) (hα0 : 0 < α) (z : ℝ) :
    (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2 := by
  have ha : (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
      = (Work.Spaces.w z) ^ 2 * b1fiveMX α A z := by
    rw [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)]
  have hb : (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
      = (Work.Spaces.w z) ^ 2 * b1fiveQz α f z := by
    rw [mul_pow, Real.sq_sqrt (b1gQznn α f z)]
  nlinarith [sq_nonneg (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)
    - Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))]

/-- The radial weight is a.e. strongly measurable; `√MX` inherits a.e. strong measurability from
the two slice integrals defining `MX`. -/
theorem b1gMXaesm (α : ℝ) (A : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen A) :
    MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (b1fiveMX α A z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Work.Spaces.DzIter 5 A z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral ((smoothOpen_continuousOn (hsm.DzIter 5)).pow 2)
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral (contOn_sig_mixed hsm (le_refl 1))
  have h3 : MeasureTheory.AEStronglyMeasurable (b1fiveMX α A)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [show b1fiveMX α A
        = fun z => (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2) from by
      funext z; rw [b1fiveMX_apply]]
    exact (h1.const_mul (4 / Real.pi)).add (h2.const_mul (200 / (Work.Spaces.gam α - 1)))
  exact Real.continuous_sqrt.comp_aestronglyMeasurable h3

/-- A.e. strong measurability of `√Qz`. -/
theorem b1gQzaesm (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (b1fiveQz α f z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 f z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral (contOn_sig_mixed hsm (le_refl 1))
  have h3 : MeasureTheory.AEStronglyMeasurable (b1fiveQz α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [show b1fiveQz α f
        = fun z => ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2 from by
      funext z; rw [b1fiveQz_apply]]
    exact h2
  exact Real.continuous_sqrt.comp_aestronglyMeasurable h3

/-- **Radial integrability of the AM–GM majorant.** -/
theorem b1gMajInt (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h6A : Work.Spaces.HkMem α 6 A) (h6f : Work.Spaces.HkMem α 6 f) (hMnn : 0 ≤ M) :
    MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := Work.FTS.TransportS.SlotT2.supOpen_w_nonneg
  have hMXint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveMX_apply] using (xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveQz_apply] using (zProdIntLe α f hα0 hα1 hf h6f).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * (((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hMajAbs_int ?_ ?_
  · exact ((aesm_w.mul (b1gMXaesm α A hA)).mul
      (aesm_w.mul (b1gQzaesm α f hf))).const_mul _
  · filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
      (mul_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))
        (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))))]
    exact mul_le_mul_of_nonneg_left (b1gAMall α A f hα0 z)
      (mul_nonneg (Real.sqrt_nonneg 3) hMnn)

/-- **The radial Cauchy–Schwarz** for the pair `(w√MX, w√Qz)`. -/
theorem b1gRadCS (α : ℝ) (A f : ℝ → ℝ → ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h6A : Work.Spaces.HkMem α 6 A) (h6f : Work.Spaces.HkMem α 6 f) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) := by
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := Work.FTS.TransportS.SlotT2.supOpen_w_nonneg
  have hMXint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveMX_apply] using (xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveQz_apply] using (zProdIntLe α f hα0 hα1 hf h6f).1
  have h := Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts (s := Work.Spaces.Iz)
    (A := fun z => (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
    (B := fun z => (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2)
    (hMXint.congr (Filter.Eventually.of_forall (fun z => by
      show (Work.Spaces.w z) ^ 2 * b1fiveMX α A z
        = (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
      rw [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)])))
    (hQint.congr (Filter.Eventually.of_forall (fun z => by
      show (Work.Spaces.w z) ^ 2 * b1fiveQz α f z
        = (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
      rw [mul_pow, Real.sq_sqrt (b1gQznn α f z)])))
    (fun z => sq_nonneg _) (fun z => sq_nonneg _)
  rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)])),
    show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [mul_pow, Real.sq_sqrt (b1gQznn α f z)]))] at h
  have heqint : (∫ z in Work.Spaces.Iz,
        Real.sqrt ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
        * Real.sqrt ((Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))]))
  rwa [heqint] at h

end

end Work.FTS.StrongPersist.H6Row6
