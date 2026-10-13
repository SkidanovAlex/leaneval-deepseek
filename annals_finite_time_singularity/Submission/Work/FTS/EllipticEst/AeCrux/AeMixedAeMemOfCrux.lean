import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AeCrux.AeSliceHonV
import Submission.Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeCrux

/-
The glue that turns the two crux statements into the tree's `aeMixedAe_mem` (the leaf
`Cores/AeStep2Aux/aeMixedAe_mem`, both call sites having the same conclusion): the gaps are the
null-set transfers `Ioo 0 (π/2) → Iθ` and `Ioi 0 → Iz`, plus `1 ≤ w z` on `z > 0`
(`w z = (1+z)^2/z^2`) for the outer conjunct.  Purely measure-theoretic; `h` and `hU` are unused.
-/
theorem AeMixedAeMemOfCrux {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hout : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz := by
  -- `Iθ = Icc 0 (π/2)` differs from `Ioo 0 (π/2)` by two points, and `Iz = Ici 0` from
  -- `Ioi 0` by one, so the corresponding restricted measures agree.
  have hIcc : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  have hIci : MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  constructor
  · -- first conjunct: transfer the a.e. slice honesty from `(0,π/2)` to `Iθ`
    filter_upwards [hsl] with z hz
    show MeasureTheory.Integrable
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
    rw [hIcc]
    exact hz
  · -- second conjunct: transfer the outer integrability from `(0,∞)` to `Iz` and from the
    -- open angular interval to `Iθ`; the weight satisfies `1 ≤ w z` on `z > 0`.
    have hfuneq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        = (fun z : ℝ => ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
      funext z
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2)).symm
    show MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
    rw [hIci, hfuneq]
    refine MeasureTheory.Integrable.mono hout ?_ ?_
    · -- a.e. strong measurability of the unweighted slice functional: divide by `w z ^ 2`
      have hb : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hout.aestronglyMeasurable
      have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
        have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 * (z ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
          (((continuous_const.add continuous_id).pow 2).continuousOn).mul
            (((continuous_id.pow 2).continuousOn).inv₀
              (fun z hz => pow_ne_zero 2 (ne_of_gt hz)))
        refine h1.congr (fun z hz => ?_)
        simp only [Work.Spaces.w, div_eq_mul_inv]
      have hc : ContinuousOn (fun z : ℝ => ((Work.Spaces.w z) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
        (hwcont.pow 2).inv₀ (fun z hz => by
          have hzpos : 0 < z := hz
          have hw : Work.Spaces.w z ≠ 0 := by
            rw [Work.Spaces.w]
            exact div_ne_zero (pow_ne_zero 2 (by linarith [hzpos]))
              (pow_ne_zero 2 (ne_of_gt hzpos))
          exact pow_ne_zero 2 hw)
      refine ((hc.aestronglyMeasurable measurableSet_Ioi).mul hb).congr ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      show ((Work.Spaces.w z) ^ 2)⁻¹
            * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                    * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
      have hzpos : 0 < z := hz
      have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
        have h1 : Work.Spaces.w z ≠ 0 := by
          rw [Work.Spaces.w]
          exact div_ne_zero (pow_ne_zero 2 (by linarith [hzpos]))
            (pow_ne_zero 2 (ne_of_gt hzpos))
        exact pow_ne_zero 2 h1
      rw [inv_mul_cancel_left₀ hw]
    · -- a.e. norm bound: `1 ≤ w z ^ 2` on `z > 0`
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      have hzpos : 0 < z := hz
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h1 : 1 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w, le_div_iff₀ (pow_pos hzpos 2)]
          nlinarith
        nlinarith [h1]
      have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwnn]
      have hX : 0 ≤ |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))| := abs_nonneg _
      simpa using mul_le_mul_of_nonneg_right hw1 hX

end Work.FTS.EllipticEst.AeCrux
