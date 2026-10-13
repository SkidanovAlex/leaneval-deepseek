import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.Trunc.WindowBase
import Submission.Work.FTS.EllSol.Trunc.PassAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAone

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- `Gc` vanishes on the far right: for `t ≥ 2N` the cutoff term is zero, and the interval
integral is zero because `(chi N)'` is supported in `[-2N,2N]`. -/
theorem gc_right_zero (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N) {t θ : ℝ}
    (ht : 2 * N ≤ |t|) (hge : 2 * N ≤ t) :
    Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0 := by
  have hchit : Work.FTS.EllSol.Trunc.chi N t = 0 := Work.FTS.EllSol.Trunc.chi_eq_zero hN ht
  have hI : (∫ s in t..(2 * N),
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0 := by
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [heq, intervalIntegral.integral_same]
    · rw [intervalIntegral.integral_of_ge (le_of_lt hlt)]
      have hz : (∫ x in Set.Ioc (2 * N) t,
          Real.exp (-(b * x)) * deriv (Work.FTS.EllSol.Trunc.chi N) x * u x θ) = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
          have hd : deriv (Work.FTS.EllSol.Trunc.chi N) x = 0 :=
            Work.FTS.EllSol.Trunc.deriv_chi_eq_zero_of_gt hN (by
              rw [abs_of_pos (by linarith [hx.1])]
              exact hx.1)
          simp [hd])
      rw [hz, neg_zero]
  show Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0
  rw [hchit, hI]
  ring

/-- The tail representation of `Gc` for `t ≤ -2N`: integrating
`s ↦ chi N s · e^{-bs} u(s,θ)` by parts over `[t,2N]` (both boundary terms vanish because
`chi N` is supported in `[-2N,2N]`) turns the defining integral into the shifted derivative
of `u` against `chi N · e^{b(t-s)}`. -/
theorem gc_tail_ibp (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hle : t ≤ -(2 * N)) :
    Work.FTS.EllSol.ShiftFT.Gc N b u t θ
      = -(∫ s in t..(2 * N), Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s))
          * (Work.Spaces.pz u s θ - b * u s θ)) := by
  have hC2 : Work.FTS.EllSol.Trunc.StripC2 u := hu
  have hslice : ∀ x : ℝ, HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u x θ) x :=
    fun x => Work.FTS.EllSol.Trunc.hasDerivAt_zslice hC2 hθ x
  have huC : Continuous (fun s : ℝ => u s θ) := Work.FTS.EllSol.Trunc.continuous_zslice hC2 hθ
  have hpzC : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
    Work.FTS.EllSol.Trunc.continuous_pz_zslice hC2 hθ
  have hLcont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    hpzC.sub (continuous_const.mul huC)
  have hchit : Work.FTS.EllSol.Trunc.chi N t = 0 := by
    apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hchi2N : Work.FTS.EllSol.Trunc.chi N (2 * N) = 0 := by
    apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
    rw [abs_of_nonneg (by linarith)]
  have hIbp : (∫ x in t..(2 * N),
        deriv (Work.FTS.EllSol.Trunc.chi N) x * (Real.exp (-(b * x)) * u x θ))
      = -(∫ x in t..(2 * N), Work.FTS.EllSol.Trunc.chi N x
          * (Real.exp (-(b * x)) * (Work.Spaces.pz u x θ - b * u x θ))) := by
    have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := t) (b := 2 * N)
      (u := fun x : ℝ => Work.FTS.EllSol.Trunc.chi N x)
      (v := fun x : ℝ => Real.exp (-(b * x)) * u x θ)
      (u' := fun x : ℝ => deriv (Work.FTS.EllSol.Trunc.chi N) x)
      (v' := fun x : ℝ => Real.exp (-(b * x)) * (Work.Spaces.pz u x θ - b * u x θ))
      (fun x _ => ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable
        (by norm_num) x).hasDerivAt)
      (fun x _ => by
        have hx1 : HasDerivAt (fun s : ℝ => Real.exp (-(b * s)))
            (Real.exp (-(b * x)) * (-b)) x := by
          have h2 : HasDerivAt (fun s : ℝ => -(b * s)) (-b) x := by
            simpa using (hasDerivAt_id x).const_mul (-b)
          simpa using h2.exp
        have h3 := hx1.mul (hslice x)
        convert h3 using 1
        ring)
      (((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv
        (by norm_num)).intervalIntegrable t (2 * N))
      (((Real.continuous_exp.comp (by fun_prop :
          Continuous fun s : ℝ => -(b * s))).mul hLcont).intervalIntegrable t (2 * N))
    rw [hchi2N, hchit] at h1
    simp only [zero_mul, sub_zero, zero_sub] at h1
    linarith
  have hIeq : (∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      = ∫ s in t..(2 * N),
          deriv (Work.FTS.EllSol.Trunc.chi N) s * (Real.exp (-(b * s)) * u s θ) := by
    apply intervalIntegral.integral_congr
    intro s _
    ring
  show Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      = -(∫ s in t..(2 * N), Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s))
          * (Work.Spaces.pz u s θ - b * u s θ))
  rw [hchit, zero_mul, zero_add, hIeq, hIbp, mul_neg, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only []
  have he : Real.exp (b * t) * Real.exp (-(b * s)) = Real.exp (b * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (b * t) * (Work.FTS.EllSol.Trunc.chi N s
        * (Real.exp (-(b * s)) * (Work.Spaces.pz u s θ - b * u s θ)))
      = Work.FTS.EllSol.Trunc.chi N s * (Real.exp (b * t) * Real.exp (-(b * s)))
        * (Work.Spaces.pz u s θ - b * u s θ) from by ring,
    he]

/-- Domination of the cutoff-weighted integral: on `[t,2N]` with `t ≤ -2N` the cutoff
vanishes below `-2N` and is `≤ 1` on `[-2N,2N]`, and the exponential factor `e^{b(t-s)}` is
`≤ 1` there because `b ≥ 0` and `t ≤ s`. -/
theorem chi_exp_abs_le (N b : ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    {L : ℝ → ℝ} (hL : Continuous L) {t : ℝ} (hle : t ≤ -(2 * N)) :
    |∫ s in t..(2 * N),
        Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s|
      ≤ ∫ s in (-(2 * N))..(2 * N), |L s| := by
  have hNm : -(2 * N) ≤ 2 * N := by linarith
  have hgC : Continuous (fun s : ℝ =>
      Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s|) :=
    (((Work.FTS.EllSol.Trunc.chi_contDiff 0 N).continuous).mul (by fun_prop :
      Continuous fun s : ℝ => Real.exp (b * (t - s)))).mul hL.abs
  have hz : (∫ s in t..(-(2 * N)),
      Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s|) = 0 := by
    rw [← intervalIntegral.integral_zero (a := t) (b := -(2 * N))]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Pi.zero_apply]
    rw [Set.uIcc_of_le hle] at hx
    have hxle : x ≤ -(2 * N) := hx.2
    have hchi0 : Work.FTS.EllSol.Trunc.chi N x = 0 := by
      apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [hchi0, zero_mul, zero_mul]
  calc |∫ s in t..(2 * N),
        Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s|
      ≤ ∫ s in t..(2 * N),
          |Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ = ∫ s in t..(2 * N),
          Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s| := by
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [abs_mul, abs_mul, abs_of_nonneg (Work.FTS.EllSol.Trunc.chi_nonneg N s),
          abs_of_pos (Real.exp_pos _)]
    _ = ∫ s in (-(2 * N))..(2 * N),
          Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s| := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hgC.intervalIntegrable t (-(2 * N))) (hgC.intervalIntegrable (-(2 * N)) (2 * N)),
          hz, zero_add]
    _ ≤ ∫ s in (-(2 * N))..(2 * N), |L s| := by
        apply intervalIntegral.integral_mono_on hNm
        · exact hgC.intervalIntegrable _ _
        · exact hL.abs.intervalIntegrable _ _
        · intro x hx
          have hb0 : b * (t - x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hb (by linarith [hx.1, hle])
          have hexp1 : Real.exp (b * (t - x)) ≤ 1 := Real.exp_le_one_iff.mpr hb0
          have hexp0 : 0 ≤ Real.exp (b * (t - x)) := Real.exp_nonneg _
          have hchi1 : Work.FTS.EllSol.Trunc.chi N x ≤ 1 :=
            Work.FTS.EllSol.Trunc.chi_le_one N x
          have hchi0 : 0 ≤ Work.FTS.EllSol.Trunc.chi N x :=
            Work.FTS.EllSol.Trunc.chi_nonneg N x
          calc Work.FTS.EllSol.Trunc.chi N x * Real.exp (b * (t - x)) * |L x|
              ≤ 1 * 1 * |L x| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul hchi1 hexp1 hexp0 (by norm_num)
            _ = |L x| := by ring

theorem GcAbsLe (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Work.FTS.EllSol.ShiftFT.Gc N b u t θ|
        ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ| := by
  intro t θ hθ ht
  have hC2 : Work.FTS.EllSol.Trunc.StripC2 u := hu
  have hLcont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    (Work.FTS.EllSol.Trunc.continuous_pz_zslice hC2 hθ).sub
      (continuous_const.mul (Work.FTS.EllSol.Trunc.continuous_zslice hC2 hθ))
  rcases le_abs.mp ht with hge | hle'
  · rw [gc_right_zero N b u hN ht hge, abs_zero]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  · have hle : t ≤ -(2 * N) := by linarith
    rw [gc_tail_ibp N b u hN hu hθ hle, abs_neg]
    exact chi_exp_abs_le N b hN hb hLcont hle

end

end Work.FTS.EllSol.ShiftFT.uTrAone
