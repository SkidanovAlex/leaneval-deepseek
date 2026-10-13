import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcSliceData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.ShiftFT.Aux2

theorem gcIBP (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      (∫ s in (-(2 * N))..(2 * N),
          Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
            * (Work.Spaces.pz u s θ - b * u s θ))
        = -(Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
  intro θ hθ t
  obtain ⟨hsliceD, hpzD⟩ := gcSliceData u hu
  have hslice' : Differentiable ℝ (fun s : ℝ => u s θ) := hsliceD θ hθ
  have hpz' : Differentiable ℝ (fun s : ℝ => Work.Spaces.pz u s θ) := hpzD θ hθ
  -- The antiderivative `P s = e^{b(t-s)} χ(s) u(s,θ)`, whose total derivative is
  -- the integrand of the left-hand side plus the term `e^{b(t-s)} χ'(s) u(s,θ)`.
  set P : ℝ → ℝ := fun s => Real.exp (b * (t - s)) * (Work.FTS.EllSol.Trunc.chi N s * u s θ)
    with hP
  set Pexp : ℝ → ℝ := fun s => -b * Real.exp (b * (t - s))
        * (Work.FTS.EllSol.Trunc.chi N s * u s θ)
      + Real.exp (b * (t - s)) * (deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
          + Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ) with hPexp
  have hPd : ∀ s, HasDerivAt P (Pexp s) s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => b * (t - s)) (-b) s := by
      have h0 : HasDerivAt (fun s : ℝ => t - s) (-1) s := (hasDerivAt_id s).const_sub t
      simpa using h0.const_mul b
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (b * (t - s)))
        (Real.exp (b * (t - s)) * (-b)) s := hlin.exp
    have hchi : HasDerivAt (Work.FTS.EllSol.Trunc.chi N)
        (deriv (Work.FTS.EllSol.Trunc.chi N) s) s :=
      ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) s).hasDerivAt
    have hslice : HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u s θ) s :=
      (hslice' s).hasDerivAt
    rw [hP]
    simp only [hPexp]
    exact (hexp.mul (hchi.mul hslice)).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have hcont_exp : Continuous (fun s : ℝ => Real.exp (b * (t - s))) := by
    apply Real.continuous_exp.comp
    fun_prop
  have hcont_chi : Continuous (Work.FTS.EllSol.Trunc.chi N) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 0 N).continuous
  have hcont_dchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv_one
  have hcont_u : Continuous (fun s : ℝ => u s θ) := hslice'.continuous
  have hcont_pz : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) := hpz'.continuous
  have hcont_Pexp : Continuous Pexp := by
    rw [hPexp]
    exact ((hcont_exp.const_mul (-b)).mul (hcont_chi.mul hcont_u)).add
      (hcont_exp.mul ((hcont_dchi.mul hcont_u).add (hcont_chi.mul hcont_pz)))
  have hcont_R : Continuous (fun s : ℝ =>
      Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) :=
    (hcont_exp.mul hcont_dchi).mul hcont_u
  have hIntPexp : IntervalIntegrable Pexp volume (-(2 * N)) (2 * N) :=
    hcont_Pexp.intervalIntegrable _ _
  have hIntR : IntervalIntegrable (fun s : ℝ =>
      Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) volume
        (-(2 * N)) (2 * N) := hcont_R.intervalIntegrable _ _
  -- Fundamental theorem of calculus; the boundary values vanish because `χ(±2N) = 0`.
  have hFTC : ∫ s in (-(2 * N))..(2 * N), Pexp s = P (2 * N) - P (-(2 * N)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hPd s) hIntPexp
  have hPtwo : P (2 * N) = 0 := by
    rw [hP]
    change Real.exp (b * (t - 2 * N))
      * (Work.FTS.EllSol.Trunc.chi N (2 * N) * u (2 * N) θ) = 0
    have h2N : (0 : ℝ) < 2 * N := by linarith
    rw [Work.FTS.EllSol.Trunc.chi_eq_zero hN (by simp [abs_of_pos h2N]), zero_mul, mul_zero]
  have hPneg : P (-(2 * N)) = 0 := by
    rw [hP]
    change Real.exp (b * (t - -(2 * N)))
      * (Work.FTS.EllSol.Trunc.chi N (-(2 * N)) * u (-(2 * N)) θ) = 0
    have h2N : (0 : ℝ) < 2 * N := by linarith
    rw [Work.FTS.EllSol.Trunc.chi_eq_zero hN (by simp [abs_neg, abs_of_pos h2N]),
      zero_mul, mul_zero]
  have hpoint : ∀ s, Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
        * (Work.Spaces.pz u s θ - b * u s θ)
      = Pexp s - Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
    intro s
    simp only [hPexp]
    ring_nf
  have hRfac : ∫ s in (-(2 * N))..(2 * N),
        Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
      = Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    show Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
      = Real.exp (b * t) * (Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
          * u s θ)
    have hexp : Real.exp (b * (t - s)) = Real.exp (b * t) * Real.exp (-(b * s)) := by
      rw [← Real.exp_add, show b * t + -(b * s) = b * (t - s) from by ring]
    rw [hexp]
    ring
  calc ∫ s in (-(2 * N))..(2 * N), Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
          * (Work.Spaces.pz u s θ - b * u s θ)
      = ∫ s in (-(2 * N))..(2 * N), (Pexp s - Real.exp (b * (t - s))
            * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact hpoint s
    _ = (∫ s in (-(2 * N))..(2 * N), Pexp s) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ :=
          intervalIntegral.integral_sub hIntPexp hIntR
    _ = (P (2 * N) - P (-(2 * N))) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
          rw [hFTC]
    _ = (0 - 0) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
          rw [hPtwo, hPneg]
    _ = -(Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
          rw [hRfac]
          ring

end Work.FTS.EllSol.ShiftFT.Aux2
