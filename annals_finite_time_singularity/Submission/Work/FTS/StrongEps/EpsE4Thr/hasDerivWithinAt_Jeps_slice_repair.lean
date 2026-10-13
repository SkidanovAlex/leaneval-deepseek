import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem hasDerivWithinAt_Jeps_slice_repair {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : ∀ s ∈ Set.Icc 0 T, MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p *
        (Work.FTS.Galerkin.slice g s) (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
      |Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun s => Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s) z θ)
      (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) z θ)
      (Set.Icc 0 T) τ := by
  obtain ⟨C, hC0, hCbd⟩ := hbd
  have hτmem : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
  -- the two hypotheses of the parametric differentiation lemma that only use `hint`
  have hF_meas : ∀ᶠ x in 𝓝 τ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) x) volume := by
    filter_upwards [hs] with x hx
    simpa only [slice] using (hint x ⟨hx.1.le, hx.2.le⟩).aestronglyMeasurable
  have hF_int : Integrable (fun p : ℝ × ℝ =>
      Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) τ) volume := by
    simpa only [slice] using hint τ hτmem
  -- the a.e.-measurability of the derivative integrand: the junk-integral obstruction of the
  -- un-repaired statement is exactly what the extra hypothesis `hint` removes (the derivative
  -- integrand is the a.e. limit of the difference quotients supplied by `hint`).
  have hF'_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Jker ρ ε p * epsRHSP α ρ ε Φs E g τ (zShift z p.1) (thShift θ p.2)) volume :=
    Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP hz hθ hτ hsol hint
  -- the domination, from `hbd` (the shifted points are in the quadrant, so the bound applies)
  have h_bound : ∀ᵐ a ∂volume, ∀ x ∈ Set.Ioo (0 : ℝ) T,
      ‖Jker ρ ε a * epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)‖
        ≤ (fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖) a := by
    refine Eventually.of_forall fun a x hx => ?_
    by_cases ha : a ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have hb : |epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)| ≤ C :=
        hCbd a (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha) x
          ⟨hx.1.le, hx.2.le⟩
      calc ‖Jker ρ ε a * epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)‖
          = ‖Jker ρ ε a‖ * |epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)| := by
            simp only [norm_mul, Real.norm_eq_abs]
        _ ≤ ‖Jker ρ ε a‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = C * ‖Jker ρ ε a‖ := by ring
    · have hz0 : Jker ρ ε a = 0 := Jker_eq_zero_of_not_mem hρ.moll hε ha
      rw [hz0, zero_mul, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hbound_int : Integrable (fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖) volume :=
    (Jker_integrable hρ.moll hε).norm.const_mul C
  -- the pointwise derivative, from the scheme
  have h_diff : ∀ᵐ a ∂volume, ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun x => Jker ρ ε a * g (zShift z a.1) (thShift θ a.2) x)
        (Jker ρ ε a * epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)) x := by
    refine Eventually.of_forall fun a x hx => ?_
    have hd : HasDerivWithinAt (fun t : ℝ => g (zShift z a.1) (thShift θ a.2) t)
        (epsRHSP α ρ ε Φs E g x (zShift z a.1) (thShift θ a.2)) (Set.Icc 0 T) x :=
      hsol.2 (zShift z a.1) (thShift θ a.2) x (zShift_pos hz) (thShift_mem hθ)
        ⟨hx.1.le, hx.2.le⟩
    exact (hd.hasDerivAt (Icc_mem_nhds hx.1 hx.2)).const_mul (Jker ρ ε a)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (𝕜 := ℝ)
      (F := fun x p => Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) x)
      (F' := fun x p => Jker ρ ε p * epsRHSP α ρ ε Φs E g x (zShift z p.1) (thShift θ p.2))
      (bound := fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖)
      (x₀ := τ) (s := Set.Ioo 0 T) hs
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  rw [show (fun s : ℝ => Jeps ρ ε (slice g s) z θ)
        = fun s : ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) s from
        funext (fun s => Jeps_eq_integral ρ ε (slice g s) hz hθ),
      show Jeps ρ ε (epsRHSP α ρ ε Φs E g τ) z θ
        = ∫ p : ℝ × ℝ, Jker ρ ε p * epsRHSP α ρ ε Φs E g τ (zShift z p.1) (thShift θ p.2)
        from Jeps_eq_integral ρ ε (epsRHSP α ρ ε Φs E g τ) hz hθ]
  exact hmain.hasDerivWithinAt

end Work.FTS.StrongEps.EpsE4Thr
