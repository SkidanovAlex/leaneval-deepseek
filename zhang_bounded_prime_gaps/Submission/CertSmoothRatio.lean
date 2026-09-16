import Submission.CertSmoothJ
import Submission.CertMkEps

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The smoothed certificate as a competitor with ratio above a threshold

`tendsto_IFuncOrth_certSmooth` and `tendsto_JFunc_certSmooth` say that the two functionals of
the smoothed certificate `certSmooth γ = certPoly · smoothCut` converge, as `γ → 0⁺`, to those of
the certificate function `certFun`.  Hence every threshold below the certificate's variational
quotient is exceeded by `certSmooth γ` for some `γ > 0` — this is the form in which the
continuity chapter feeds the tensor localisation of §5.3 (which needs a *continuous* input).
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- **A sharper certificate bound:** the variational quotient of `certFun` exceeds `4.001`. -/
theorem cert_ratio_gt_sharp :
    ((4001 : ℝ) / 1000) < (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun := by
  rw [sum_JFunc_certFun_value_eq, IFuncOrth_certFun_eq]
  have hK2 : (0 : ℝ) < (certK : ℝ) * (certK : ℝ) := mul_pos certK_pos certK_pos
  have hineq : ((4001 : ℤ) * certqI * certDJ : ℤ) < (50000 : ℤ) * certqJ * certDI := by decide
  have hineq' : ((4001 : ℝ) * (certqI : ℝ) * (certDJ : ℝ)) < 50000 * (certqJ : ℝ) * (certDI : ℝ) := by
    exact_mod_cast hineq
  have hDIne : (certDI : ℝ) ≠ 0 := ne_of_gt certDI_pos
  have hDJne : (certDJ : ℝ) ≠ 0 := ne_of_gt certDJ_pos
  have h : ((4001 : ℝ) / 1000) * ((certqI : ℝ) / (certDI : ℝ))
      < 50 * ((certqJ : ℝ) / (certDJ : ℝ)) := by
    have h1 : ((4001 : ℝ) / 1000) * ((certqI : ℝ) / (certDI : ℝ))
        = ((4001 * (certqI : ℝ) * (certDJ : ℝ))) / (1000 * ((certDI : ℝ) * (certDJ : ℝ))) := by
      field_simp
    have h2 : (50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))
        = (50 * (certqJ : ℝ) * (certDI : ℝ)) / ((certDI : ℝ) * (certDJ : ℝ)) := by
      field_simp
    rw [h1, h2, div_lt_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 1000) (mul_pos certDI_pos certDJ_pos))
      (mul_pos certDI_pos certDJ_pos)]
    have h3 : (4001 : ℝ) * (certqI : ℝ) * (certDJ : ℝ) * ((certDI : ℝ) * (certDJ : ℝ))
        < 50000 * (certqJ : ℝ) * (certDI : ℝ) * ((certDI : ℝ) * (certDJ : ℝ)) :=
      mul_lt_mul_of_pos_right hineq' (mul_pos certDI_pos certDJ_pos)
    nlinarith [h3]
  rw [lt_div_iff₀ (mul_pos hK2 (div_pos certqI_pos certDI_pos))]
  calc ((4001 : ℝ) / 1000) * ((certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ)))
      = ((certK : ℝ) * (certK : ℝ)) * (((4001 : ℝ) / 1000) * ((certqI : ℝ) / (certDI : ℝ))) := by ring
    _ < ((certK : ℝ) * (certK : ℝ)) * ((50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))) :=
        mul_lt_mul_of_pos_left h hK2
    _ = 50 * (certK : ℝ) * (certK : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ)) := by ring

/-- **Some `certSmooth γ` has quotient above any threshold below the certificate's.** -/
theorem exists_certSmooth_ratio_gt_of_lt {r : ℝ}
    (hr : r < (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun) :
    ∃ γ : ℝ, 0 < γ ∧ r < (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth γ))
      / IFuncOrth 50 (certSmooth γ) := by
  have hnum : Tendsto (fun n : ℕ =>
      ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun)) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact tendsto_JFunc_certSmooth i ((24 : ℝ) / 25)
  have hden : Tendsto (fun n : ℕ => IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 (IFuncOrth 50 certFun)) := tendsto_IFuncOrth_certSmooth
  have hratio : Tendsto (fun n : ℕ =>
      (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) (certSmooth ((1 : ℝ) / (n + 1))))
        / IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 ((∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun)) :=
    hnum.div hden (ne_of_gt certFun_IFuncOrth_pos)
  obtain ⟨n, hn⟩ := (hratio.eventually (Ioi_mem_nhds hr)).exists
  exact ⟨(1 : ℝ) / (n + 1), by positivity, hn⟩

end

end Commons.NumberTheory.MaynardSieve
