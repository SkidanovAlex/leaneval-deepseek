import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.MK_critical_bound
import Submission.Work.ZeroDensity.Ingham.zeta_halfLine_poly_bound
import Submission.Work.ZeroDensity.Ingham.gamma_crit_bound
import Submission.Work.ZeroDensity.Ingham.integral_Ioi_polyexp_le
import Submission.Work.ZeroDensity.Ingham.critTailNumeric

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- (Put this in namespace `Work.ZeroDensity.Ingham`, with `open scoped Classical BigOperators` and
`open MeasureTheory`; import `Submission.Work.ZeroDensity.Ingham.Defs` and
`Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs`.)

**The tails of the critical-line integral of the detector are small.**  There is `A₀ ≥ 6` such that
for every `A ≥ A₀`, every `T ≥ 2`, all `K, Y` with `1 ≤ K ≤ T`, `1 ≤ Y ≤ T²`, and every `ρ` with
`1/2 ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T`,

`Y^{1/2-Re ρ} ( ∫_{v > A log (A T)} critIntegrand K ρ v dv + ∫_{v ≤ -A log (A T)} critIntegrand K ρ v dv )
   ≤ π/10`,

where `critIntegrand K ρ v = ‖ζ(1/2 + i(Im ρ + v))‖ · ‖M_K(1/2 + i(Im ρ + v))‖ · ‖Γ(1/2 - Re ρ + iv)‖`. -/
theorem critTailSmall : ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
    ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T → 1 ≤ Y → Y ≤ T ^ 2 →
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      Y ^ (1 / 2 - ρ.re) *
        ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
          + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zeta_halfLine_poly_bound
  have hK6pos : 0 < Commons.Analysis.Complex.K6 := Commons.Analysis.Complex.K6_pos
  set J : ℝ := ∫ s in Set.Ioi 0, (1 + s)^10 * Real.exp (-(Real.pi/2) * s) with hJdef
  set J' : ℝ := |J| + 1 with hJ'def
  have hJ'pos : 0 < J' := by rw [hJ'def]; exact add_pos_of_nonneg_of_pos (abs_nonneg J) one_pos
  have hJ'nn : 0 ≤ J' := le_of_lt hJ'pos
  have hJJ' : J ≤ J' := by rw [hJ'def]; linarith [le_abs_self J]
  set Kall : ℝ := 4 * Cz * Commons.Analysis.Complex.K6 * J' with hKalldef
  have hKallpos : 0 < Kall := by
    rw [hKalldef]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hCzpos) hK6pos) hJ'pos
  obtain ⟨A₀, hA₀6, hA₀main⟩ := critTailNumeric Kall hKallpos
  refine ⟨A₀, hA₀6, ?_⟩
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hρ1 hρ2 hγ
  set H : ℝ := A * Real.log (A * T) with hHdef
  have hA6 : 6 ≤ A := le_trans hA₀6 hA
  have hApos : 0 < A := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  have hNpos : 0 < Real.log (A*T) := Real.log_pos hAT1
  have hHpos : 0 < H := by rw [hHdef]; exact mul_pos hApos hNpos
  have hlog1 : 1 ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0:ℝ) < A * T)]
    have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    nlinarith [hA6, hT, h3]
  have hH1 : 1 ≤ H := by
    rw [hHdef]
    have hmul : (6:ℝ) * 1 ≤ A * Real.log (A * T) :=
      mul_le_mul hA6 hlog1 (by norm_num) hApos.le
    linarith
  have hHnn : 0 ≤ H := le_of_lt hHpos
  have hYpow_le : Y ^ (1/2 - ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hYpow_nn : 0 ≤ Y ^ (1/2 - ρ.re) := Real.rpow_nonneg (by linarith) _
  set c : ℝ := Cz * (2 * Real.sqrt K) * Commons.Analysis.Complex.K6 with hcdef
  have hc_nn : 0 ≤ c := by
    rw [hcdef]; exact mul_nonneg (mul_nonneg hCzpos.le
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg K))) hK6pos.le
  set X : ℝ := Real.exp (-(Real.pi/2)*H) * (3+T+H)^4 * (1+H)^6 with hXdef
  have h3TH : (0:ℝ) ≤ 3 + T + H := by linarith
  have h1H : (0:ℝ) ≤ 1 + H := by linarith
  have hX_nn : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg h3TH 4)) (pow_nonneg h1H 6)
  have key : ∀ u τ : ℝ, 1 ≤ |u| → |τ| ≤ T + |u| →
      ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ * ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ *
        ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖
      ≤ c * ((3 + T + |u|)^4 * (1 + |u|)^6 * Real.exp (-(Real.pi/2)*|u|)) := by
    intro u τ hu hτ
    have hZ : ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ Cz * (3 + |τ|)^4 := hCz τ
    have hZ2 : Cz * (3 + |τ|)^4 ≤ Cz * (3 + T + |u|)^4 := by
      apply mul_le_mul_of_nonneg_left _ hCzpos.le
      apply pow_le_pow_left₀ (add_nonneg (by norm_num) (abs_nonneg τ)) _ 4
      linarith [hτ]
    have hM : ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ 2 * Real.sqrt K := by
      apply MK_critical_bound
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    have hre_z : Complex.re (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I) = (1/2:ℝ) - ρ.re := by
      simp [Complex.add_re, Complex.mul_re]
    have him_z : Complex.im (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I) = u := by
      simp [Complex.add_im, Complex.mul_im]
    have hG : ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖ ≤
        Commons.Analysis.Complex.K6 * (1 + |u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|) := by
      have h := gamma_crit_bound (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)
        (by rw [hre_z]; linarith) (by rw [hre_z]; linarith) (by rw [him_z]; exact hu)
      simpa [him_z] using h
    have hZ3 : ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ Cz * (3 + T + |u|)^4 := le_trans hZ hZ2
    have hZt_nn : 0 ≤ Cz * (3 + T + |u|)^4 :=
      mul_nonneg hCzpos.le (pow_nonneg (by linarith [abs_nonneg u, hT] : (0:ℝ) ≤ 3 + T + |u|) 4)
    have hMt_nn : 0 ≤ 2 * Real.sqrt K := mul_nonneg (by norm_num) (Real.sqrt_nonneg K)
    have hGt_nn : 0 ≤ Commons.Analysis.Complex.K6 * (1 + |u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|) :=
      mul_nonneg (mul_nonneg hK6pos.le (Real.rpow_nonneg (add_nonneg (by norm_num) (abs_nonneg u)) 6)) (Real.exp_nonneg _)
    calc ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ * ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ *
            ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖
        ≤ (Cz * (3+T+|u|)^4) * (2*Real.sqrt K) *
            (Commons.Analysis.Complex.K6 * (1+|u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|)) := by
          exact mul_le_mul (mul_le_mul hZ3 hM (norm_nonneg _) hZt_nn) hG (norm_nonneg _)
            (mul_nonneg hZt_nn hMt_nn)
      _ = c * ((3+T+|u|)^4 * (1+|u|)^6 * Real.exp (-(Real.pi/2)*|u|)) := by
          rw [hcdef]
          have hpow : (1 + |u|) ^ (6:ℝ) = (1 + |u|) ^ 6 := Real.rpow_natCast (1 + |u|) 6
          rw [hpow]; ring
  have hpb_pos : ∀ v ∈ Set.Ioi H, critIntegrand K ρ v ≤
      c * ((3+T+v)^4 * (1+v)^6 * Real.exp (-(Real.pi/2)*v)) := by
    intro v hv
    have hvlt : H < v := by simpa using hv
    have hvpos : 0 < v := by linarith [hH1, hvlt]
    have harg : (1/2:ℂ) + (ρ.im:ℂ)*Complex.I + (v:ℂ)*Complex.I
        = (1/2:ℂ) + ((ρ.im + v:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hu : 1 ≤ |v| := by rw [abs_of_pos hvpos]; linarith [hH1, hvlt]
    have hτ : |ρ.im + v| ≤ T + |v| := by
      calc |ρ.im + v| ≤ |ρ.im| + |v| := abs_add_le _ _
        _ ≤ T + |v| := by linarith [hγ]
    have hk := key v (ρ.im + v) hu hτ
    rw [critIntegrand, harg]
    simpa [abs_of_pos hvpos] using hk
  have hpb_neg : ∀ v ∈ Set.Ioi H, critIntegrand K ρ (-v) ≤
      c * ((3+T+v)^4 * (1+v)^6 * Real.exp (-(Real.pi/2)*v)) := by
    intro v hv
    have hvlt : H < v := by simpa using hv
    have hvpos : 0 < v := by linarith [hH1, hvlt]
    have hargn : (1/2:ℂ) + (ρ.im:ℂ)*Complex.I + (((-v:ℝ)):ℂ)*Complex.I
        = (1/2:ℂ) + ((ρ.im - v:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hu : 1 ≤ |(-v:ℝ)| := by rw [abs_neg, abs_of_pos hvpos]; linarith [hH1, hvlt]
    have hτ : |ρ.im - v| ≤ T + |(-v:ℝ)| := by
      rw [abs_neg, abs_of_pos hvpos]
      calc |ρ.im - v| ≤ |ρ.im| + |v| := by
              rw [sub_eq_add_neg]; exact le_trans (abs_add_le _ _) (by rw [abs_neg])
        _ ≤ T + v := by rw [abs_of_pos hvpos]; linarith [hγ]
    have hk := key (-v) (ρ.im - v) hu hτ
    rw [critIntegrand, hargn]
    simpa [abs_neg, abs_of_pos hvpos] using hk
  have hI1 : (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J) := by
    rw [hJdef, hXdef]
    refine integral_Ioi_polyexp_le T H c (by linarith) hH1 hc_nn (fun v => critIntegrand K ρ v) ?_ ?_
    · intro v _; simp only [critIntegrand]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    · intro v hv; exact hpb_pos v hv
  have hI2 : (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J) := by
    rw [hJdef, hXdef]
    rw [← integral_comp_neg_Ioi H (fun x => critIntegrand K ρ x)]
    refine integral_Ioi_polyexp_le T H c (by linarith) hH1 hc_nn (fun v => critIntegrand K ρ (-v)) ?_ ?_
    · intro v _; simp only [critIntegrand]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    · intro v hv; exact hpb_neg v hv
  have hI1' : (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J') := by
    calc (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J) := hI1
      _ ≤ c * (X * J') := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJJ' hX_nn) hc_nn
  have hI2' : (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J') := by
    calc (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J) := hI2
      _ ≤ c * (X * J') := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJJ' hX_nn) hc_nn
  have hsum : (∫ v in Set.Ioi H, critIntegrand K ρ v) + (∫ v in Set.Iic (-H), critIntegrand K ρ v)
      ≤ 2 * (c * (X * J')) := by linarith [hI1', hI2']
  have h2X : 0 ≤ 2 * (c * (X * J')) :=
    mul_nonneg (by norm_num) (mul_nonneg hc_nn (mul_nonneg hX_nn hJ'nn))
  have hfin : 2 * (c * (X * J')) ≤ Kall * Real.sqrt T * X := by
    rw [hKalldef]
    have h2c : 2 * c * J' ≤ 4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T := by
      rw [show 2 * c * J' = (4 * Cz * Commons.Analysis.Complex.K6 * J') * Real.sqrt K by
            rw [hcdef]; ring]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKT)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCzpos.le) hK6pos.le) hJ'nn)
    calc 2 * (c * (X * J')) = (2 * c * J') * X := by ring
      _ ≤ (4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T) * X :=
            mul_le_mul_of_nonneg_right h2c hX_nn
      _ = 4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T * X := by ring
  calc Y ^ (1/2 - ρ.re) *
        ((∫ v in Set.Ioi H, critIntegrand K ρ v) + (∫ v in Set.Iic (-H), critIntegrand K ρ v))
      ≤ Y ^ (1/2 - ρ.re) * (2 * (c * (X * J'))) := mul_le_mul_of_nonneg_left hsum hYpow_nn
    _ ≤ 1 * (2 * (c * (X * J'))) := mul_le_mul_of_nonneg_right hYpow_le h2X
    _ = 2 * (c * (X * J')) := by ring
    _ ≤ Kall * Real.sqrt T * X := hfin
    _ ≤ Real.pi / 10 := by
        have hnum := hA₀main A hA T hT
        have heq : Kall * Real.sqrt T * X = Kall * Real.sqrt T * (3 + T + A*Real.log (A*T))^4
            * (1 + A*Real.log (A*T))^6 * Real.exp (-(Real.pi/2)*(A*Real.log (A*T))) := by
          rw [hXdef, hHdef]; ring
        rw [heq]; exact hnum

end Work.ZeroDensity.Ingham
