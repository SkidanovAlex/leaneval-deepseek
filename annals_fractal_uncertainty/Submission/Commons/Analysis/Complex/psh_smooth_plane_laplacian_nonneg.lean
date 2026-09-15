import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.Calculus.taylor_second_order_isLittleO

namespace Commons.Analysis.Complex

set_option autoImplicit false
open MeasureTheory


lemma integral_quadratic_circle {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] E →L[ℝ] F) (a b : E) :
    (∫ θ in (0:ℝ)..(2*Real.pi), L (Real.cos θ • a + Real.sin θ • b) (Real.cos θ • a + Real.sin θ • b))
      = Real.pi • (L a a + L b b) := by
  have h_expand : ∀ θ, L (Real.cos θ • a + Real.sin θ • b) (Real.cos θ • a + Real.sin θ • b)
      = (Real.cos θ)^2 • (L a a) + (Real.sin θ * Real.cos θ) • ((L a b) + (L b a))
        + (Real.sin θ)^2 • (L b b) := by
    intro θ
    simp only [map_add, map_smul, smul_apply, add_apply, smul_add, smul_smul]
    rw [mul_comm (Real.cos θ) (Real.sin θ)]
    module
  simp_rw [h_expand]
  have hcont : ∀ (g : ℝ → F), Continuous g → IntervalIntegrable g MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    fun g hg => hg.intervalIntegrable _ _
  have hA : IntervalIntegrable (fun θ => (Real.cos θ)^2 • (L a) a) MeasureTheory.volume 0 (2*Real.pi) :=
    hcont _ (by fun_prop)
  have hM : IntervalIntegrable (fun θ => (Real.sin θ * Real.cos θ) • ((L a) b + (L b) a)) MeasureTheory.volume 0 (2*Real.pi) :=
    hcont _ (by fun_prop)
  have hD : IntervalIntegrable (fun θ => (Real.sin θ)^2 • (L b) b) MeasureTheory.volume 0 (2*Real.pi) :=
    hcont _ (by fun_prop)
  rw [intervalIntegral.integral_add (f := fun θ => (Real.cos θ)^2 • (L a) a + (Real.sin θ * Real.cos θ) • ((L a) b + (L b) a)) (g := fun θ => (Real.sin θ)^2 • (L b) b) (hA.add hM) hD]
  rw [intervalIntegral.integral_add (f := fun θ => (Real.cos θ)^2 • (L a) a) (g := fun θ => (Real.sin θ * Real.cos θ) • ((L a) b + (L b) a)) hA hM]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [integral_cos_sq, integral_sin_mul_cos₁, integral_sin_sq]
  rw [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
  simp

lemma point_eq {d : ℕ} (w : Fin d → ℂ) (s θ : ℝ) :
    (fun j => Complex.exp (θ * Complex.I) * ((s : ℂ) * w j))
      = s • (Complex.exp (θ * Complex.I) • w) := by
  ext j
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

lemma point_eq_neg {d : ℕ} (w : Fin d → ℂ) (s θ : ℝ) :
    (fun j => Complex.exp (θ * Complex.I) * ((-(s : ℂ)) * w j))
      = - (s • (Complex.exp (θ * Complex.I) • w)) := by
  ext j
  simp only [Pi.neg_apply, Pi.smul_apply, Complex.real_smul, neg_mul]
  ring

lemma norm_exp_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma norm_smul_exp {d : ℕ} (w : Fin d → ℂ) (s θ : ℝ) :
    ‖s • (Complex.exp (θ * Complex.I) • w)‖ = |s| * ‖w‖ := by
  rw [norm_smul, norm_smul, norm_exp_I, Real.norm_eq_abs]
  ring

lemma exp_direction {d : ℕ} (w : Fin d → ℂ) (θ : ℝ) :
    Complex.exp (θ * Complex.I) • w = Real.cos θ • w + Real.sin θ • (Complex.I • w) := by
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, Complex.exp_mul_I, Complex.real_smul]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem psh_smooth_plane_laplacian_nonneg {d : ℕ} (φ : (Fin d → ℂ) → ℝ)
    (hφ : ContDiff ℝ 3 φ)
    (hsmv : ∀ z (v : Fin d → ℂ), φ z ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi),
      φ (z + fun j => Complex.exp (θ * Complex.I) * v j)) / (2 * Real.pi))
    (z w : Fin d → ℂ) :
    0 ≤ (iteratedFDeriv ℝ 2 φ z) ![w, w]
      + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w] := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  set L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ φ) z with hL
  set l : (Fin d → ℂ) →L[ℝ] ℝ := fderiv ℝ φ z with hl
  set R : (Fin d → ℂ) → ℝ := fun h => φ (z + h) - φ z - l h - (1/2:ℝ) • ((L h) h) with hRdef
  set u : ℝ → (Fin d → ℂ) := fun θ => Complex.exp (θ * Complex.I) • w with hudef
  set S : ℝ := (L w) w + (L (Complex.I • w)) (Complex.I • w) with hS
  have hgoal : (iteratedFDeriv ℝ 2 φ z) ![w, w]
      + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w] = S := by
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [hL, hS, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hgoal]
  have hR : R =o[nhds 0] fun h => ‖h‖ ^ 2 := by
    have h := Commons.Analysis.Calculus.taylor_second_order_isLittleO (f := φ) (x := z) hφ2
    rw [hRdef, hL, hl]
    exact h
  have hucont : Continuous u := by rw [hudef]; fun_prop
  have hRcont : Continuous R := by rw [hRdef]; fun_prop
  have hφcont : Continuous φ := hφ.continuous
  have hII : ∀ (f : ℝ → ℝ), Continuous f → IntervalIntegrable f MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    fun f hf => hf.intervalIntegrable _ _
  have hsmv1 : ∀ s : ℝ, φ z ≤ (∫ θ in (0:ℝ)..(2*Real.pi), φ (z + s • u θ)) / (2*Real.pi) := by
    intro s
    have h := hsmv z (fun j => (s:ℂ) * w j)
    simp only [point_eq] at h
    simpa [hudef] using h
  have hsmv2 : ∀ s : ℝ, φ z ≤ (∫ θ in (0:ℝ)..(2*Real.pi), φ (z - s • u θ)) / (2*Real.pi) := by
    intro s
    have h := hsmv z (fun j => (-(s:ℂ)) * w j)
    simp only [point_eq_neg] at h
    have hh : (fun θ => φ (z + - (s • u θ))) = fun θ => φ (z - s • u θ) := by
      ext θ; rw [sub_eq_add_neg]
    rw [hh] at h
    simpa [hudef] using h
  have hident : ∀ x : (Fin d → ℂ), φ (z + x) + φ (z - x) - 2 * φ z = (L x) x + R x + R (-x) := by
    intro x
    rw [hRdef]
    rw [show φ (z - x) = φ (z + (-x)) by rw [sub_eq_add_neg]]
    simp only [map_neg, neg_apply, neg_neg, smul_eq_mul]
    ring
  have hkey : ∀ s : ℝ, 0 ≤ (∫ θ in (0:ℝ)..(2*Real.pi), (L (s • u θ)) (s • u θ))
      + (∫ θ in (0:ℝ)..(2*Real.pi), (R (s • u θ) + R (-(s • u θ)))) := by
    intro s
    have h1 := hsmv1 s
    have h2 := hsmv2 s
    have hint1 : IntervalIntegrable (fun θ => φ (z + s • u θ)) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (hφcont.comp (by fun_prop))
    have hint2 : IntervalIntegrable (fun θ => φ (z - s • u θ)) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (hφcont.comp (by fun_prop))
    have hadd : 2 * φ z ≤ (∫ θ in (0:ℝ)..(2*Real.pi), (φ (z + s • u θ) + φ (z - s • u θ))) / (2*Real.pi) := by
      have hsum := add_le_add h1 h2
      have hff : (∫ θ in (0:ℝ)..(2*Real.pi), φ (z + s • u θ)) / (2*Real.pi)
          + (∫ θ in (0:ℝ)..(2*Real.pi), φ (z - s • u θ)) / (2*Real.pi)
          = (∫ θ in (0:ℝ)..(2*Real.pi), (φ (z + s • u θ) + φ (z - s • u θ))) / (2*Real.pi) := by
        rw [← add_div, intervalIntegral.integral_add hint1 hint2]
      rw [hff] at hsum
      linarith [hsum]
    have h2pi : 2 * φ z * (2*Real.pi) ≤ (∫ θ in (0:ℝ)..(2*Real.pi), (φ (z + s • u θ) + φ (z - s • u θ))) :=
      (le_div_iff₀ (by positivity)).mp hadd
    have hpoint : ∀ θ, φ (z + s • u θ) + φ (z - s • u θ)
        = 2 * φ z + ((L (s • u θ)) (s • u θ) + (R (s • u θ) + R (-(s • u θ)))) := by
      intro θ
      have hx := hident (s • u θ)
      linarith [hx]
    have hIntA : IntervalIntegrable (fun θ => (L (s • u θ)) (s • u θ)) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (by fun_prop)
    have hIntB : IntervalIntegrable (fun θ => R (s • u θ) + R (-(s • u θ))) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (by fun_prop)
    have hIntg : IntervalIntegrable (fun θ => (L (s • u θ)) (s • u θ) + (R (s • u θ) + R (-(s • u θ)))) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (by fun_prop)
    have hsplit : (∫ θ in (0:ℝ)..(2*Real.pi), (φ (z + s • u θ) + φ (z - s • u θ)))
        = 2 * φ z * (2*Real.pi) + ((∫ θ in (0:ℝ)..(2*Real.pi), (L (s • u θ)) (s • u θ))
            + (∫ θ in (0:ℝ)..(2*Real.pi), (R (s • u θ) + R (-(s • u θ))))) := by
      simp_rw [hpoint]
      rw [intervalIntegral.integral_add (f := fun _ : ℝ => 2 * φ z) (g := fun θ => (L (s • u θ)) (s • u θ) + (R (s • u θ) + R (-(s • u θ)))) (hII _ continuous_const) hIntg]
      rw [intervalIntegral.integral_const]
      rw [intervalIntegral.integral_add (f := fun θ => (L (s • u θ)) (s • u θ)) (g := fun θ => R (s • u θ) + R (-(s • u θ))) hIntA hIntB]
      simp only [smul_eq_mul]
      ring
    linarith [h2pi, hsplit]
  have hAval : ∀ s : ℝ, (∫ θ in (0:ℝ)..(2*Real.pi), (L (s • u θ)) (s • u θ)) = s^2 * (Real.pi * S) := by
    intro s
    have hpt : ∀ θ, (L (s • u θ)) (s • u θ) = s^2 • ((L (u θ)) (u θ)) := by
      intro θ
      simp only [map_smul, smul_apply, smul_smul, sq]
    have hInt : (∫ θ in (0:ℝ)..(2*Real.pi), (L (u θ)) (u θ)) = Real.pi * S := by
      have hpt2 : ∀ θ, u θ = Real.cos θ • w + Real.sin θ • (Complex.I • w) := by
        intro θ; rw [hudef]; exact exp_direction w θ
      simp_rw [hpt2]
      rw [integral_quadratic_circle L w (Complex.I • w), hS]
      simp only [smul_eq_mul]
    simp_rw [hpt]
    rw [intervalIntegral.integral_smul, hInt]
    simp only [smul_eq_mul]
  have hBbound : ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, |s| * ‖w‖ < δ →
      |(∫ θ in (0:ℝ)..(2*Real.pi), (R (s • u θ) + R (-(s • u θ))))| ≤ 4 * Real.pi * ε * |s|^2 * ‖w‖^2 := by
    intro ε hε
    rw [Asymptotics.isLittleO_iff] at hR
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (hR hε)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hpt : ∀ θ, |R (s • u θ) + R (-(s • u θ))| ≤ 2 * ε * (|s| * ‖w‖)^2 := by
      intro θ
      have hd1 : dist (s • u θ) (0:Fin d → ℂ) < δ := by
        rw [dist_zero_right, norm_smul_exp]; exact hs
      have hd2 : dist (-(s • u θ)) (0:Fin d → ℂ) < δ := by
        rw [dist_zero_right, norm_neg, norm_smul_exp]; exact hs
      have h1 := hδ' hd1
      have h2 := hδ' hd2
      rw [norm_smul_exp, Real.norm_of_nonneg (sq_nonneg (|s| * ‖w‖))] at h1
      rw [norm_neg, norm_smul_exp, Real.norm_of_nonneg (sq_nonneg (|s| * ‖w‖))] at h2
      have h3 : |R (s • u θ) + R (-(s • u θ))| ≤ ‖R (s • u θ)‖ + ‖R (-(s • u θ))‖ := by
        rw [← Real.norm_eq_abs]; exact norm_add_le _ _
      linarith [h3, h1, h2, sq_nonneg (|s| * ‖w‖)]
    have hInt : IntervalIntegrable (fun θ => |R (s • u θ) + R (-(s • u θ))|) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ (by fun_prop)
    have hInt2 : IntervalIntegrable (fun _ : ℝ => 2 * ε * (|s| * ‖w‖)^2) MeasureTheory.volume 0 (2*Real.pi) :=
      hII _ continuous_const
    have h1 : |∫ θ in (0:ℝ)..(2*Real.pi), (R (s • u θ) + R (-(s • u θ)))| ≤
        ∫ θ in (0:ℝ)..(2*Real.pi), |R (s • u θ) + R (-(s • u θ))| :=
      intervalIntegral.abs_integral_le_integral_abs (by positivity)
    have h2 : (∫ θ in (0:ℝ)..(2*Real.pi), |R (s • u θ) + R (-(s • u θ))|) ≤
        ∫ θ in (0:ℝ)..(2*Real.pi), (fun _ : ℝ => 2 * ε * (|s| * ‖w‖)^2) θ :=
      intervalIntegral.integral_mono (by positivity) hInt hInt2 hpt
    have h3 : (∫ θ in (0:ℝ)..(2*Real.pi), (fun _ : ℝ => 2 * ε * (|s| * ‖w‖)^2) θ) = 4 * Real.pi * ε * |s|^2 * ‖w‖^2 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    linarith [h1, h2, h3]
  have hfinal : ∀ ε > 0, -4 * ε * ‖w‖^2 ≤ S := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hBbound ε hε
    set s : ℝ := δ / (2 * (‖w‖ + 1)) with hsdef
    have hs_pos : 0 < s := by rw [hsdef]; positivity
    have hsW : |s| * ‖w‖ < δ := by
      rw [hsdef, abs_of_pos (by positivity)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w, hδ]
    have hB_le := (abs_le.mp (hδ' s hsW)).2
    rw [sq_abs s] at hB_le
    have hk := hkey s
    rw [hAval s] at hk
    have h1 : (s^2 * Real.pi) * (-(4*ε*‖w‖^2)) ≤ (s^2 * Real.pi) * S := by
      nlinarith [hk, hB_le]
    have hfac : 0 < s^2 * Real.pi := mul_pos (pow_pos hs_pos 2) Real.pi_pos
    have h2 : -(4*ε*‖w‖^2) ≤ S := by nlinarith [h1, hfac]
    linarith [h2]
  have hSnn : 0 ≤ S := by
    apply le_of_forall_pos_le_add
    intro η hη
    have h := hfinal (η / (4 * (‖w‖^2 + 1))) (by positivity)
    have hle : 4 * (η / (4 * (‖w‖^2 + 1))) * ‖w‖^2 ≤ η := by
      have hW : (0:ℝ) < ‖w‖^2 + 1 := by positivity
      field_simp
      nlinarith [hη, norm_nonneg w]
    linarith [h, hle]
  exact hSnn

end Commons.Analysis.Complex