import Mathlib
import Submission.Commons.Analysis.Integral.average_inv_parabolic_circle_neg
import Submission.Commons.Analysis.InnerProductSpace.norm_smul_orthonormal_cos_sin

set_option maxHeartbeats 3200000

open MeasureTheory Set Real
open scoped InnerProductSpace

namespace Commons.Analysis.Integral

private lemma intervalIntegral_shift_pi {u : ℝ → ℝ} (hu : Function.Periodic u (2 * Real.pi)) :
    ∫ θ in (0)..(2 * Real.pi), u (θ + Real.pi) = ∫ θ in (0)..(2 * Real.pi), u θ := by
  rw [intervalIntegral.integral_comp_add_right (f := u) (d := Real.pi)]
  rw [show (0:ℝ) + Real.pi = Real.pi by ring,
      show (2*Real.pi) + Real.pi = Real.pi + 2 * Real.pi by ring]
  rw [hu.intervalIntegral_add_eq (t := Real.pi) (s := 0)]
  rw [show (0:ℝ) + 2 * Real.pi = 2 * Real.pi by ring]

private noncomputable def φf (t : ℝ) : ℝ := t ^ (-(2:ℝ)/3)
private noncomputable def φf' (t : ℝ) : ℝ := (-(2:ℝ)/3) * t ^ (-(5:ℝ)/3)

private lemma φf_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt φf (φf' t) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := (-(2:ℝ)/3)) (Or.inl (ne_of_gt ht))
  have he : (-(2:ℝ)/3 - 1) = (-(5:ℝ)/3) := by norm_num
  rw [he] at h
  exact h

private lemma φf_inj : InjOn φf (Set.Ioi 0) := by
  intro t ht s hs h
  have ht0 : 0 < t := ht
  have hs0 : 0 < s := hs
  have ht' : (t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = t := by
    rw [← Real.rpow_mul ht0.le]
    rw [show (-(2:ℝ)/3) * (-(3:ℝ)/2) = (1:ℝ) by norm_num, Real.rpow_one]
  have hs' : (s ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = s := by
    rw [← Real.rpow_mul hs0.le]
    rw [show (-(2:ℝ)/3) * (-(3:ℝ)/2) = (1:ℝ) by norm_num, Real.rpow_one]
  have hφ : φf t = φf s := h
  calc t = (φf t) ^ (-(3:ℝ)/2) := ht'.symm
    _ = (φf s) ^ (-(3:ℝ)/2) := by rw [hφ]
    _ = s := hs'

private lemma φf_image : φf '' Set.Ioi 0 = Set.Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact Real.rpow_pos_of_pos hx _
  · intro y hy
    refine ⟨y ^ (-(3:ℝ)/2), Real.rpow_pos_of_pos hy _, ?_⟩
    rw [φf, ← Real.rpow_mul hy.le]
    rw [show (-(3:ℝ)/2) * (-(2:ℝ)/3) = (1:ℝ) by norm_num, Real.rpow_one]

private noncomputable def G (v : ℝ) : ℝ :=
  ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
      (((1 + v ^ 2 + 2 * v * Real.cos θ) ^ (-(1:ℝ)/2)) - 1)) * v ^ (-(3:ℝ)/2)

private noncomputable def U (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
      (((t ^ (4/3:ℝ) + 1 + 2 * t ^ (2/3:ℝ) * Real.cos θ) ^ (-(1:ℝ)/2)) - t ^ (-(2:ℝ)/3))

private lemma key_base (t : ℝ) (ht : 0 < t) (θ : ℝ) :
    1 + (φf t) ^ 2 + 2 * (φf t) * Real.cos θ
      = t ^ (-(4:ℝ)/3) * (t ^ (4/3:ℝ) + 1 + 2 * t ^ (2/3:ℝ) * Real.cos θ) := by
  have hsq : (φf t) ^ 2 = t ^ (-(4:ℝ)/3) := by
    rw [φf, pow_two, ← Real.rpow_add ht]
    norm_num
  have h1 : t ^ (-(4:ℝ)/3) * t ^ (4/3:ℝ) = 1 := by
    rw [← Real.rpow_add ht]; norm_num
  have h2 : t ^ (-(4:ℝ)/3) * t ^ (2/3:ℝ) = t ^ (-(2:ℝ)/3) := by
    rw [← Real.rpow_add ht]; norm_num
  have hexp : t ^ (-(4:ℝ)/3) * (t ^ (4/3:ℝ) + 1 + 2 * t ^ (2/3:ℝ) * Real.cos θ)
      = t ^ (-(4:ℝ)/3) * t ^ (4/3:ℝ) + t ^ (-(4:ℝ)/3)
        + (t ^ (-(4:ℝ)/3) * t ^ (2/3:ℝ)) * (2 * Real.cos θ) := by ring
  rw [hsq]
  simp only [φf]
  rw [hexp, h1, h2]; ring

private lemma key_nonneg (t : ℝ) (ht : 0 < t) (θ : ℝ) :
    (0:ℝ) ≤ t ^ (4/3:ℝ) + 1 + 2 * t ^ (2/3:ℝ) * Real.cos θ := by
  have h1 : t ^ (2/3:ℝ) * t ^ (2/3:ℝ) = t ^ (4/3:ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (t ^ (2/3:ℝ) + Real.cos θ), sq_nonneg (Real.sin θ), h1, h2]

private lemma key_algebra (t : ℝ) (ht : 0 < t) (θ : ℝ) :
    ((1 + (φf t) ^ 2 + 2 * (φf t) * Real.cos θ) ^ (-(1:ℝ)/2))
      = t ^ (2/3:ℝ) * ((t ^ (4/3:ℝ) + 1 + 2 * t ^ (2/3:ℝ) * Real.cos θ) ^ (-(1:ℝ)/2)) := by
  rw [key_base t ht θ]
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ t ^ (-(4:ℝ)/3)) (key_nonneg t ht θ)]
  rw [← Real.rpow_mul ht.le]
  rw [show (-(4:ℝ)/3) * (-(1:ℝ)/2) = (2:ℝ)/3 by norm_num]

private lemma key_pow (t : ℝ) (ht : 0 < t) : (φf t) ^ (-(3:ℝ)/2) = t := by
  rw [φf, ← Real.rpow_mul ht.le]
  rw [show (-(2:ℝ)/3) * (-(3:ℝ)/2) = (1:ℝ) by norm_num, Real.rpow_one]

private lemma G_phi_eq (t : ℝ) (ht : 0 < t) :
    |φf' t| * G (φf t) = (2/3) * U t := by
  have habs : |φf' t| = (2/3) * t ^ (-(5:ℝ)/3) := by
    rw [φf', abs_mul, abs_of_neg (by norm_num : (-(2:ℝ)/3) < 0),
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
    norm_num
  have hpow : (φf t) ^ (-(3:ℝ)/2) = t := key_pow t ht
  set J : ℝ := ∫ θ in (0)..(2*Real.pi),
            (((t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) - t ^ (-(2:ℝ)/3)) with hJ
  have inner : (∫ θ in (0)..(2*Real.pi), (((1 + (φf t)^2 + 2*(φf t)*Real.cos θ) ^ (-(1:ℝ)/2)) - 1))
      = t ^ (2/3:ℝ) * J := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    beta_reduce
    rw [key_algebra t ht θ]
    have hmul1 : t ^ (2/3:ℝ) * t ^ (-(2:ℝ)/3) = 1 := by
      rw [← Real.rpow_add ht]; norm_num
    rw [mul_sub, hmul1]
  have hG : G (φf t) = ((1/(2*Real.pi)) * (t ^ (2/3:ℝ) * J)) * t := by
    unfold G
    rw [inner, hpow]
  have hkey : t ^ (-(5:ℝ)/3) * t ^ (2/3:ℝ) * t = 1 := by
    have h1 : t ^ (-(5:ℝ)/3) * t ^ (2/3:ℝ) = t ^ (-(5:ℝ)/3 + 2/3) := (Real.rpow_add ht _ _).symm
    rw [show (-(5:ℝ)/3 + 2/3) = (-(1:ℝ)) by norm_num] at h1
    have h2 : t ^ (-(1:ℝ)) * t = t ^ (-(1:ℝ) + 1) := by
      have hh := (Real.rpow_add ht (-(1:ℝ)) 1).symm
      rwa [Real.rpow_one] at hh
    rw [h1, h2, show (-(1:ℝ) + 1) = 0 by norm_num, Real.rpow_zero]
  have hL : (2/3) * t ^ (-(5:ℝ)/3) * (((1/(2*Real.pi)) * (t ^ (2/3:ℝ) * J)) * t)
      = (2/3) * (1/(2*Real.pi)) * J * (t ^ (-(5:ℝ)/3) * t ^ (2/3:ℝ) * t) := by ring
  rw [habs, hG, hL, hkey]
  rw [U, hJ]
  ring

private lemma subst_key :
    (∫ v in Set.Ioi (0:ℝ), G v) = (2/3) * (∫ t in Set.Ioi (0:ℝ), U t) := by
  have himg := integral_image_eq_integral_abs_deriv_smul
      (f := φf) (f' := φf') (s := Set.Ioi (0:ℝ)) measurableSet_Ioi
      (fun t ht => (φf_hasDerivAt ht).hasDerivWithinAt) φf_inj G
  rw [φf_image] at himg
  rw [himg]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  beta_reduce
  rw [smul_eq_mul]
  exact G_phi_eq t ht

private lemma A_ne_zero (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) (θ : ℝ) :
    t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ ≠ 0 := by
  intro h0
  have h2 : t^(2/3:ℝ)*t^(2/3:ℝ) = t^(4/3:ℝ) := by rw [← Real.rpow_add ht]; norm_num
  have hkey : t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ - (t^(2/3:ℝ)-1)^2
      = 2*t^(2/3:ℝ)*(1+Real.cos θ) := by rw [← h2]; ring
  have hnonneg : 0 ≤ 2*t^(2/3:ℝ)*(1+Real.cos θ) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos ht _).le)
    linarith [Real.neg_one_le_cos θ]
  have hle : (t^(2/3:ℝ)-1)^2 ≤ 0 := by
    rw [h0] at hkey; linarith [hkey, hnonneg]
  have hsq0 : (t^(2/3:ℝ)-1)^2 = 0 := le_antisymm hle (sq_nonneg _)
  have ha1 : t^(2/3:ℝ) = 1 := by have := sq_eq_zero_iff.mp hsq0; linarith
  have hpow : (t^(2/3:ℝ))^(3/2:ℝ) = t := by
    rw [← Real.rpow_mul ht.le]
    rw [show (2/3:ℝ)*(3/2:ℝ) = 1 by norm_num, Real.rpow_one]
  exact ht1 (by rw [← hpow, ha1, Real.one_rpow])

private lemma A'_ne_zero (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) (θ : ℝ) :
    t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ ≠ 0 := by
  intro h0
  have h2 : t^(2/3:ℝ)*t^(2/3:ℝ) = t^(4/3:ℝ) := by rw [← Real.rpow_add ht]; norm_num
  have hkey : t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ - (t^(2/3:ℝ)-1)^2
      = 2*t^(2/3:ℝ)*(1-Real.cos θ) := by rw [← h2]; ring
  have hnonneg : 0 ≤ 2*t^(2/3:ℝ)*(1-Real.cos θ) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos ht _).le)
    linarith [Real.cos_le_one θ]
  have hle : (t^(2/3:ℝ)-1)^2 ≤ 0 := by
    rw [h0] at hkey; linarith [hkey, hnonneg]
  have hsq0 : (t^(2/3:ℝ)-1)^2 = 0 := le_antisymm hle (sq_nonneg _)
  have ha1 : t^(2/3:ℝ) = 1 := by have := sq_eq_zero_iff.mp hsq0; linarith
  have hpow : (t^(2/3:ℝ))^(3/2:ℝ) = t := by
    rw [← Real.rpow_mul ht.le]
    rw [show (2/3:ℝ)*(3/2:ℝ) = 1 by norm_num, Real.rpow_one]
  exact ht1 (by rw [← hpow, ha1, Real.one_rpow])

private lemma norm_eq (t : ℝ) (ht : 0 < t) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (θ : ℝ) :
    (‖(1 * t ^ (2/3:ℝ)) • e - (1:ℝ) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
      = (t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2) := by
  have hnormid := Commons.Analysis.InnerProductSpace.norm_smul_orthonormal_cos_sin e f he hf hef
      (1 * t ^ (2/3:ℝ)) (1:ℝ) θ
  rw [hnormid]
  simp only [one_mul]
  have hA : (t^(2/3:ℝ) - Real.cos θ)^2 + (Real.sin θ)^2 = t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ := by
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 : t^(2/3:ℝ)*t^(2/3:ℝ) = t^(4/3:ℝ) := by rw [← Real.rpow_add ht]; norm_num
    nlinarith [h1, h2]
  rw [hA, Real.sqrt_eq_rpow, ← Real.rpow_neg (show (0:ℝ) ≤ t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ by
      rw [← hA]; positivity)]
  congr 1
  norm_num

private lemma split_const {j : ℝ → ℝ} (hj : Continuous j) (c : ℝ) :
    (∫ θ in (0)..(2*Real.pi), (j θ - c)) = (∫ θ in (0)..(2*Real.pi), j θ) - (2*Real.pi)*c := by
  rw [intervalIntegral.integral_sub (hj.intervalIntegrable _ _)
        (intervalIntegrable_const (c := c)), intervalIntegral.integral_const]
  rw [smul_eq_mul]; ring

private lemma U_eq_commons (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    U t = ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
            ((‖(1 * t ^ (2/3:ℝ)) • e - (1:ℝ) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
              - (1 * t ^ (2/3:ℝ))⁻¹)) := by
  have hbase : Continuous (fun θ : ℝ => t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ) := by fun_prop
  have hbase' : Continuous (fun θ : ℝ => t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) := by fun_prop
  have hcont1 : Continuous (fun θ : ℝ => (t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) :=
      hbase.rpow_const (fun θ => Or.inl (A_ne_zero t ht ht1 θ))
  have hcont2 : Continuous (fun θ : ℝ => (t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) :=
      hbase'.rpow_const (fun θ => Or.inl (A'_ne_zero t ht ht1 θ))
  have hshift : (∫ θ in (0)..(2*Real.pi), (t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2))
      = (∫ θ in (0)..(2*Real.pi), (t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) := by
    have hu : Function.Periodic
        (fun θ : ℝ => (t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) (2*Real.pi) := by
      intro x; simp only [Real.cos_add_two_pi]
    have h := intervalIntegral_shift_pi hu
    have hcongr : (∫ θ in (0)..(2*Real.pi),
          (fun ψ : ℝ => (t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos ψ) ^ (-(1:ℝ)/2)) (θ + Real.pi))
        = (∫ θ in (0)..(2*Real.pi), (t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      beta_reduce
      rw [Real.cos_add_pi]
      rw [show t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*(-(Real.cos θ)) = t^(4/3:ℝ)+1+2*t^(2/3:ℝ)*Real.cos θ by ring]
    exact hcongr.symm.trans h
  have hfin : (1*t^(2/3:ℝ))⁻¹ = t^(-(2:ℝ)/3) := by
    rw [one_mul, ← Real.rpow_neg ht.le]
    congr 1
    norm_num
  have hcongR : (∫ θ in (0)..(2*Real.pi),
          ((‖(1 * t ^ (2/3:ℝ)) • e - (1:ℝ) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
            - t^(-(2:ℝ)/3)))
      = (∫ θ in (0)..(2*Real.pi),
          ((t^(4/3:ℝ)+1-2*t^(2/3:ℝ)*Real.cos θ) ^ (-(1:ℝ)/2) - t^(-(2:ℝ)/3))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    beta_reduce
    rw [norm_eq t ht e f he hf hef θ]
  have hL := split_const hcont1 (t^(-(2:ℝ)/3))
  have hR := hcongR.trans (split_const hcont2 (t^(-(2:ℝ)/3)))
  rw [U, hfin, hL, hR, hshift]



theorem integral_phi_rpow_neg_three_halves_neg :
    ∫ v in Set.Ioi (0 : ℝ),
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
            (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
          * v ^ (-(3 : ℝ) / 2)
      < 0 := by
  let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let f : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have he : ‖e‖ = 1 := by rw [PiLp.norm_single]; norm_num
  have hf : ‖f‖ = 1 := by rw [PiLp.norm_single]; norm_num
  have hef : inner ℝ e f = 0 := by rw [EuclideanSpace.inner_single_left]; simp [f]
  have hmain := average_inv_parabolic_circle_neg (d := 2) (by norm_num) (c := 1) (rho := 1)
      (by norm_num) (by norm_num) e f he hf hef
  change (∫ v in Set.Ioi (0:ℝ), G v) < 0
  rw [subst_key]
  have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (1:ℝ) := by rw [ae_iff]; simp
  have hUeq : (∫ t in Set.Ioi (0:ℝ), U t)
      = (∫ t in Set.Ioi (0:ℝ), ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
            ((‖(1 * t ^ (2/3:ℝ)) • e - (1:ℝ) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
              - (1 * t ^ (2/3:ℝ))⁻¹))) := by
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [hae1] with t ht1 htmem
    exact U_eq_commons t htmem ht1 e f he hf hef
  have hUneg : (∫ t in Set.Ioi (0:ℝ), U t) < 0 := by
    rw [hUeq]
    exact hmain
  linarith [hUneg]

end Commons.Analysis.Integral
