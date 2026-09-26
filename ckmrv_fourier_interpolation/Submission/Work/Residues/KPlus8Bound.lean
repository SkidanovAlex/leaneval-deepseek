import Mathlib
import Submission.Work.Residues.KPlusAux

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues
open Work.Kernels
open Work.Residues.KPlusAux

set_option maxHeartbeats 8000000

/-! ## The `d = 8` bound -/

theorem kplus_eight_bound (z : ℍ) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im → ‖KPlus 8 τ z‖ ≤ C * ‖(τ:ℂ)‖ * eps τ := by
  obtain ⟨H2, K2, hK2, hb2⟩ := E2_decay_bound
  obtain ⟨H4, K4, hK4, hb4⟩ := E4_decay_bound
  obtain ⟨H6, K6, hK6, hb6⟩ := E6_decay_bound
  obtain ⟨HD, KD, hKD, hbD⟩ := Delta_decay_bound
  set K0 : ℝ := K2 + K4 + K6 + KD + 1 with hK0
  have hK2' : K2 ≤ K0 := by rw [hK0]; linarith
  have hK4' : K4 ≤ K0 := by rw [hK0]; linarith
  have hK6' : K6 ≤ K0 := by rw [hK0]; linarith
  have hKD' : KD ≤ K0 := by rw [hK0]; linarith
  have hK1' : 1 ≤ K0 := by rw [hK0]; linarith
  have hK0pos : 0 < K0 := lt_of_lt_of_le zero_lt_one hK1'
  set Kz : ℝ := 7 + ‖jInvariantFun z‖ + 1 with hKz
  have hKz1 : 1 ≤ Kz := by rw [hKz]; linarith [norm_nonneg (jInvariantFun z)]
  have hKz0 : 0 ≤ Kz := le_trans zero_le_one hKz1
  set K1 : ℝ := K0 + 2 * Kz * K0 + 1 with hK1
  have hK10 : 0 < K1 := by rw [hK1]; nlinarith [hK0pos, hKz1]
  have hK0le : K0 ≤ K1 := by rw [hK1]; nlinarith [hK0pos, hKz1]
  have hKzle : 2 * Kz * K0 ≤ K1 := by rw [hK1]; linarith
  have hK1ge1 : 1 ≤ K1 := le_trans hK1' hK0le
  set Hbig : ℝ := Real.log (100 * K1) / (2 * Real.pi) with hHbig
  set Hz : ℝ := max H2 (max H4 (max H6 (max HD (max Hbig 1)))) with hHz
  set Cz : ℝ := ‖phitVec z 0‖ * 1000 + (‖phitVec z 2‖ * (2 * ‖E8Fun z‖)
      + 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖)) * (2/‖DeltaFun z‖) + 1 with hCz
  refine ⟨Hz, (Real.pi^2/36) * Cz * K1 + 1, by positivity, fun τ hτ => ?_⟩
  have hy2 : H2 ≤ τ.im := by rw [hHz] at hτ; exact le_trans (le_max_left _ _) hτ
  have hy4 : H4 ≤ τ.im := by
    rw [hHz] at hτ; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτ)
  have hy6 : H6 ≤ τ.im := by
    rw [hHz] at hτ
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))
  have hyD : HD ≤ τ.im := by
    rw [hHz] at hτ
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ)))
  have hybig : Hbig ≤ τ.im := by
    rw [hHz] at hτ
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))))
  have hy1 : 1 ≤ τ.im := by
    rw [hHz] at hτ
    exact le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))))) hτ
  -- the `q`-scale
  have hlog : Real.log (100 * K1) ≤ 2 * Real.pi * τ.im := by
    have h : (2 * Real.pi) * Hbig ≤ (2 * Real.pi) * τ.im :=
      mul_le_mul_of_nonneg_left hybig (by positivity)
    have h2 : (2 * Real.pi) * Hbig = Real.log (100 * K1) := by
      rw [hHbig]; field_simp
    linarith [h, h2]
  have heps : eps τ ≤ (100 * K1)⁻¹ := by
    rw [eps]
    calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(Real.log (100 * K1))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = (100 * K1)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
  have hm100 : K1 * eps τ ≤ 1/100 := by
    have h := mul_le_mul_of_nonneg_left heps hK10.le
    have h2 : K1 * (100 * K1)⁻¹ = 1/100 := by
      field_simp
    rwa [h2] at h
  set m : ℝ := K1 * eps τ with hm
  have hm0 : 0 ≤ m := by rw [hm]; exact mul_nonneg hK10.le (eps_pos τ).le
  have hm1 : m ≤ 1 := by rw [hm]; linarith [hm100, hK1ge1]
  -- decay bounds, first with `K0`
  have h20 : ‖E2Fun τ - 1‖ ≤ K0 * eps τ := by
    have h := hb2 τ hy2
    have h' : K2 * eps τ ≤ K0 * eps τ := mul_le_mul_of_nonneg_right hK2' (eps_pos τ).le
    linarith
  have h40 : ‖E4Fun τ - 1‖ ≤ K0 * eps τ := by
    have h := hb4 τ hy4
    have h' : K4 * eps τ ≤ K0 * eps τ := mul_le_mul_of_nonneg_right hK4' (eps_pos τ).le
    linarith
  have h60 : ‖E6Fun τ - 1‖ ≤ K0 * eps τ := by
    have h := hb6 τ hy6
    have h' : K6 * eps τ ≤ K0 * eps τ := mul_le_mul_of_nonneg_right hK6' (eps_pos τ).le
    linarith
  have hD0 : ‖DeltaFun τ‖ ≤ K0 * eps τ := by
    have h := hbD τ hyD
    have h' : KD * eps τ ≤ K0 * eps τ := mul_le_mul_of_nonneg_right hKD' (eps_pos τ).le
    linarith
  have hK0e0 : 0 ≤ K0 * eps τ := mul_nonneg hK0pos.le (eps_pos τ).le
  have hmE4cube : ‖E4Fun τ ^ 3 - 1‖ ≤ 7 * (K0 * eps τ) := by
    have hE : E4Fun τ ^ 3 - 1 = (E4Fun τ - 1) * (E4Fun τ ^ 2 + E4Fun τ + 1) := by ring
    rw [hE]
    have h2' : ‖E4Fun τ‖ ≤ 2 := norm_le_two h40 (by nlinarith [hK0e0, hm100])
    have hb : ‖E4Fun τ ^ 2 + E4Fun τ + 1‖ ≤ 7 := by
      rw [show E4Fun τ ^ 2 + E4Fun τ + 1 = (E4Fun τ ^ 2 + E4Fun τ) + 1 from by ring]
      have h := norm_add_le (E4Fun τ ^ 2 + E4Fun τ) (1:ℂ)
      rw [norm_one] at h
      have h' := norm_add_le (E4Fun τ ^ 2) (E4Fun τ)
      rw [norm_pow] at h'
      nlinarith [norm_nonneg (E4Fun τ), norm_nonneg (E4Fun τ ^ 2), h, h', h2']
    have h := norm_mul_le_mul h40 hb hK0e0
    linarith [h]
  -- transfer to `m`
  have hm2 : ‖E2Fun τ - 1‖ ≤ m := by
    have h' : K0 * eps τ ≤ K1 * eps τ := mul_le_mul_of_nonneg_right hK0le (eps_pos τ).le
    rw [hm]; linarith
  have hm4 : ‖E4Fun τ - 1‖ ≤ m := by
    have h' : K0 * eps τ ≤ K1 * eps τ := mul_le_mul_of_nonneg_right hK0le (eps_pos τ).le
    rw [hm]; linarith
  have hm6 : ‖E6Fun τ - 1‖ ≤ m := by
    have h' : K0 * eps τ ≤ K1 * eps τ := mul_le_mul_of_nonneg_right hK0le (eps_pos τ).le
    rw [hm]; linarith
  have hmD : ‖DeltaFun τ‖ ≤ m := by
    have h' : K0 * eps τ ≤ K1 * eps τ := mul_le_mul_of_nonneg_right hK0le (eps_pos τ).le
    rw [hm]; linarith
  -- the `h`-factor `kph τ z`
  set v : ℂ := E4Fun τ ^ 3 - DeltaFun τ * jInvariantFun z with hv
  have hv1 : ‖v - 1‖ ≤ Kz * (K0 * eps τ) := by
    have hE : v - 1 = (E4Fun τ ^ 3 - 1) + (-(DeltaFun τ * jInvariantFun z)) := by rw [hv]; ring
    rw [hE]
    have h := norm_add_le (E4Fun τ ^ 3 - 1) (-(DeltaFun τ * jInvariantFun z))
    rw [norm_neg] at h
    have hD2 : ‖DeltaFun τ * jInvariantFun z‖ ≤ (K0 * eps τ) * ‖jInvariantFun z‖ :=
      norm_mul_le_mul hD0 le_rfl hK0e0
    have hKz' : 7 + ‖jInvariantFun z‖ ≤ Kz := by rw [hKz]; linarith
    nlinarith [h, hmE4cube, hD2, hKz', norm_nonneg (jInvariantFun z), eps_pos τ, hK0pos]
  have hveps : Kz * (K0 * eps τ) ≤ 1/2 := by
    have h2 : Kz * (K0 * (100 * K1)⁻¹) ≤ 1/2 := by
      have h1 : Kz * (K0 * (100 * K1)⁻¹) = Kz * K0 / (100 * K1) := by rw [mul_inv]; ring
      rw [h1, div_le_iff₀ (by positivity)]
      nlinarith [hKzle, hKz1, hK0pos, hK10]
    calc Kz * (K0 * eps τ) ≤ Kz * (K0 * (100 * K1)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hKz0
          exact mul_le_mul_of_nonneg_left heps hK0pos.le
      _ ≤ 1/2 := h2
  have hv0 : 0 ≤ Kz * (K0 * eps τ) := mul_nonneg hKz0 hK0e0
  -- transfer to `kph`
  have hkph_eq : kph τ z = v⁻¹ := by
    have h : DeltaFun τ * kpJ τ z = v := by
      have h1 : DeltaFun τ * kpJ τ z
          = DeltaFun τ * jInvariantFun τ - DeltaFun τ * jInvariantFun z := by
        rw [kpJ]; ring
      rw [h1, hv, delta_mul_j]
    rw [kph, h]
  have hmh : ‖kph τ z - 1‖ ≤ m := by
    rw [hkph_eq]
    have h := norm_sub_one_inv_le hv0 hveps hv1
    have hm2' : 2 * (Kz * (K0 * eps τ)) ≤ m := by
      rw [hm, hK1]
      nlinarith [eps_pos τ, hK0pos, hKz1]
    linarith [h, hm2']
  have hkph2 : ‖kph τ z‖ ≤ 2 := by
    have h := norm_add_le (kph τ z - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith [h, hmh, hm1]
  have hJinv_eq : (kpJ τ z)⁻¹ = DeltaFun τ * kph τ z := by
    rw [kph]
    exact inv_eq_mul_inv_of_ne_zero (delta_ne_zero τ)
  have hJinv1 : ‖(kpJ τ z)⁻¹‖ ≤ 2 * m := by
    rw [hJinv_eq]
    have h := norm_mul_le_mul hmD hkph2 hm0
    linarith [h, hm0]
  have hJinv : ‖(DeltaFun z * kpJ τ z)⁻¹‖ ≤ 2 * m / ‖DeltaFun z‖ :=
    norm_mul_inv_le hJinv1
  have hJnz : kpJ τ z ≠ 0 := by
    intro hJ0
    have h1 : kph τ z = 0 := by rw [kph, hJ0, mul_zero, _root_.inv_zero]
    have h2 : ‖kph τ z - 1‖ ≤ m := hmh
    rw [h1] at h2
    norm_num at h2
    rw [hm] at h2
    linarith [h2, hm100]
  have ht1 : 1 ≤ ‖(τ:ℂ)‖ := by
    have h : τ.im ≤ ‖(τ:ℂ)‖ := by
      have := Complex.abs_im_le_norm (τ : ℂ)
      rwa [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at this
    linarith
  have he2 : ‖E2Fun τ‖ ≤ 2 := norm_le_two hm2 hm1
  have he4 : ‖E4Fun τ‖ ≤ 2 := norm_le_two hm4 hm1
  have he6 : ‖E6Fun τ‖ ≤ 2 := norm_le_two hm6 hm1
  have hphi0 : ‖phi0 τ‖ ≤ 3 * ‖(τ:ℂ)‖ := by
    have hE : phi0 τ = (τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi:ℂ) := by simp only [phi0]
    rw [hE]
    have h1 : ‖(τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi:ℂ)‖
        ≤ ‖(τ:ℂ) * E2Fun τ‖ + ‖3 * Complex.I / (Real.pi:ℂ)‖ := norm_sub_le _ _
    have h2 : ‖(τ:ℂ) * E2Fun τ‖ ≤ ‖(τ:ℂ)‖ * 2 := norm_mul_le_mul le_rfl he2 (norm_nonneg _)
    have h3 : ‖(3:ℂ) * Complex.I / (Real.pi:ℂ)‖ ≤ 1 := by
      have hpi : ‖(Real.pi:ℂ)‖ = Real.pi := by
        rw [Complex.norm_real]; exact abs_of_nonneg Real.pi_pos.le
      rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, hpi]
      rw [div_le_one (by positivity : (0:ℝ) < Real.pi)]
      exact Real.pi_gt_three.le
    linarith [h1, h2, h3, ht1]
  have hA8 : ‖A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)‖ ≤ 100 * m := by
    rw [A8v]; exact norm_A8_le hm1 hm2 hm4 hm6 hmh
  have hB8 : ‖B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)‖ ≤ 100 * m := by
    rw [B8v]; exact norm_B8_le hm1 hm2 hm4 hm6 hmh
  -- the two pieces of `G8`
  have hb1 : ‖phitVec z 0 * ((τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)
        + (6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z))‖
      ≤ (‖phitVec z 0‖ * 1000) * (‖(τ:ℂ)‖ * m) := by
    have hc : ‖(6:ℂ) * Complex.I / (Real.pi:ℂ)‖ ≤ 6/Real.pi := by
      have hpi : ‖(Real.pi:ℂ)‖ = Real.pi := by
        rw [Complex.norm_real]; exact abs_of_nonneg Real.pi_pos.le
      rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, hpi]
    have hsum : ‖(τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)
          + (6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)‖
        ≤ (‖(τ:ℂ)‖ * (100 * m) + (6/Real.pi) * (100 * m)) := by
      have h1 : ‖(τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)‖ ≤ ‖(τ:ℂ)‖ * (100*m) :=
        norm_mul_le_mul le_rfl hA8 (norm_nonneg _)
      have h2 : ‖(6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)‖
          ≤ (6/Real.pi) * (100*m) := norm_mul_le_mul hc hB8 (by positivity)
      have h := norm_add_le ((τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z))
        ((6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z))
      linarith [h, h1, h2]
    have hkey := norm_mul_le_mul (le_refl (‖phitVec z 0‖)) hsum (norm_nonneg _)
    have hfin : ‖phitVec z 0‖ * (‖(τ:ℂ)‖ * (100 * m) + (6/Real.pi) * (100 * m))
        ≤ (‖phitVec z 0‖ * 1000) * (‖(τ:ℂ)‖ * m) := by
      have hpi6 : (6/Real.pi) * 100 ≤ 900 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < Real.pi)]
        nlinarith [Real.pi_gt_three]
      have h9 : (6/Real.pi) * (100 * m) ≤ 900 * (‖(τ:ℂ)‖ * m) := by nlinarith [hpi6, hm0, ht1]
      have h10 : ‖(τ:ℂ)‖ * (100 * m) + 900 * (‖(τ:ℂ)‖ * m) ≤ 1000 * (‖(τ:ℂ)‖ * m) := by
        nlinarith [hm0, ht1, norm_nonneg (τ:ℂ)]
      nlinarith [h9, h10, hm0, ht1, norm_nonneg (phitVec z 0), norm_nonneg (‖(τ:ℂ)‖ * m)]
    linarith [hkey, hfin]
  have hb2 : ‖(phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z - 2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z)
        * (DeltaFun z * kpJ τ z)⁻¹‖
      ≤ ((‖phitVec z 2‖ * (2 * ‖E8Fun z‖) + 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖)) * (2/‖DeltaFun z‖))
        * (‖(τ:ℂ)‖ * m) := by
    have h1 : ‖phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z‖
        ≤ ‖phitVec z 2‖ * (2 * ‖E8Fun z‖) * ‖(τ:ℂ)‖ := by
      calc ‖phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z‖
          = ‖phitVec z 2‖ * ‖(τ:ℂ)‖ * ‖E6Fun τ‖ * ‖E8Fun z‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ ‖phitVec z 2‖ * ‖(τ:ℂ)‖ * 2 * ‖E8Fun z‖ := by gcongr
        _ = ‖phitVec z 2‖ * (2 * ‖E8Fun z‖) * ‖(τ:ℂ)‖ := by ring
    have h2 : ‖2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z‖
        ≤ 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖) * ‖(τ:ℂ)‖ := by
      calc ‖2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z‖
          = ‖(2:ℂ)‖ * ‖phi0 τ‖ * ‖phitVec z 1‖ * ‖E4Fun τ‖ * ‖E10Fun z‖ := by
            rw [norm_mul, norm_mul, norm_mul, norm_mul]
        _ = 2 * ‖phi0 τ‖ * ‖phitVec z 1‖ * ‖E4Fun τ‖ * ‖E10Fun z‖ := by
            rw [Complex.norm_ofNat]
        _ ≤ 2 * (3 * ‖(τ:ℂ)‖) * ‖phitVec z 1‖ * 2 * ‖E10Fun z‖ := by gcongr
        _ = 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖) * ‖(τ:ℂ)‖ := by ring
    have hsub : ‖phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z - 2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z‖
        ≤ ((‖phitVec z 2‖ * (2 * ‖E8Fun z‖) + 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖)) * ‖(τ:ℂ)‖) := by
      have h := norm_sub_le (phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z)
        (2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z)
      have h1' : ‖phitVec z 2‖ * (2 * ‖E8Fun z‖) * ‖(τ:ℂ)‖
          = (‖phitVec z 2‖ * (2 * ‖E8Fun z‖)) * ‖(τ:ℂ)‖ := by ring
      linarith [h, h1, h2, ht1]
    have h := norm_mul_le_mul hsub hJinv (by positivity)
    have hfin : ((‖phitVec z 2‖ * (2 * ‖E8Fun z‖) + 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖)) * ‖(τ:ℂ)‖)
          * (2 * m / ‖DeltaFun z‖)
        ≤ ((‖phitVec z 2‖ * (2 * ‖E8Fun z‖) + 6 * ‖phitVec z 1‖ * (2 * ‖E10Fun z‖)) * (2/‖DeltaFun z‖))
          * (‖(τ:ℂ)‖ * m) := by
      have hzpos : 0 < ‖DeltaFun z‖ := norm_pos_iff.mpr (delta_ne_zero z)
      have hD : 2 * m / ‖DeltaFun z‖ = (2/‖DeltaFun z‖) * m := by ring
      rw [hD]
      nlinarith [hzpos, hm0, norm_nonneg (τ:ℂ), norm_nonneg (phitVec z 2),
        norm_nonneg (phitVec z 1), norm_nonneg (E8Fun z), norm_nonneg (E10Fun z)]
    linarith [h, hfin]
  -- combine
  have hG8 : ‖G8 τ z‖ ≤ Cz * (‖(τ:ℂ)‖ * m) := by
    rw [hCz]
    rw [G8]
    have h := norm_add_le (phitVec z 0 * ((τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)
          + (6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)))
      ((phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z - 2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z)
        * (DeltaFun z * kpJ τ z)⁻¹)
    nlinarith [h, hb1, hb2, hm0, norm_nonneg (τ:ℂ), norm_nonneg (phitVec z 0),
      norm_nonneg (phitVec z 1), norm_nonneg (phitVec z 2), norm_nonneg (E8Fun z),
      norm_nonneg (E10Fun z), norm_nonneg (‖DeltaFun z‖)]
  have hpi2 : ‖(Real.pi : ℂ)^2/(36*Complex.I)‖ = Real.pi^2/36 := by
    have h1 : ‖((Real.pi:ℂ)^2)‖ = Real.pi^2 := by
      rw [norm_pow]
      have h : ‖(Real.pi:ℂ)‖ = Real.pi := by
        rw [Complex.norm_real]; exact abs_of_nonneg Real.pi_pos.le
      rw [h]
    have h2 : ‖(36:ℂ) * Complex.I‖ = 36 := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    rw [norm_div, h1, h2]
  have hK : KPlus 8 τ z = (Real.pi : ℂ)^2/(36*Complex.I) * G8 τ z := KPlus_eight_eq τ z hJnz
  have hCz0 : 0 ≤ Cz := by rw [hCz]; positivity
  calc ‖KPlus 8 τ z‖ = ‖(Real.pi : ℂ)^2/(36*Complex.I) * G8 τ z‖ := by rw [hK]
    _ = (Real.pi^2/36) * ‖G8 τ z‖ := by rw [norm_mul, hpi2]
    _ ≤ (Real.pi^2/36) * (Cz * (‖(τ:ℂ)‖ * m)) := mul_le_mul_of_nonneg_left hG8 (by positivity)
    _ ≤ ((Real.pi^2/36) * Cz * K1 + 1) * ‖(τ:ℂ)‖ * eps τ := by
        rw [hm]
        nlinarith [norm_nonneg (τ:ℂ), eps_nonneg τ, Real.pi_pos, hCz0, hK10]
