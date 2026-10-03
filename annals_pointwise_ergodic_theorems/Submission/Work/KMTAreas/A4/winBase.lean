import Mathlib
import Submission.Work.KMTAreas.A4.winZFourier

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Elementary properties of the unmodulated window `win M 0` -/

/-- The unmodulated window is the rescaled smoothing profile: `win M 0 m = M⁻¹ ψ(m/M)`. -/
theorem win_zero_apply (M : ℝ) (m : ℤ) :
    win M (0 : FreqCircle) m = ((M : ℂ))⁻¹ * (lipSchPsi ((m : ℝ) / M) : ℂ) := by
  rw [win]
  simp

/-- The modulated window factors through the unmodulated one. -/
theorem win_eq_win_zero_mul_fourier (M : ℝ) (γ : FreqCircle) (m : ℤ) :
    win M γ m = win M (0 : FreqCircle) m * (fourier m γ : ℂ) := by
  have h0 : (fourier m (0 : FreqCircle) : ℂ) = 1 := by simp
  rw [win, win, h0]
  ring

/-- Decay of the unmodulated window. -/
theorem win_zero_decay (M : ℝ) (hM : 0 < M) (m : ℤ) :
    ‖win M (0 : FreqCircle) m‖ ≤ ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) / M)
      * jbDecay 12 ((m : ℝ) / M) := by
  have hψ := schwartz_decay lipSchPsi ((m : ℝ) / M)
  have hnorm : ‖((M : ℂ))⁻¹‖ = M⁻¹ := by
    have h1 : ‖(M : ℂ)‖ = |M| := RCLike.norm_ofReal M
    rw [norm_inv, h1, abs_of_pos hM]
  rw [win_zero_apply, norm_mul, hnorm]
  have hMinv : (0:ℝ) ≤ M⁻¹ := le_of_lt (inv_pos.mpr hM)
  calc M⁻¹ * ‖(lipSchPsi ((m : ℝ) / M) : ℂ)‖
      ≤ M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) * jbDecay 12 ((m : ℝ) / M)) :=
        mul_le_mul_of_nonneg_left hψ hMinv
    _ = (2 ^ 12 * (schwartzSeminormSum lipSchPsi + 1) / M) * jbDecay 12 ((m : ℝ) / M) := by
        ring

/-! ## The `jbDecay` comparison on a unit segment -/

/-- On the segment `[(m-1)/M, m/M]` the bracket `jb` is comparable with its value at the right
endpoint: `jb (m/M) ≤ 2 jb t`. -/
theorem jb_le_two_jb_of_mem_segment {M : ℝ} (hM : 1 ≤ M) (m : ℤ) {t : ℝ}
    (h1 : ((m - 1 : ℤ) : ℝ) / M ≤ t) (h2 : t ≤ (m : ℝ) / M) : jb ((m : ℝ) / M) ≤ 2 * jb t := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  set y : ℝ := (m : ℝ) / M with hy
  set x : ℝ := ((m - 1 : ℤ) : ℝ) / M with hx
  have hcast : ((m - 1 : ℤ) : ℝ) = (m : ℝ) - 1 := by push_cast; ring
  have hxy : y = x + 1 / M := by
    rw [hx, hy, hcast]
    rw [← add_div]
    congr 1
    ring
  have h1le : (1 : ℝ) / M ≤ 1 := by rw [div_le_iff₀ hMpos]; linarith
  have hjb1 : jb (1 / M) ≤ jb 1 := by
    rw [jb_le_jb_iff, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / M), abs_one]
    exact h1le
  have hjb1' : jb (1 / M) ≤ Real.sqrt 2 := by
    refine hjb1.trans (le_of_eq ?_); rw [jb]; norm_num
  have hybound : jb y ≤ 2 * jb x := by
    rw [hxy]
    have hsub := jb_add_le_sqrt_two_mul x (1 / M)
    have hsqrt : Real.sqrt 2 * jb (1 / M) ≤ 2 := by
      have h2 : Real.sqrt 2 * jb (1 / M) ≤ Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hjb1' (Real.sqrt_nonneg 2)
      rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h2
    calc jb (x + 1 / M) ≤ Real.sqrt 2 * jb x * jb (1 / M) := hsub
      _ = (Real.sqrt 2 * jb (1 / M)) * jb x := by ring
      _ ≤ 2 * jb x := mul_le_mul_of_nonneg_right hsqrt (le_of_lt (jb_pos x))
  have hbt : 0 ≤ jb t := (jb_pos t).le
  have hstrad : x < 0 → ¬ (0 < y) := by
    intro hx0 hy0
    have h1' : ((m - 1 : ℤ) : ℝ) < 0 := by
      have : x * M < 0 := mul_neg_of_neg_of_pos hx0 hMpos
      rwa [hx, div_mul_cancel₀ _ (ne_of_gt hMpos)] at this
    have h2' : (0 : ℝ) < (m : ℝ) := by
      have : 0 < y * M := mul_pos hy0 hMpos
      rwa [hy, div_mul_cancel₀ _ (ne_of_gt hMpos)] at this
    have hmi1 : m - 1 < 0 := by exact_mod_cast h1'
    have hmi2 : (0 : ℤ) < m := by exact_mod_cast h2'
    omega
  by_cases hx0 : 0 ≤ x
  · have hxt : x ≤ t := h1
    have hmono : jb x ≤ jb t := by
      rw [jb_le_jb_iff, abs_of_nonneg hx0, abs_of_nonneg (le_trans hx0 hxt)]
      exact hxt
    linarith
  · have hx0' : x < 0 := not_le.mp hx0
    by_cases hy0 : y ≤ 0
    · have hmono : jb y ≤ jb t := by
        rw [jb_le_jb_iff, abs_of_nonpos hy0, abs_of_nonpos (le_trans h2 hy0)]
        linarith
      linarith
    · exact absurd (not_le.mp hy0) (hstrad hx0')

/-- On the segment `[(m-1)/M, m/M]` the decay `jbDecay 12` is bounded by its value at the right
endpoint, up to `2 ^ 12`. -/
theorem jbDecay_segment_le {M : ℝ} (hM : 1 ≤ M) (m : ℤ) {t : ℝ}
    (h1 : ((m - 1 : ℤ) : ℝ) / M ≤ t) (h2 : t ≤ (m : ℝ) / M) :
    jbDecay 12 t ≤ 2 ^ 12 * jbDecay 12 ((m : ℝ) / M) := by
  have hjb := jb_le_two_jb_of_mem_segment hM m h1 h2
  have hy : 0 < jb t := jb_pos t
  have hy2 : 0 < jb ((m : ℝ) / M) := jb_pos _
  have hkey : (jb t)⁻¹ * jb ((m : ℝ) / M) ≤ 2 := by
    rw [inv_mul_le_iff₀ hy]; linarith
  have hpow : (jb t)⁻¹ ≤ 2 * (jb ((m : ℝ) / M))⁻¹ := by
    calc (jb t)⁻¹ = ((jb t)⁻¹ * jb ((m : ℝ) / M)) * (jb ((m : ℝ) / M))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hy2), mul_one]
      _ ≤ 2 * (jb ((m : ℝ) / M))⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt (inv_pos.mpr hy2))
  have h12 : (0:ℝ) ≤ (jb t)⁻¹ := le_of_lt (inv_pos.mpr hy)
  calc jbDecay 12 t = ((jb t)⁻¹) ^ 12 := by rw [jbDecay]
    _ ≤ (2 * (jb ((m : ℝ) / M))⁻¹) ^ 12 := pow_le_pow_left₀ h12 hpow 12
    _ = 2 ^ 12 * jbDecay 12 ((m : ℝ) / M) := by rw [jbDecay, mul_pow]

/-! ## (alpha): decay of the adjacent difference of the unmodulated window -/

/-- **Decay of the adjacent differences of the window.** -/
theorem win_zero_diff_le {M : ℝ} (hM : 1 ≤ M) (m : ℤ) :
    ‖win M (0 : FreqCircle) m - win M (0 : FreqCircle) (m - 1)‖
      ≤ ((2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
          * 2 ^ 12 / M ^ 2) * jbDecay 12 ((m : ℝ) / M) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  set x : ℝ := ((m - 1 : ℤ) : ℝ) / M with hx
  set y : ℝ := (m : ℝ) / M with hy
  have hcast : ((m - 1 : ℤ) : ℝ) = (m : ℝ) - 1 := by push_cast; ring
  have hS : 0 ≤ schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) :=
    schwartzSeminormSum_nonneg _
  have hMinv : (0:ℝ) ≤ M⁻¹ := le_of_lt (inv_pos.mpr hMpos)
  have hx_le_y : x ≤ y := by
    rw [hx, hy, hcast]
    exact div_le_div_of_nonneg_right (by linarith) hMpos.le
  have hmvt : ‖(lipSchPsi y : ℂ) - (lipSchPsi x : ℂ)‖ ≤
      ((2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
        * 2 ^ 12 * jbDecay 12 y) * (y - x) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := (lipSchPsi : ℝ → ℂ)) (f' := fun t : ℝ => deriv (lipSchPsi : ℝ → ℂ) t)
      (a := x) (b := y)
      (C := (2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
        * 2 ^ 12 * jbDecay 12 y) ?_ ?_ y ⟨hx_le_y, le_refl y⟩
    · intro t ht
      exact (SchwartzMap.hasDerivAt lipSchPsi t).hasDerivWithinAt
    · intro t ht
      have ht1 : x ≤ t := ht.1
      have ht2 : t ≤ y := le_of_lt ht.2
      have hψ' : ‖deriv (lipSchPsi : ℝ → ℂ) t‖
          ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
            * jbDecay 12 t := by
        have h := schwartz_decay (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) t
        rw [SchwartzMap.derivCLM_apply] at h
        exact h
      have hseg : jbDecay 12 t ≤ 2 ^ 12 * jbDecay 12 y := by
        rw [hy]
        exact jbDecay_segment_le hM m (by rw [hx] at ht1; exact ht1) (by rw [hy] at ht2; exact ht2)
      calc ‖deriv (lipSchPsi : ℝ → ℂ) t‖
          ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
            * jbDecay 12 t := hψ'
        _ ≤ (2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
            * (2 ^ 12 * jbDecay 12 y) :=
              mul_le_mul_of_nonneg_left hseg (by positivity : (0:ℝ) ≤ 2 ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1))
        _ = (2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
            * 2 ^ 12 * jbDecay 12 y := by ring
  have hdiff : win M (0 : FreqCircle) m - win M (0 : FreqCircle) (m - 1)
      = ((M : ℂ))⁻¹ * ((lipSchPsi y : ℂ) - (lipSchPsi x : ℂ)) := by
    rw [win_zero_apply, win_zero_apply, hy, hx]
    ring
  have hnorm : ‖((M : ℂ))⁻¹‖ = M⁻¹ := by
    have h1 : ‖(M : ℂ)‖ = |M| := RCLike.norm_ofReal M
    rw [norm_inv, h1, abs_of_pos hMpos]
  have hyx : y - x = 1 / M := by
    rw [hx, hy, hcast, sub_div]
    congr 1
    ring
  have hmvt' : ‖(lipSchPsi y : ℂ) - (lipSchPsi x : ℂ)‖ ≤
      ((2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
        * 2 ^ 12 * jbDecay 12 y) * (1 / M) := by
    have h := hmvt
    rw [hyx] at h
    exact h
  rw [hdiff, norm_mul, hnorm]
  calc M⁻¹ * ‖(lipSchPsi y : ℂ) - (lipSchPsi x : ℂ)‖
      ≤ M⁻¹ * (((2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
        * 2 ^ 12 * jbDecay 12 y) * (1 / M)) :=
        mul_le_mul_of_nonneg_left hmvt' hMinv
    _ = ((2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1)
          * 2 ^ 12 / M ^ 2) * jbDecay 12 y := by
        field_simp

/-- **(alpha)** Decay of the adjacent difference of the window `win M 0`, uniformly in `M ≥ 1`
and the shift `s`. -/
theorem winDelta_decay : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 1 ≤ M → ∀ (s n : ℤ),
    ‖win M (0 : FreqCircle) (n - s) - win M (0 : FreqCircle) (n - 1 - s)‖
      ≤ (C / M ^ 2) * jbDecay 12 (((n - s : ℤ) : ℝ) / M) := by
  have hS : 0 ≤ schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) :=
    schwartzSeminormSum_nonneg _
  refine ⟨(2 : ℝ) ^ 12 * (schwartzSeminormSum (SchwartzMap.derivCLM ℂ ℂ lipSchPsi) + 1) * 2 ^ 12,
    by positivity, ?_⟩
  intro M hM s n
  have hsub : n - 1 - s = (n - s) - 1 := by ring
  rw [hsub]
  exact win_zero_diff_le (M := M) hM (n - s)


/-! ## The `λ`-periodization of the smoothing profile (Poisson summation) -/

/-- **The `λ`-periodization of `ψ = lipSchPsi` is constant** for `0 < λ ≤ 1`: it equals `1/λ`. -/
theorem lipSchPsi_periodization (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (y : ℝ) :
    (∑' j : ℤ, (lipSchPsi (y + (j : ℝ) * lam) : ℂ)) = ((lam : ℂ))⁻¹ := by
  have hS : 0 ≤ schwartzSeminormSum lipSchPsi := schwartzSeminormSum_nonneg _
  set C : ℝ := (2:ℝ)^12 * (schwartzSeminormSum lipSchPsi + 1) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hdec : ∀ t : ℝ, ‖(lipSchPsi t : ℂ)‖ ≤ C * jbDecay 12 t := fun t =>
    schwartz_decay lipSchPsi t
  have hcont : Continuous fun u : ℝ => (lipSchPsi (lam * u) : ℂ) := by fun_prop
  -- decay of the dilated profile
  have hf_bigO : (fun u : ℝ => (lipSchPsi (lam * u) : ℂ))
      =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    refine isBigO_cocompact_of_le_inv_pow (D := C * lam⁻¹ ^ 12) (by positivity) ?_
    intro t ht
    have hnorm : ‖(lipSchPsi (lam * t) : ℂ)‖ ≤ C * jbDecay 12 (lam * t) := hdec _
    have hjb : jbDecay 12 (lam * t) ≤ ((lam * |t|)⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      rw [inv_le_inv₀ (jb_pos _) (by positivity)]
      calc lam * |t| = |lam * t| := by rw [abs_mul, abs_of_pos h0]
        _ ≤ jb (lam * t) := abs_le_jb _
    calc ‖(lipSchPsi (lam * t) : ℂ)‖ ≤ C * jbDecay 12 (lam * t) := hnorm
      _ ≤ C * ((lam * |t|)⁻¹) ^ 12 := mul_le_mul_of_nonneg_left hjb hCpos.le
      _ = (C * lam⁻¹ ^ 12) * (|t|⁻¹) ^ 12 := by rw [mul_inv, mul_pow]; ring
  -- the Fourier transform of the dilated profile
  have hcm : ∀ (c : ℂ) (g : ℝ → ℂ) (ξ : ℝ), (𝓕 fun u => c * g u) ξ = c * (𝓕 g) ξ := by
    intro c g ξ
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [circle_smul_eq_mul]
    ring
  have hFT : ∀ ξ : ℝ, (𝓕 fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) ξ
      = (lam : ℂ)⁻¹ * (lipSchChi (ξ / lam) : ℂ) := by
    intro ξ
    have hdil := realFourier_dilation (lipSchPsi : ℝ → ℂ) h0 ξ
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
    have hstep : (𝓕 fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) ξ
        = (lam : ℂ)⁻¹ * (𝓕 fun u : ℝ => (lam : ℂ) * (lipSchPsi (lam * u) : ℂ)) ξ := by
      rw [hcm (lam : ℂ) (fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) ξ]
      rw [← mul_assoc, inv_mul_cancel₀ hl, one_mul]
    have hdil' : (𝓕 fun u : ℝ => (lam : ℂ) * (lipSchPsi (lam * u) : ℂ)) ξ
        = (𝓕 (lipSchPsi : ℝ → ℂ)) (ξ / lam) := hdil
    rw [hstep, hdil', ← SchwartzMap.fourier_coe, lipSchPsi_fourier]
  -- decay of the Fourier transform
  have hFf_bigO : (𝓕 fun u : ℝ => (lipSchPsi (lam * u) : ℂ))
      =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    refine isBigO_cocompact_of_le_inv_pow (D := lam⁻¹) (by positivity) ?_
    intro t ht
    rw [hFT t]
    have hz : (lipSchChi (t / lam) : ℂ) = 0 := by
      apply lipSchChi_eq_zero
      rw [abs_div, abs_of_pos h0, le_div_iff₀ h0]
      linarith [h1, ht]
    rw [hz, mul_zero, norm_zero]
    positivity
  -- Poisson summation at the point `y/λ`
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay
    (f := fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) hcont (b := 12) (by norm_num)
    hf_bigO hFf_bigO (y / lam)
  have hL : (∑' n : ℤ, (fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) (y / lam + n))
      = ∑' n : ℤ, (lipSchPsi (y + (n : ℝ) * lam) : ℂ) := by
    refine tsum_congr fun n => ?_
    congr 1
    field_simp
  rw [hL] at hpois
  have hR : (∑' n : ℤ, (𝓕 fun u : ℝ => (lipSchPsi (lam * u) : ℂ)) n
      * (fourier n (((y / lam) : ℝ) : UnitAddCircle) : ℂ)) = (lam : ℂ)⁻¹ := by
    rw [tsum_eq_single 0]
    · simp only [Int.cast_zero]
      rw [hFT 0, zero_div, lipSchChi_zero, mul_one]
      simp
    · intro n hn
      have hz : (lipSchChi ((n:ℝ) / lam) : ℂ) = 0 := by
        apply lipSchChi_eq_zero
        rw [abs_div, abs_of_pos h0, le_div_iff₀ h0]
        have h1n : (1:ℝ) ≤ |((n:ℤ):ℝ)| := by
          have h0 : (1:ℤ) ≤ (n.natAbs : ℤ) := by
            have := Int.natAbs_pos.mpr hn
            omega
          have h2 : ((n.natAbs : ℤ) : ℝ) = |((n:ℤ):ℝ)| := by
            rw [← Int.cast_abs, Int.natCast_natAbs]
          rw [← h2]
          exact_mod_cast h0
        linarith [h1]
      rw [hFT n, hz, mul_zero, zero_mul]
  rw [hR] at hpois
  exact hpois

/-! ## Lattice-sum bounds for `jbDecay` (Riemann comparison `riemann_shift`) -/

/-- The `ℕ`-half-lattice of `jbDecay N` is summable (for `12 ≤ N`). -/
theorem jbDecay_nat_summable {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam) :
    Summable fun k : ℕ => jbDecay N ((k : ℝ) * lam) := by
  have h12 : Summable fun k : ℕ => jbDecay 12 ((k : ℝ) * lam) := by
    have h := summable_eps_jbDecay_shift' (ε := lam) h0 (le_refl (0:ℝ))
    refine (h.mul_left lam⁻¹).congr (fun k => ?_)
    rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
    congr 1
    ring
  exact Summable.of_nonneg_of_le (fun k => jbDecay_nonneg N _) (fun k => jbDecay_anti hN _) h12

/-- Riemann-sum bound on the `ℕ`-half-lattice. -/
theorem jbDecay_nat_lattice_le {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    (∑' k : ℕ, jbDecay N ((k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ := by
  have h12 : (∑' k : ℕ, jbDecay 12 ((k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ := by
    have h := riemann_shift 11 (by norm_num) (ε := lam) (t := 0) h0 h1 (le_refl (0:ℝ))
    have h0' : jbDecay 11 (0:ℝ) = 1 := by
      rw [jbDecay]
      have hjb0 : jb (0:ℝ) = 1 := by rw [jb]; norm_num
      rw [hjb0, inv_one, one_pow]
    rw [h0', mul_one] at h
    have hX : (∑' k : ℕ, jbDecay 12 (0 + lam * (k:ℝ)))
        = ∑' k : ℕ, jbDecay 12 ((k:ℝ) * lam) := by
      refine tsum_congr fun k => ?_
      congr 1
      ring
    rw [tsum_mul_left] at h
    rw [hX] at h
    rw [show (2:ℝ)^60 * lam⁻¹ = (2:ℝ)^60 / lam from (div_eq_mul_inv _ _).symm, le_div_iff₀ h0,
      mul_comm]
    exact h
  refine (Summable.tsum_le_tsum (f := fun k : ℕ => jbDecay N ((k:ℝ)*lam))
    (g := fun k : ℕ => jbDecay 12 ((k:ℝ)*lam)) (fun k => jbDecay_anti hN _)
    (jbDecay_nat_summable hN h0) (jbDecay_nat_summable (le_refl 12) h0)).trans h12

/-- Summability of the shifted `ℕ`-half-lattice. -/
theorem jbDecay_nat_shift_summable {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam) {t : ℝ}
    (ht : 0 ≤ t) : Summable fun k : ℕ => jbDecay N (t + (k : ℝ) * lam) := by
  have h12 : Summable fun k : ℕ => jbDecay 12 (t + (k : ℝ) * lam) := by
    have h := summable_eps_jbDecay_shift' (ε := lam) h0 ht
    refine (h.mul_left lam⁻¹).congr (fun k => ?_)
    rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
    congr 1
    ring
  exact Summable.of_nonneg_of_le (fun k => jbDecay_nonneg N _) (fun k => jbDecay_anti hN _) h12

/-- Riemann-sum bound on the shifted `ℕ`-half-lattice. -/
theorem jbDecay_nat_shift_lattice_le {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∑' k : ℕ, jbDecay N (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ := by
  have h12 : (∑' k : ℕ, jbDecay 12 (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ := by
    have h := riemann_shift 11 (by norm_num) (ε := lam) (t := t) h0 h1 ht
    have hX : (∑' k : ℕ, jbDecay 12 (t + lam * (k:ℝ)))
        = ∑' k : ℕ, jbDecay 12 (t + (k:ℝ) * lam) := by
      refine tsum_congr fun k => ?_
      congr 1
      ring
    rw [tsum_mul_left] at h
    rw [hX] at h
    have hb : (2:ℝ)^60 * jbDecay 11 t ≤ (2:ℝ)^60 := by
      have h := mul_le_mul_of_nonneg_left (jbDecay_le_one 11 t) (by positivity : (0:ℝ) ≤ (2:ℝ)^60)
      linarith [h]
    rw [show (2:ℝ)^60 * lam⁻¹ = (2:ℝ)^60 / lam from (div_eq_mul_inv _ _).symm, le_div_iff₀ h0,
      mul_comm]
    exact h.trans hb
  refine (Summable.tsum_le_tsum (f := fun k : ℕ => jbDecay N (t + (k:ℝ)*lam))
    (g := fun k : ℕ => jbDecay 12 (t + (k:ℝ)*lam)) (fun k => jbDecay_anti hN _)
    (jbDecay_nat_shift_summable hN h0 ht) (jbDecay_nat_shift_summable (by norm_num : 12 ≤ 12) h0 ht)).trans h12

/-- Summability of the `ℤ`-lattice of `jbDecay N`. -/
theorem jbDecay_int_summable {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam) :
    Summable fun r : ℤ => jbDecay N ((r : ℝ) * lam) := by
  have hpos : Summable fun k : ℕ => jbDecay N ((k : ℝ) * lam) := jbDecay_nat_summable hN h0
  have hneg : Summable fun k : ℕ => jbDecay N (((-(k + 1) : ℤ) : ℝ) * lam) := by
    have hshift : Summable fun k : ℕ => jbDecay N (lam + (k:ℝ) * lam) :=
      jbDecay_nat_shift_summable hN h0 h0.le
    refine hshift.congr (fun k => ?_)
    rw [show (((-(k+1) : ℤ) : ℝ) * lam) = -(lam + (k:ℝ)*lam) by push_cast; ring, jbDecay_neg]
  exact Summable.of_nat_of_neg_add_one hpos hneg

/-- Riemann-sum bound on the full `ℤ`-lattice. -/
theorem jbDecay_int_lattice_le {N : ℕ} (hN : 12 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    (∑' r : ℤ, jbDecay N ((r : ℝ) * lam)) ≤ 2 * ((2 : ℝ) ^ 60 * lam⁻¹) := by
  have hpos : Summable fun k : ℕ => jbDecay N ((k : ℝ) * lam) := jbDecay_nat_summable hN h0
  have hneg : Summable fun k : ℕ => jbDecay N (((-(k + 1) : ℤ) : ℝ) * lam) := by
    have hshift : Summable fun k : ℕ => jbDecay N (lam + (k:ℝ) * lam) :=
      jbDecay_nat_shift_summable hN h0 h0.le
    refine hshift.congr (fun k => ?_)
    rw [show (((-(k+1) : ℤ) : ℝ) * lam) = -(lam + (k:ℝ)*lam) by push_cast; ring, jbDecay_neg]
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  have h1' : (∑' k : ℕ, jbDecay N (((-(k + 1) : ℤ) : ℝ) * lam))
      = ∑' k : ℕ, jbDecay N (lam + (k:ℝ) * lam) := by
    refine tsum_congr fun k => ?_
    rw [show (((-(k+1) : ℤ) : ℝ) * lam) = -(lam + (k:ℝ)*lam) by push_cast; ring, jbDecay_neg]
  rw [h1']
  have hb1 := jbDecay_nat_lattice_le hN h0 h1
  have hb2 := jbDecay_nat_shift_lattice_le hN h0 h1 h0.le
  calc (∑' k : ℕ, jbDecay N ((k:ℝ)*lam)) + (∑' k : ℕ, jbDecay N (lam + (k:ℝ)*lam))
      ≤ (2:ℝ)^60 * lam⁻¹ + (2:ℝ)^60 * lam⁻¹ := add_le_add hb1 hb2
    _ = 2 * ((2:ℝ)^60 * lam⁻¹) := by ring

/-- Summability of the `ℤ`-lattice with the parameter written as a division. -/
theorem jbDecay_int_summable_div {N : ℕ} (hN : 12 ≤ N) {M : ℝ} (hM : 0 < M) :
    Summable fun r : ℤ => jbDecay N ((r : ℝ) / M) := by
  have h := jbDecay_int_summable (lam := M⁻¹) hN (inv_pos.mpr hM)
  refine h.congr (fun r => ?_)
  rfl

/-- Riemann-sum bound on the `ℤ`-lattice with the parameter written as a division. -/
theorem jbDecay_int_lattice_le_div {N : ℕ} (hN : 12 ≤ N) {M : ℝ} (hM : 1 ≤ M) :
    (∑' r : ℤ, jbDecay N ((r : ℝ) / M)) ≤ 2 * ((2 : ℝ) ^ 60 * M) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h := jbDecay_int_lattice_le (lam := M⁻¹) hN (inv_pos.mpr hMpos) (by
    rw [inv_le_one₀ hMpos]; exact hM)
  refine h.trans (le_of_eq ?_)
  rw [inv_eq_one_div, one_div, inv_inv]

/-- Riemann-sum bound on the shifted `ℕ`-half-lattice with `⟨t⟩^{-12}` on the right. -/
theorem jbDecay_nat_shift_lattice_le13 {N : ℕ} (hN : 13 ≤ N) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∑' k : ℕ, jbDecay N (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ * jbDecay 12 t := by
  have h13 : (∑' k : ℕ, jbDecay 13 (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ * jbDecay 12 t := by
    have h := riemann_shift 12 (by norm_num) (ε := lam) (t := t) h0 h1 ht
    rw [show (12 + 1 : ℕ) = 13 from rfl] at h
    have hX : (∑' k : ℕ, jbDecay 13 (t + lam * (k:ℝ)))
        = ∑' k : ℕ, jbDecay 13 (t + (k:ℝ) * lam) := by
      refine tsum_congr fun k => ?_
      congr 1
      ring
    rw [tsum_mul_left] at h
    rw [hX] at h
    rw [show (2:ℝ)^60 * lam⁻¹ * jbDecay 12 t = ((2:ℝ)^60 * jbDecay 12 t) / lam from by
      rw [div_eq_mul_inv]; ring, le_div_iff₀ h0, mul_comm]
    exact h
  refine (Summable.tsum_le_tsum (f := fun k : ℕ => jbDecay N (t + (k:ℝ)*lam))
    (g := fun k : ℕ => jbDecay 13 (t + (k:ℝ)*lam)) (fun k => jbDecay_anti hN _)
    (jbDecay_nat_shift_summable (by omega : 12 ≤ N) h0 ht)
    (jbDecay_nat_shift_summable (by norm_num : 12 ≤ 13) h0 ht)).trans h13

end Work.KMTAreas.A4
