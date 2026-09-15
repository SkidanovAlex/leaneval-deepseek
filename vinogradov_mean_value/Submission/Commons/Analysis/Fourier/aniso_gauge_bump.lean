import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Convolution.integral_aniso_tent_scaling

open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace

namespace Commons.Analysis.Fourier

set_option maxHeartbeats 2000000

noncomputable section

/-- There is a Schwartz function on `ℝ` whose Fourier transform is identically `1` on `[-1,1]`.
It is obtained as the inverse Fourier transform of a smooth bump equal to `1` on `[-2,2]`. -/
lemma exists_schwartzMap_fourier_eq_one_Icc :
    ∃ g : SchwartzMap ℝ ℂ, ∀ t : ℝ, |t| ≤ 1 → 𝓕 (g : ℝ → ℂ) t = 1 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
  let φ : ℝ → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hφ_diff : ContDiff ℝ ∞ φ := by
    have hb : ContDiff ℝ ∞ (bump : ℝ → ℝ) := bump.contDiff
    exact (Complex.ofRealCLM.contDiff (n := ∞)).comp hb
  have hφ_cs : HasCompactSupport φ := by
    have hb : HasCompactSupport (bump : ℝ → ℝ) := bump.hasCompactSupport
    exact hb.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let φS : SchwartzMap ℝ ℂ := hφ_cs.toSchwartzMap hφ_diff
  refine ⟨𝓕⁻ φS, ?_⟩
  intro t ht
  have hcoe : (φS : ℝ → ℂ) t = φ t := HasCompactSupport.toSchwartzMap_toFun hφ_cs hφ_diff t
  have h1 : 𝓕 ((𝓕⁻ φS : SchwartzMap ℝ ℂ) : ℝ → ℂ) t = (φS : ℝ → ℂ) t := by
    rw [← SchwartzMap.fourier_coe (𝓕⁻ φS), FourierTransform.fourier_fourierInv_eq]
  rw [h1, hcoe]
  have hmem : t ∈ Metric.closedBall (0 : ℝ) bump.rIn := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    have : bump.rIn = 2 := rfl
    rw [this]; linarith
  have hb1 : (bump : ℝ → ℝ) t = 1 := bump.one_of_mem_closedBall hmem
  simp [φ, hb1]

/-- Polynomial decay of a complex-valued Schwartz function on `ℝ`. -/
lemma schwartzMap_real_decay (g : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖g t‖ ≤ B * (1 + |t|) ^ (-(N : ℝ)) := by
  refine ⟨max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
      (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) g)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have ha : 0 < (1 + |x| : ℝ) := by positivity
  have hbound : (1 + |x|) ^ N * ‖g x‖ ≤
      2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
        (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) g) := by
    simpa using SchwartzMap.one_add_le_sup_seminorm_apply
      (m := ((N, 0) : ℕ × ℕ)) (k := N) (n := 0) le_rfl le_rfl g x
  have hle : (1 + |x|) ^ N * ‖g x‖ ≤
      max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
        (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) g)) 1 :=
    hbound.trans (le_max_left _ _)
  have haN : (1 + |x|) ^ (-(N : ℝ)) * (1 + |x|) ^ N = 1 := by
    rw [← Real.rpow_natCast (1 + |x|) N, ← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero]
  calc ‖g x‖
      = (1 + |x|) ^ (-(N : ℝ)) * ((1 + |x|) ^ N * ‖g x‖) := by
        rw [← mul_assoc, haN, one_mul]
    _ ≤ (1 + |x|) ^ (-(N : ℝ)) *
        max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
          (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) g)) 1 :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ha.le _)
    _ = max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
          (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) g)) 1 *
        (1 + |x|) ^ (-(N : ℝ)) := by rw [mul_comm]

/-- The Fourier transform on `ℝ`, written as an integral against `exp(-2π i u s)`. -/
lemma fourier_real_apply (g : SchwartzMap ℝ ℂ) (s : ℝ) :
    𝓕 (g : ℝ → ℂ) s
      = ∫ u : ℝ, g u * Complex.exp (-(2 * Real.pi * Complex.I) * ((u * s : ℝ) : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [Real.fourierChar_apply, Real.inner_apply]
  congr 1
  push_cast
  ring

/-- The rescaling rule for the one-dimensional Fourier transform. -/
lemma fourier_scaling_real (g : SchwartzMap ℝ ℂ) (a s : ℝ) (ha : 0 < a) :
    (∫ t : ℝ, g (a * t) * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * t : ℝ) : ℂ)))
      = ((a⁻¹ : ℝ) : ℂ) * 𝓕 (g : ℝ → ℂ) (s / a) := by
  have hfun : (fun t : ℝ => g (a * t) * Complex.exp (-(2 * Real.pi * Complex.I) * ((s * t : ℝ) : ℂ)))
      = fun t : ℝ => (fun u : ℝ => g u * Complex.exp (-(2 * Real.pi * Complex.I) * ((u * (s / a) : ℝ) : ℂ))) (a * t) := by
    funext t
    simp only []
    congr 1
    rw [show s * t = (a * t) * (s / a) by field_simp]
  rw [hfun]
  simp only []
  rw [Measure.integral_comp_mul_left (fun u : ℝ => g u * Complex.exp (-(2 * Real.pi * Complex.I) * ((u * (s / a) : ℝ) : ℂ)))]
  rw [abs_of_pos (inv_pos.mpr ha), Complex.real_smul]
  rw [fourier_real_apply]

/-- Monotonicity of `x ↦ x^e` for a nonpositive exponent `e` on the range `x ≥ 1`. -/
lemma rpow_le_rpow_of_one_le_of_exponent_nonpos {x y e : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (he : e ≤ 0) : y ^ e ≤ x ^ e := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (le_trans hx hxy)
  have h1 : y ^ e = (y ^ (-e))⁻¹ := by simpa using Real.rpow_neg hy0.le (-e)
  have h2 : x ^ e = (x ^ (-e))⁻¹ := by simpa using Real.rpow_neg hx0.le (-e)
  rw [h1, h2]
  simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_rpow hx0.le hxy (neg_nonneg.mpr he))

/-- `∏_{i<k} δ^{i+1} = δ^{k(k+1)/2}`. -/
lemma prod_pow_succ (δ : ℝ) (k : ℕ) :
    (∏ i : Fin k, δ ^ (i.val + 1)) = δ ^ (k * (k + 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin k => i.val + 1) δ,
    Commons.Analysis.Convolution.sum_fin_val_add_one k]

/-- `∏_{i<k} (δ^{i+1})⁻¹ = (δ^{k(k+1)/2})⁻¹`. -/
lemma prod_pow_succ_inv (δ : ℝ) (k : ℕ) :
    (∏ i : Fin k, (δ ^ (i.val + 1))⁻¹) = (δ ^ (k * (k + 1) / 2))⁻¹ := by
  rw [Finset.prod_inv_distrib, prod_pow_succ]

/-- Pointwise product bound: the product `∏ᵢ (1 + cᵢ)^{-A}` is controlled by the anisotropic
gauge `(max 1 (supᵢ cᵢ))^{-A}`. -/
lemma prod_one_add_rpow_neg_le_max_sup {k : ℕ} (hk : 1 ≤ k) {A : ℝ} (hA : 0 < A)
    (c : Fin k → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∏ i : Fin k, (1 + c i) ^ (-A))
      ≤ (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ c)) ^ (-A) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin k)))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩ c
  have hrpow : ∏ i : Fin k, (1 + c i) ^ (-A) = (∏ i : Fin k, (1 + c i)) ^ (-A) :=
    Real.finsetProd_rpow Finset.univ (fun i => 1 + c i) (fun i _ => by linarith [hc i]) (-A)
  rw [hrpow]
  have hge1 : 1 ≤ ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (1 + c i) :=
    Finset.one_le_prod (fun i _ => by linarith [hc i])
  have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin k)) (fun i => 1 + c i)
    (Finset.mem_univ j)
  have hone : 1 + c j ≤ ∏ i : Fin k, (1 + c i) := by
    rw [← hsplit]
    calc 1 + c j = 1 * (1 + c j) := by rw [one_mul]
      _ ≤ (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (1 + c i)) * (1 + c j) :=
          mul_le_mul_of_nonneg_right hge1 (by linarith [hc j])
  calc (∏ i : Fin k, (1 + c i)) ^ (-A)
      ≤ (1 + c j) ^ (-A) :=
        rpow_le_rpow_of_one_le_of_exponent_nonpos (by linarith [hc j]) hone (by linarith)
    _ ≤ (max 1 (c j)) ^ (-A) :=
        rpow_le_rpow_of_one_le_of_exponent_nonpos (le_max_left 1 (c j))
          (max_le (by linarith [hc j]) (by linarith [hc j])) (by linarith)
    _ = (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ c)) ^ (-A) := by
        rw [hj]


/-- **Anisotropic bump function.** For `k ≥ 1` and `A > k` there is a family of functions
`ψ δ` (`0 < δ ≤ 1`) on `ℝ^k` whose Fourier transform is identically `1` on the anisotropic
box `{ξ : |ξᵢ| ≤ δ^{i+1}}`, which is integrable with uniformly bounded `L¹` norm, and which
obeys the anisotropic decay bound `‖ψ δ x‖ ≤ C δ^{k(k+1)/2} (max 1 supᵢ δ^{i+1}|xᵢ|)^{-A}`. -/
theorem aniso_gauge_bump (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : (k : ℝ) < A) : ∃ C : ℝ, 0 < C ∧ ∃ ψ : ℝ → (Fin k → ℝ) → ℂ, (∀ δ : ℝ, 0 < δ → δ ≤ 1 → MeasureTheory.Integrable (ψ δ)) ∧ (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ξ : Fin k → ℝ, (∀ i : Fin k, |ξ i| ≤ δ ^ (i.val + 1)) → (∫ z : Fin k → ℝ, ψ δ z * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i : Fin k, ξ i * z i : ℝ) : ℂ))) = 1) ∧ (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Fin k → ℝ, ‖ψ δ x‖ ≤ C * (δ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => δ ^ (i.val + 1) * |x i|)) ^ (-A))) ∧ (∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∫ z : Fin k → ℝ, ‖ψ δ z‖) ≤ C) := by
  obtain ⟨g, hg⟩ := exists_schwartzMap_fourier_eq_one_Icc
  obtain ⟨N, hNA⟩ := exists_nat_ge A
  obtain ⟨B, hBpos, hBdecay⟩ := schwartzMap_real_decay g N
  set L : ℝ := ∫ t : ℝ, ‖g t‖ with hLdef
  have hLnn : 0 ≤ L := by rw [hLdef]; exact integral_nonneg (fun t => norm_nonneg _)
  have hApos : 0 < A := lt_of_le_of_lt (Nat.cast_nonneg k) hA
  have hgint : Integrable (g : ℝ → ℂ) := g.integrable
  refine ⟨max 1 (max (B ^ k) (L ^ k)), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
      fun δ z => ((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ) * ∏ i : Fin k, g (δ ^ (i.val + 1) * z i),
      ?_, ?_, ?_, ?_⟩
  · -- integrability
    intro δ hδ hδ1
    have hcoord : ∀ i : Fin k, Integrable (fun t : ℝ => g (δ ^ (i.val + 1) * t)) :=
      fun i => hgint.comp_mul_left' (pow_ne_zero _ hδ.ne')
    have hprod : Integrable (fun z : Fin k → ℝ => ∏ i : Fin k, g (δ ^ (i.val + 1) * z i)) :=
      Integrable.fintype_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
        (f := fun i t => g (δ ^ (i.val + 1) * t)) hcoord
    exact hprod.const_mul _
  · -- Fourier transform
    intro δ hδ hδ1 ξ hξ
    have hVal𝓕 : ∀ i : Fin k, 𝓕 (g : ℝ → ℂ) (ξ i / δ ^ (i.val + 1)) = 1 := by
      intro i
      apply hg
      rw [abs_div, abs_of_pos (pow_pos hδ _), div_le_one (pow_pos hδ _)]
      exact hξ i
    have hfac : ∀ i : Fin k,
        (∫ t : ℝ, g (δ ^ (i.val + 1) * t) * Complex.exp (-(2 * Real.pi * Complex.I) * ((ξ i * t : ℝ) : ℂ)))
          = (((δ ^ (i.val + 1) : ℝ)) : ℂ)⁻¹ * 𝓕 (g : ℝ → ℂ) (ξ i / δ ^ (i.val + 1)) := by
      intro i
      have h := fourier_scaling_real g (δ ^ (i.val + 1)) (ξ i) (pow_pos hδ _)
      rw [Complex.ofReal_inv] at h
      exact h
    have hcongr : (∫ z : Fin k → ℝ, (((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ)
          * ∏ i : Fin k, g (δ ^ (i.val + 1) * z i))
          * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i : Fin k, ξ i * z i : ℝ) : ℂ)))
        = ∫ z : Fin k → ℝ, ((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ) * ∏ i : Fin k,
            (g (δ ^ (i.val + 1) * z i) * Complex.exp (-(2 * Real.pi * Complex.I) * ((ξ i * z i : ℝ) : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [hcongr, integral_const_mul]
    simp only [MeasureTheory.volume_pi]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
          (f := fun i t => g (δ ^ (i.val + 1) * t) * Complex.exp (-(2 * Real.pi * Complex.I) * ((ξ i * t : ℝ) : ℂ)))]
    simp only [hfac, hVal𝓕, mul_one]
    have hprodC : ∏ i : Fin k, ((δ ^ (i.val + 1) : ℝ) : ℂ)⁻¹
        = (((δ ^ (k * (k + 1) / 2) : ℝ)) : ℂ)⁻¹ := by
      simp only [← Complex.ofReal_inv]
      rw [← Complex.ofReal_prod, prod_pow_succ_inv, Complex.ofReal_inv]
    rw [hprodC, mul_inv_cancel₀]
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (pow_pos hδ _)
  · -- pointwise bound
    intro δ hδ hδ1 x
    have hterm : ∀ i : Fin k, ‖g (δ ^ (i.val + 1) * x i)‖
        ≤ B * (1 + δ ^ (i.val + 1) * |x i|) ^ (-A) := by
      intro i
      have h1 := hBdecay (δ ^ (i.val + 1) * x i)
      have h2 : (1 + |δ ^ (i.val + 1) * x i|) ^ (-(N : ℝ))
          ≤ (1 + δ ^ (i.val + 1) * |x i|) ^ (-A) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hδ.le _)]
        have hc : 0 ≤ δ ^ (i.val + 1) * |x i| := mul_nonneg (pow_nonneg hδ.le _) (abs_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hBpos.le)
    have hprodbound := prod_one_add_rpow_neg_le_max_sup hk hApos
      (fun i : Fin k => δ ^ (i.val + 1) * |x i|)
      (fun i => mul_nonneg (pow_nonneg hδ.le _) (abs_nonneg _))
    have hprod_norm : ∏ i : Fin k, ‖g (δ ^ (i.val + 1) * x i)‖
        ≤ B ^ k * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            (fun i => δ ^ (i.val + 1) * |x i|))) ^ (-A) := by
      calc ∏ i : Fin k, ‖g (δ ^ (i.val + 1) * x i)‖
          ≤ ∏ i : Fin k, B * (1 + δ ^ (i.val + 1) * |x i|) ^ (-A) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hterm i)
        _ = B ^ k * ∏ i : Fin k, (1 + δ ^ (i.val + 1) * |x i|) ^ (-A) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ k * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun i => δ ^ (i.val + 1) * |x i|))) ^ (-A) :=
            mul_le_mul_of_nonneg_left hprodbound (pow_nonneg hBpos.le k)
    have hCge : B ^ k ≤ max 1 (max (B ^ k) (L ^ k)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    calc ‖((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ) * ∏ i : Fin k, g (δ ^ (i.val + 1) * x i)‖
        = δ ^ (k * (k + 1) / 2) * ∏ i : Fin k, ‖g (δ ^ (i.val + 1) * x i)‖ := by
          rw [norm_mul, norm_prod, Complex.norm_of_nonneg (by positivity)]
      _ ≤ δ ^ (k * (k + 1) / 2) * (B ^ k * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun i => δ ^ (i.val + 1) * |x i|))) ^ (-A)) :=
          mul_le_mul_of_nonneg_left hprod_norm (by positivity)
      _ = B ^ k * (δ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun i => δ ^ (i.val + 1) * |x i|))) ^ (-A)) := by ring
      _ ≤ max 1 (max (B ^ k) (L ^ k)) * (δ ^ (k * (k + 1) / 2) * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun i => δ ^ (i.val + 1) * |x i|))) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hCge (by positivity)
  · -- L^1 bound
    intro δ hδ hδ1
    have hfac4 : ∀ i : Fin k, (∫ t : ℝ, ‖g (δ ^ (i.val + 1) * t)‖) = (δ ^ (i.val + 1))⁻¹ * L := by
      intro i
      have h := Measure.integral_comp_mul_left (fun t : ℝ => ‖g t‖) (δ ^ (i.val + 1))
      rw [abs_of_pos (inv_pos.mpr (pow_pos hδ _)), smul_eq_mul] at h
      rw [hLdef]
      exact h
    have hval : (∫ z : Fin k → ℝ, ‖((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ) * ∏ i : Fin k, g (δ ^ (i.val + 1) * z i)‖)
        = L ^ k := by
      have hL1 : (∫ z : Fin k → ℝ, ‖((δ ^ (k * (k + 1) / 2) : ℝ) : ℂ) * ∏ i : Fin k, g (δ ^ (i.val + 1) * z i)‖)
          = ∫ z : Fin k → ℝ, δ ^ (k * (k + 1) / 2) * ∏ i : Fin k, ‖g (δ ^ (i.val + 1) * z i)‖ := by
        apply integral_congr_ae
        filter_upwards with z
        rw [norm_mul, norm_prod, Complex.norm_of_nonneg (by positivity)]
      rw [hL1, integral_const_mul]
      simp only [MeasureTheory.volume_pi]
      rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
            (f := fun i t => ‖g (δ ^ (i.val + 1) * t)‖)]
      simp only [hfac4]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        prod_pow_succ_inv]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]
    rw [hval]
    calc L ^ k ≤ max (B ^ k) (L ^ k) := le_max_right _ _
      _ ≤ max 1 (max (B ^ k) (L ^ k)) := le_max_right _ _

end

end Commons.Analysis.Fourier