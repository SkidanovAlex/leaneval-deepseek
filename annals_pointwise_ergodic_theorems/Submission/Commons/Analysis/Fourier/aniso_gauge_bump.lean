import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

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
    Finset.one_le_prod₀ (fun i _ => by linarith [hc i])
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


end

end Commons.Analysis.Fourier