import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Classical

/-- Change of variables `v = k * t ^ (-(2/3))` in the improper integral over `(0, b)`:
for `c, z, k, b > 0` and any `G : ℝ → ℝ`,
`∫_{0}^{b} (c · t^{2/3} · z)⁻¹ · G (k · t^{-2/3}) dt
   = (3/2) · k^{1/2} / (c · z) · ∫_{k b^{-2/3}}^{∞} G v · v^{-3/2} dv`. -/
theorem integral_Ioo_subst_rpow_neg_two_thirds {c z k b : ℝ} (hc : 0 < c) (hz : 0 < z)
    (hk : 0 < k) (hb : 0 < b) (G : ℝ → ℝ) :
    (∫ t in Set.Ioo (0:ℝ) b, (1 / (c * t ^ ((2:ℝ)/3) * z)) * G (k * t ^ (-(2:ℝ)/3)))
      = (3/2) * k ^ ((1:ℝ)/2) / (c * z)
        * (∫ v in Set.Ioi (k * b ^ (-(2:ℝ)/3)), G v * v ^ (-(3:ℝ)/2)) := by
  -- Differentiability of `t ↦ k * t ^ (-(2/3))` on the open interval `(0, b)`.
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) b,
      HasDerivWithinAt (fun s : ℝ => k * s ^ (-(2:ℝ)/3))
        (k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1))) (Set.Ioo (0:ℝ) b) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s ^ (-(2:ℝ)/3))
        ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht.1))
    exact (h1.const_mul k).hasDerivWithinAt
  -- Injectivity on `(0, b)`.
  have hinj : InjOn (fun t : ℝ => k * t ^ (-(2:ℝ)/3)) (Set.Ioo (0:ℝ) b) := by
    intro x hx y hy hxy
    have hx0 : (0:ℝ) ≤ x := le_of_lt hx.1
    have hy0 : (0:ℝ) ≤ y := le_of_lt hy.1
    have hxy' : x ^ (-(2:ℝ)/3) = y ^ (-(2:ℝ)/3) := mul_left_cancel₀ (ne_of_gt hk) hxy
    exact Real.rpow_left_injOn (by norm_num : (-(2:ℝ)/3) ≠ 0) hx0 hy0 hxy'
  -- The image of `(0, b)` under `t ↦ k * t ^ (-(2/3))` is `(k * b^{-2/3}, ∞)`.
  have himage : (fun t : ℝ => k * t ^ (-(2:ℝ)/3)) '' Set.Ioo (0:ℝ) b
      = Set.Ioi (k * b ^ (-(2:ℝ)/3)) := by
    have hp_neg : (-(2:ℝ)/3 : ℝ) < 0 := by norm_num
    have hb_p_pos : 0 < b ^ (-(2:ℝ)/3) := Real.rpow_pos_of_pos hb _
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hmem_t : t ∈ Set.Ioi (0:ℝ) := ht.1
      have hmem_b : b ∈ Set.Ioi (0:ℝ) := hb
      have hlt : b ^ (-(2:ℝ)/3) < t ^ (-(2:ℝ)/3) :=
        (Real.strictAntiOn_rpow_Ioi_of_exponent_neg hp_neg) hmem_t hmem_b ht.2
      exact mul_lt_mul_of_pos_left hlt hk
    · intro hv
      have hv_gt : k * b ^ (-(2:ℝ)/3) < v := hv
      have hv_pos : 0 < v := lt_trans (mul_pos hk hb_p_pos) hv_gt
      have hx_pos : 0 < v / k := div_pos hv_pos hk
      refine ⟨(v / k) ^ (-(3:ℝ)/2), ?_, ?_⟩
      · constructor
        · exact Real.rpow_pos_of_pos hx_pos _
        · have h1 : b ^ (-(2:ℝ)/3) < v / k := by
            rw [lt_div_iff₀ hk]; linarith
          have h3neg : (-(3:ℝ)/2 : ℝ) < 0 := by norm_num
          have hmem1 : b ^ (-(2:ℝ)/3) ∈ Set.Ioi (0:ℝ) := hb_p_pos
          have hmem2 : v / k ∈ Set.Ioi (0:ℝ) := hx_pos
          have h2 : (v / k) ^ (-(3:ℝ)/2) < (b ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) :=
            (Real.strictAntiOn_rpow_Ioi_of_exponent_neg h3neg) hmem1 hmem2 h1
          have hb_eq : (b ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = b := by
            rw [← Real.rpow_mul hb.le]
            norm_num
          rwa [hb_eq] at h2
      · show k * ((v / k) ^ (-(3:ℝ)/2)) ^ (-(2:ℝ)/3) = v
        rw [← Real.rpow_mul (le_of_lt hx_pos) (-(3:ℝ)/2) (-(2:ℝ)/3)]
        have hexp : (-(3:ℝ)/2) * (-(2:ℝ)/3) = (1:ℝ) := by norm_num
        rw [hexp, Real.rpow_one]
        field_simp
  -- Pointwise identity of the two integrands (after substitution).
  have hscalar_gen : ∀ t : ℝ, 0 < t →
      (1 / (c * t ^ ((2:ℝ)/3) * z))
      = |k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1))|
        * ((3/2) * k ^ ((1:ℝ)/2) / (c*z) * (k * t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2)) := by
    intro t ht
    have htp : (0:ℝ) < t ^ ((-(2:ℝ)/3) - 1) := Real.rpow_pos_of_pos ht _
    have hneg : k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1)) ≤ 0 := by
      have h1 : (-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1) < 0 :=
        mul_neg_of_neg_of_pos (by norm_num) htp
      nlinarith [hk]
    have hA : |k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1))|
        = k * ((2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1) := by
      rw [abs_of_nonpos hneg]; ring
    have hB : (k * t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = k ^ (-(3:ℝ)/2) * t := by
      rw [Real.mul_rpow hk.le (Real.rpow_nonneg ht.le _)]
      rw [← Real.rpow_mul ht.le (-(2:ℝ)/3) (-(3:ℝ)/2)]
      rw [show (-(2:ℝ)/3) * (-(3:ℝ)/2) = (1:ℝ) by norm_num, Real.rpow_one]
    have hkcomb : k * k ^ ((1:ℝ)/2) * k ^ (-(3:ℝ)/2) = 1 := by
      have h1 : k ^ ((1:ℝ)/2) * k ^ (-(3:ℝ)/2) = k ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add hk]; norm_num
      calc k * k ^ ((1:ℝ)/2) * k ^ (-(3:ℝ)/2)
          = k * (k ^ ((1:ℝ)/2) * k ^ (-(3:ℝ)/2)) := by ring
        _ = k * k ^ (-(1:ℝ)) := by rw [h1]
        _ = 1 := by rw [Real.rpow_neg_one k, mul_inv_cancel₀ (ne_of_gt hk)]
    have htcomb : t ^ ((-(2:ℝ)/3) - 1) * t = t ^ (-(2:ℝ)/3) := by
      rw [show (-(2:ℝ)/3) - 1 = (-(2:ℝ)/3) + (-1) by norm_num, Real.rpow_add ht,
          Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]
    have hD : 1 / (c * t ^ ((2:ℝ)/3) * z) = (1/(c*z)) * t ^ (-(2:ℝ)/3) := by
      rw [show (-(2:ℝ)/3 : ℝ) = -((2:ℝ)/3) by norm_num, Real.rpow_neg ht.le (2/3)]
      field_simp
    rw [hA, hB, hD]
    rw [show k * ((2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1)
            * ((3:ℝ)/2 * k ^ ((1:ℝ)/2) / (c*z) * (k ^ (-(3:ℝ)/2) * t))
          = (1/(c*z)) * (k * k ^ ((1:ℝ)/2) * k ^ (-(3:ℝ)/2))
            * (t ^ ((-(2:ℝ)/3) - 1) * t) by ring]
    rw [hkcomb, htcomb]; ring
  -- Change of variables.
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0:ℝ) b)
      (f := fun t : ℝ => k * t ^ (-(2:ℝ)/3))
      (f' := fun t : ℝ => k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1)))
      (g := fun v : ℝ => (3/2) * k ^ ((1:ℝ)/2) / (c*z) * (G v * v ^ (-(3:ℝ)/2)))
      measurableSet_Ioo hderiv hinj
  rw [himage] at key
  have key2 : (∫ x in Set.Ioo (0:ℝ) b, |k * ((-(2:ℝ)/3) * x ^ ((-(2:ℝ)/3) - 1))|
        * ((3/2) * k ^ ((1:ℝ)/2) / (c*z)
            * (G (k * x ^ (-(2:ℝ)/3)) * (k * x ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2))))
      = ∫ x in Set.Ioi (k * b ^ (-(2:ℝ)/3)),
          (3/2) * k ^ ((1:ℝ)/2) / (c*z) * (G x * x ^ (-(3:ℝ)/2)) := by
    simpa only [smul_eq_mul] using key.symm
  have h1 : (∫ t in Set.Ioo (0:ℝ) b, (1 / (c * t ^ ((2:ℝ)/3) * z)) * G (k * t ^ (-(2:ℝ)/3)))
      = ∫ t in Set.Ioo (0:ℝ) b, |k * ((-(2:ℝ)/3) * t ^ ((-(2:ℝ)/3) - 1))|
          * ((3/2) * k ^ ((1:ℝ)/2) / (c*z) * (G (k * t ^ (-(2:ℝ)/3))
              * (k * t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2))) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [hscalar_gen t ht.1]
    ring
  have h2 : (∫ v in Set.Ioi (k * b ^ (-(2:ℝ)/3)),
        (3/2) * k ^ ((1:ℝ)/2) / (c*z) * (G v * v ^ (-(3:ℝ)/2)))
      = (3/2) * k ^ ((1:ℝ)/2) / (c*z)
        * (∫ v in Set.Ioi (k * b ^ (-(2:ℝ)/3)), G v * v ^ (-(3:ℝ)/2)) := by
    rw [MeasureTheory.integral_const_mul]
  rw [h1, key2, h2]

end Commons.Analysis.Integral