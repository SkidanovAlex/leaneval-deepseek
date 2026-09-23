import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Commons.Analysis.Calculus

/-- If `|u| ≤ 1` and `|v| ≤ w` then `u * v ≤ w`. -/
lemma abs_mul_le_of_abs_le_one {u v w : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ w) : u * v ≤ w := by
  calc u * v ≤ |u * v| := le_abs_self _
    _ = |u| * |v| := abs_mul u v
    _ ≤ 1 * w := mul_le_mul hu hv (abs_nonneg v) (by norm_num)
    _ = w := one_mul w

/-- `|sin s - s| ≤ s ^ 2 / 2` for `|s| ≤ 1`. -/
lemma abs_sin_sub_self_le_sq {s : ℝ} (hs : |s| ≤ 1) : |Real.sin s - s| ≤ s ^ 2 / 2 := by
  have h := Real.abs_sub_sin_le s
  rw [abs_sub_comm] at h
  have hle : |s| ^ 3 ≤ s ^ 2 := by
    have h2 : |s| ^ 3 ≤ |s| ^ 2 := by
      calc |s| ^ 3 = |s| ^ 2 * |s| := by ring
        _ ≤ |s| ^ 2 * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = |s| ^ 2 := by ring
    simpa [sq_abs] using h2
  calc |Real.sin s - s| ≤ |s| ^ 3 / 6 := h
    _ ≤ s ^ 2 / 2 := by linarith [hle, sq_nonneg s]

/-- Second-order lower Taylor bound for `cos` around `a`: for `|s| ≤ 1`,
`cos a - sin a * s - s ^ 2 ≤ cos (a + s)`. -/
lemma cos_add_ge {a s : ℝ} (hs : |s| ≤ 1) :
    Real.cos a - Real.sin a * s - s ^ 2 ≤ Real.cos (a + s) := by
  have hcos : Real.cos a - s ^ 2 / 2 ≤ Real.cos a * Real.cos s := by
    have hc1 : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
    have h1 : |1 - Real.cos s| ≤ s ^ 2 / 2 := by
      rw [abs_of_nonneg (by linarith [Real.cos_le_one s])]
      linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
    have h4 : Real.cos a * (1 - Real.cos s) ≤ s ^ 2 / 2 :=
      abs_mul_le_of_abs_le_one hc1 h1
    nlinarith [h4]
  have hsin : -Real.sin a * s - s ^ 2 / 2 ≤ -Real.sin a * Real.sin s := by
    have hs1 : |Real.sin a| ≤ 1 := Real.abs_sin_le_one a
    have h1 : |Real.sin s - s| ≤ s ^ 2 / 2 := abs_sin_sub_self_le_sq hs
    have h4 : Real.sin a * (Real.sin s - s) ≤ s ^ 2 / 2 :=
      abs_mul_le_of_abs_le_one hs1 h1
    linarith [h4]
  rw [Real.cos_add]
  linarith [hcos, hsin]

/-- Upper Taylor bound: `cos a * cos t ≤ cos a + t ^ 2 / 2`. -/
lemma cos_mul_cos_upper (a t : ℝ) : Real.cos a * Real.cos t ≤ Real.cos a + t ^ 2 / 2 := by
  have h1 : -(1 : ℝ) ≤ Real.cos a := Real.neg_one_le_cos a
  have h2 : 1 - Real.cos t ≤ t ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have h3 : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
  have h4 : -(1 : ℝ) * (1 - Real.cos t) ≤ Real.cos a * (1 - Real.cos t) :=
    mul_le_mul_of_nonneg_right h1 h3
  have h5 : -(t ^ 2 / 2) ≤ -(1 : ℝ) * (1 - Real.cos t) := by linarith [h2]
  nlinarith [h4, h5]

theorem eventually_cos_sub_model_le {a R C : ℝ} (ha : 0 < a) (haπ : a < Real.pi) (hC : 0 ≤ C)
    {ρ : ℝ → ℝ}
    (hbound : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), |ρ t - a| ≤ C * t)
    (hlim : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ t ≤ a + t * R + ε * t) :
    ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      -ε * t ≤ Real.cos (ρ t) - (Real.cos a * Real.cos t - R * Real.sin a * Real.sin t) := by
  intro ε hε
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  set δ : ℝ := ε / (2 * Real.sin a) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hsinδ : Real.sin a * δ = ε / 2 := by
    rw [hδdef]; field_simp
  set K : ℝ := C ^ 2 + 1 / 2 + |R * Real.sin a| / 2 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hC1 : 0 < C + 1 := by linarith
  have hT2 : (0 : ℝ) < 1 / (C + 1) := div_pos one_pos hC1
  have hT3 : (0 : ℝ) < ε / (2 * K + 2) := by
    apply div_pos hε; linarith
  filter_upwards [hbound, hlim δ hδpos,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hT2).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hT3).filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < t from self_mem_nhdsWithin)]
    with t hb hlimt ht1 htC htK ht0
  have hCt1 : C * t < 1 := by
    have hle : C * t ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left htC.le hC
    have heq : C * (1 / (C + 1)) = C / (C + 1) := by ring
    rw [heq] at hle
    have hlt : C / (C + 1) < 1 := by rw [div_lt_one hC1]; linarith
    linarith
  have hs1 : |ρ t - a| ≤ 1 := le_trans hb hCt1.le
  have ht_abs1 : |t| ≤ 1 := by rw [abs_of_pos ht0]; linarith
  have hs2 : (ρ t - a) ^ 2 ≤ C ^ 2 * t ^ 2 := by
    have hCt0 : 0 ≤ C * t := mul_nonneg hC ht0.le
    have hy := abs_le.mp hb
    nlinarith [hy.1, hy.2, hCt0]
  have hKt : K * t ≤ ε / 2 := by
    have hle : K * t ≤ K * (ε / (2 * K + 2)) := mul_le_mul_of_nonneg_left htK.le hKnn
    have hpos : (0 : ℝ) < 2 * K + 2 := by linarith
    have hb2 : K * (ε / (2 * K + 2)) ≤ ε / 2 := by
      have heq : K * (ε / (2 * K + 2)) = K * ε / (2 * K + 2) := by ring
      rw [heq, div_le_iff₀ hpos]
      nlinarith [hε]
    linarith
  have hKt2 : K * t ^ 2 ≤ ε / 2 * t := by
    have heq : K * t ^ 2 = (K * t) * t := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hKt ht0.le
  have hA : Real.cos a - Real.sin a * (ρ t - a) - (ρ t - a) ^ 2 ≤ Real.cos (ρ t) := by
    have h := cos_add_ge (a := a) (s := ρ t - a) hs1
    have hlt : a + (ρ t - a) = ρ t := by ring
    rwa [hlt] at h
  have hB : -Real.cos a - t ^ 2 / 2 ≤ -Real.cos a * Real.cos t := by
    have h := cos_mul_cos_upper a t
    linarith
  have hC2 : R * Real.sin a * t - |R * Real.sin a| * (t ^ 2 / 2) ≤ R * Real.sin a * Real.sin t := by
    have h2 : |Real.sin t - t| ≤ t ^ 2 / 2 := abs_sin_sub_self_le_sq ht_abs1
    have h3 : -(|R * Real.sin a| * |Real.sin t - t|) ≤ R * Real.sin a * (Real.sin t - t) := by
      have hh := neg_abs_le (R * Real.sin a * (Real.sin t - t))
      rwa [abs_mul] at hh
    have h4 : |R * Real.sin a| * |Real.sin t - t| ≤ |R * Real.sin a| * (t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    nlinarith [h3, h4]
  have hsinδt : Real.sin a * δ * t = ε / 2 * t := by rw [hsinδ]
  have hD : -(Real.sin a * R * t + Real.sin a * δ * t) ≤ -Real.sin a * (ρ t - a) := by
    have h1 : -(R + δ) * t ≤ a - ρ t := by nlinarith [hlimt]
    have h2 : Real.sin a * (-(R + δ) * t) ≤ Real.sin a * (a - ρ t) :=
      mul_le_mul_of_nonneg_left h1 hsina.le
    nlinarith [h2]
  have htotal : -(ε / 2) * t - (C ^ 2 + 1 / 2 + |R * Real.sin a| / 2) * t ^ 2 ≤
      Real.cos (ρ t) - (Real.cos a * Real.cos t - R * Real.sin a * Real.sin t) := by
    linarith [hA, hB, hC2, hD, hs2, hsinδt]
  have hfinal : -ε * t ≤ -(ε / 2) * t - (C ^ 2 + 1 / 2 + |R * Real.sin a| / 2) * t ^ 2 := by
    rw [hKdef] at hKt2
    linarith [hKt2]
  linarith [htotal, hfinal]

end Commons.Analysis.Calculus