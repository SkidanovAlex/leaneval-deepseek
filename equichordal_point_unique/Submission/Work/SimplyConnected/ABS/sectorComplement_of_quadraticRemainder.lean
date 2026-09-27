import Mathlib

namespace Work.SimplyConnected.ABS

open Complex

/-- **A sector in the complement of a level set, from a quadratic Taylor remainder.**
Let `g : ℂ → ℂ` satisfy `g w₀ ≠ 0`, let `d ≠ 0`, and suppose the first-order Taylor remainder of `g`
at `w₀` is `O (‖v‖ ^ 2)`. Then there are non-zero real-linear functionals `L₁ L₂` spanning a
non-empty sector and `δ > 0` such that no point `v` of the sector with `‖v‖ < δ` has
`‖g (w₀ + v)‖ < ‖g w₀‖`. -/
theorem sectorComplement_of_quadraticRemainder {g : ℂ → ℂ} {w₀ d : ℂ}
    (hg0 : g w₀ ≠ 0) (hd : d ≠ 0)
    (hrem : ∃ C : ℝ, ∀ᶠ v in nhds (0 : ℂ),
      ‖g (w₀ + v) - g w₀ - d * v‖ ≤ C * ‖v‖ ^ 2) :
    ∃ (L₁ L₂ : ℂ →L[ℝ] ℝ) (δ : ℝ), L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ 0 < δ ∧
      (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ v : ℂ, ‖v‖ < δ → ‖g (w₀ + v)‖ < ‖g w₀‖ → ¬ (0 < L₁ v ∧ 0 < L₂ v) := by
  -- Unpack the `O (‖v‖ ^ 2)` remainder into an actual ball around `0`.
  obtain ⟨C, hC⟩ := hrem
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp hC
  -- The privileged direction: `v ↦ Re (conj (g w₀) * d * v)` is the linear term of
  -- `‖g (w₀ + v)‖ ^ 2 = ‖g w₀‖ ^ 2 + 2 Re (conj (g w₀) * d * v) + O (‖v‖ ^ 2)`.
  have hgc : (starRingEnd ℂ) (g w₀) ≠ 0 := by simpa using star_ne_zero.mpr hg0
  let a : ℂ := (starRingEnd ℂ) (g w₀) * d
  have ha : a ≠ 0 := mul_ne_zero hgc hd
  -- The two functionals cut out the cone `{v | Re (a v) > |Im (a v)|}` of half-angle `π / 4`
  -- around the direction of `a`, on which `Re (a v) ≥ ‖a‖ ‖v‖ / 2`.
  let L₁ : ℂ →L[ℝ] ℝ := (Complex.reCLM + Complex.imCLM).comp (a • (1 : ℂ →L[ℝ] ℂ))
  let L₂ : ℂ →L[ℝ] ℝ := (Complex.reCLM - Complex.imCLM).comp (a • (1 : ℂ →L[ℝ] ℂ))
  have hL₁ : ∀ v : ℂ, L₁ v = (a * v).re + (a * v).im := by
    intro v; simp [L₁]
  have hL₂ : ∀ v : ℂ, L₂ v = (a * v).re - (a * v).im := by
    intro v; simp [L₂]
  -- Non-degeneracy, witnessed by `a⁻¹` where both functionals take the value `1`.
  have hne₁ : L₁ ≠ 0 := by
    intro h
    have h1 : L₁ a⁻¹ = 0 := by rw [h]; rfl
    rw [hL₁ a⁻¹, mul_inv_cancel₀ ha] at h1
    simp at h1
  have hne₂ : L₂ ≠ 0 := by
    intro h
    have h1 : L₂ a⁻¹ = 0 := by rw [h]; rfl
    rw [hL₂ a⁻¹, mul_inv_cancel₀ ha] at h1
    simp at h1
  -- The size parameters for the threshold `δ`.
  set K : ℝ := max C 0 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hKdef]; exact le_max_left _ _
  set B : ℝ := ‖a‖ with hBdef
  have hB : 0 < B := by rw [hBdef]; exact norm_pos_iff.mpr ha
  have hA : 0 < ‖g w₀‖ := norm_pos_iff.mpr hg0
  set δ : ℝ := min ε₁ (min 1 (B / (2 * ‖g w₀‖ * (K + 1)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hε₁pos (lt_min one_pos (div_pos hB (by nlinarith [hA, hK])))
  have hδle₁ : δ ≤ ε₁ := by rw [hδdef]; exact min_le_left _ _
  have hδle1 : δ ≤ 1 := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleB : δ ≤ B / (2 * ‖g w₀‖ * (K + 1)) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨L₁, L₂, δ, hne₁, hne₂, hδpos, ⟨a⁻¹, ?_, ?_⟩, ?_⟩
  · rw [hL₁ a⁻¹, mul_inv_cancel₀ ha]; simp
  · rw [hL₂ a⁻¹, mul_inv_cancel₀ ha]; simp
  · -- Main step: a point of the sector of small norm cannot have smaller norm-image.
    intro v hvnorm hlt hsect
    obtain ⟨hs1, hs2⟩ := hsect
    rw [hL₁ v] at hs1
    rw [hL₂ v] at hs2
    -- Inside the sector, `Re (a v) > |Im (a v)|`, hence `‖a v‖ ≤ 2 Re (a v)`.
    have habs : |(a * v).im| < (a * v).re := by
      rw [abs_lt]; constructor <;> linarith
    have hPpos : 0 < (a * v).re := lt_of_le_of_lt (abs_nonneg _) habs
    have hsq : (a * v).re ^ 2 + (a * v).im ^ 2 = ‖a * v‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hsq2 : (a * v).im ^ 2 < (a * v).re ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hPpos]
      exact habs
    have hBs : ‖a * v‖ ≤ 2 * (a * v).re := by
      have h : ‖a * v‖ ^ 2 ≤ (2 * (a * v).re) ^ 2 := by
        rw [← hsq]; nlinarith [hsq2, sq_nonneg ((a * v).re)]
      have h1 := (sq_le_sq.mp h)
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith)] at h1
    have hnorms : ‖a * v‖ = B * ‖v‖ := by rw [hBdef, Complex.norm_mul]
    have hBs1 : B * ‖v‖ ≤ 2 * (a * v).re := by rw [hnorms] at hBs; exact hBs
    -- The quadratic remainder is dominated by `K ‖v‖ ^ 2` on the ball of radius `ε₁`.
    have hsε : ‖v‖ < ε₁ := lt_of_lt_of_le hvnorm hδle₁
    have hremb : ‖g (w₀ + v) - g w₀ - d * v‖ ≤ K * ‖v‖ ^ 2 := by
      have hvball : v ∈ Metric.ball (0:ℂ) ε₁ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hsε
      have h1 := hε₁ hvball
      have h2 : C * ‖v‖ ^ 2 ≤ K * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hCK (sq_nonneg _)
      exact le_trans h1 h2
    have hs1' : ‖v‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hvnorm hδle1)
    have hδmul : 2 * ‖g w₀‖ * (K + 1) * δ ≤ B := by
      have hcpos : 0 < 2 * ‖g w₀‖ * (K + 1) := by nlinarith [hA, hK]
      have hle : δ * (2 * ‖g w₀‖ * (K + 1)) ≤ B := (le_div_iff₀ hcpos).mp hδleB
      nlinarith [hle]
    -- The linear gain `Re (a v) / ‖g w₀‖` beats the quadratic loss `K ‖v‖ ^ 2`.
    have hK_s_sq : K * ‖v‖ ^ 2 ≤ (a * v).re / ‖g w₀‖ := by
      rw [le_div_iff₀ hA]
      have hstep1 : K * ‖g w₀‖ * δ ≤ B / 2 := by
        nlinarith [hδmul, hK, hA, le_of_lt hδpos]
      have hstep2 : K * ‖v‖ * ‖g w₀‖ ≤ B / 2 := by
        nlinarith [hstep1, hvnorm, hK, hA, norm_nonneg v]
      have hstep3 : K * ‖v‖ ^ 2 * ‖g w₀‖ ≤ B * ‖v‖ / 2 := by
        nlinarith [hstep2, norm_nonneg v]
      linarith [hstep3, hBs1]
    -- Cauchy–Schwarz against `g w₀`: `‖g w₀‖ * ‖g w₀ + d v‖ ≥ ‖g w₀‖ ^ 2 + Re (a v)`.
    have hF6 : ‖g w₀‖ + (a * v).re / ‖g w₀‖ ≤ ‖g w₀ + d * v‖ := by
      have hkey : ‖g w₀‖ ^ 2 + (a * v).re ≤ ‖g w₀‖ * ‖g w₀ + d * v‖ := by
        have h_exp : ((starRingEnd ℂ) (g w₀) * (g w₀ + d * v)).re
            = ‖g w₀‖ ^ 2 + ((starRingEnd ℂ) (g w₀) * (d * v)).re := by
          simp only [mul_add, Complex.add_re, Complex.mul_re, Complex.conj_re,
            Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
          ring
        have hle : ((starRingEnd ℂ) (g w₀) * (g w₀ + d * v)).re
            ≤ ‖(starRingEnd ℂ) (g w₀) * (g w₀ + d * v)‖ := Complex.re_le_norm _
        rw [Complex.norm_mul, Complex.norm_conj] at hle
        have hae : a * v = (starRingEnd ℂ) (g w₀) * (d * v) := by
          show ((starRingEnd ℂ) (g w₀) * d) * v = _
          ring
        rw [hae]
        linarith [h_exp, hle]
      have hdiv : (‖g w₀‖ ^ 2 + (a * v).re) / ‖g w₀‖ ≤ ‖g w₀ + d * v‖ := by
        rw [div_le_iff₀ hA]; linarith
      have hEq : (‖g w₀‖ ^ 2 + (a * v).re) / ‖g w₀‖
          = ‖g w₀‖ + (a * v).re / ‖g w₀‖ := by
        field_simp
      linarith [hdiv, hEq]
    -- Reverse triangle inequality and the remainder bound.
    have hF4 : ‖g w₀ + d * v‖ - K * ‖v‖ ^ 2 ≤ ‖g (w₀ + v)‖ := by
      have h2 := neg_le_abs (‖g (w₀ + v)‖ - ‖g w₀ + d * v‖)
      have h3 := abs_norm_sub_norm_le (g (w₀ + v)) (g w₀ + d * v)
      have hb : g (w₀ + v) - (g w₀ + d * v) = g (w₀ + v) - g w₀ - d * v := by ring
      rw [hb] at h3
      linarith [h2, h3, hremb]
    have hfin : ‖g w₀‖ ≤ ‖g (w₀ + v)‖ := by linarith [hF6, hF4, hK_s_sq]
    linarith [hfin, hlt]

end Work.SimplyConnected.ABS
