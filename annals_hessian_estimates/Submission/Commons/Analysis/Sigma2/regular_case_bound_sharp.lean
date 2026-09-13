import Mathlib.Algebra.Order.Star.Real

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Sigma2

open scoped BigOperators

private theorem sq_le_nine_of_abs_le_three {x : ℝ} (h : |x| ≤ 3) : x ^ 2 ≤ 9 := by
  have h1 := abs_le.mp h
  nlinarith [h1.1, h1.2]

private theorem one_le_of_two_le_sq {S : ℝ} (hS : 0 < S) (h : 2 ≤ S ^ 2) : 1 ≤ S := by
  nlinarith [hS, h, sq_nonneg (S - 1)]

open scoped BigOperators in
theorem regular_case_bound_sharp {S rho b α β Γ : ℝ} {lam xc u D1b : Fin 4 → ℝ}
    (hb : 0 < b) (hrho : 0 < rho) (hrho9 : rho < 9) (hS : 0 < S) (hΓ : 4 ≤ Γ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβΓ : β * Γ ≤ α / 4)
    (hbS : b ≤ S) (hS2 : 2 ≤ S ^ 2)
    (hxc : ∀ i : Fin 4, |xc i| ≤ 3) (hu : ∀ i : Fin 4, |u i| ≤ Γ)
    (hfs3 : (∑ i : Fin 4, (S - lam i)) = 3 * S)
    (hfsnn : ∀ i : Fin 4, 0 ≤ S - lam i)
    (hlam0 : 0 < lam 0) (hlarge : S / 4 ≤ lam 0)
    (hf0 : S / 16 ≤ (S - lam 0) * (lam 0) ^ 2)
    (hx1 : 1 / 4 ≤ (xc 0) ^ 2)
    (hmax1 : ∀ i : Fin 4, D1b i / b = 4 * xc i / rho - α * xc i * lam i - β * u i * lam i)
    (hmaxP : -12 * S / rho - 8 * (∑ i : Fin 4, (S - lam i) * (xc i) ^ 2) / rho ^ 2 + 2 * α
        + β * (∑ i : Fin 4, (S - lam i) * (lam i) ^ 2)
        + (1 / 36) * ((1 / b) * (∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2)) ≤ 0) :
    rho ^ 2 * b ≤ 11943936 / α ^ 2 := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hS1 : 1 ≤ S := one_le_of_two_le_sq hS hS2
  set g : Fin 4 → ℝ := fun i => 4 * xc i / rho - α * xc i * lam i - β * u i * lam i with hgdef
  have hD : ∀ i : Fin 4, D1b i = b * g i := by
    intro i
    have h := hmax1 i
    rw [div_eq_iff hbne] at h
    simp only [hgdef]
    rw [h]; ring
  -- Abbreviations for the sums appearing in `hmaxP`.
  set T2 : ℝ := ∑ i : Fin 4, (S - lam i) * (xc i) ^ 2 with hT2
  set T3 : ℝ := ∑ i : Fin 4, (S - lam i) * (lam i) ^ 2 with hT3
  set P : ℝ := ∑ i : Fin 4, (S - lam i) * (g i) ^ 2 with hP
  have hWsum : (∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2) = b ^ 2 * P := by
    rw [hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hD i]; ring
  have hmaxP' : -12 * S / rho - 8 * T2 / rho ^ 2 + 2 * α + β * T3 + (b / 36) * P ≤ 0 := by
    have h := hmaxP
    have hWb : (1 / 36) * ((1 / b) * (∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2))
        = (b / 36) * P := by
      rw [hWsum]
      field_simp
    rw [hWb] at h
    exact h
  have hT3nn : 0 ≤ T3 := by
    rw [hT3]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hfsnn i) (sq_nonneg _))
  have hβT3 : 0 ≤ β * T3 := mul_nonneg hβ hT3nn
  -- Clear the denominators in `hmaxP'`.
  have hPle_poly : (b / 36) * P * rho ^ 2 ≤ 12 * S * rho + 8 * T2 := by
    have h1 : (-12 * S / rho - 8 * T2 / rho ^ 2 + 2 * α + β * T3 + (b / 36) * P) * rho ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmaxP' (by positivity)
    have e : (-12 * S / rho - 8 * T2 / rho ^ 2 + 2 * α + β * T3 + (b / 36) * P) * rho ^ 2
        = -12 * S * rho - 8 * T2 + (2 * α + β * T3) * rho ^ 2 + (b / 36) * P * rho ^ 2 := by
      field_simp
      ring
    rw [e] at h1
    nlinarith [h1, hα, hβT3, sq_nonneg rho]
  have hxc2 : ∀ i : Fin 4, (xc i) ^ 2 ≤ 9 := fun i => sq_le_nine_of_abs_le_three (hxc i)
  have hT2le : T2 ≤ 27 * S := by
    rw [hT2]
    calc ∑ i : Fin 4, (S - lam i) * (xc i) ^ 2
        ≤ ∑ i : Fin 4, (S - lam i) * 9 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hxc2 i) (hfsnn i))
      _ = 27 * S := by rw [← Finset.sum_mul, hfs3]; ring
  have hRHS_poly : 12 * S * rho + 8 * T2 ≤ 324 * S := by
    have h2 : 8 * T2 ≤ 216 * S := by nlinarith [hT2le]
    have h1 : 12 * S * rho ≤ 108 * S := by nlinarith [hrho, hrho9, hS]
    linarith [h1, h2]
  have hkey_poly : (b / 36) * P * rho ^ 2 ≤ 324 * S := le_trans hPle_poly hRHS_poly
  have hObj : rho ^ 2 * b * α ^ 2 ≤ 11943936 := by
    by_cases hcase : 16 ≤ α * lam 0 * rho
    · -- Case A: the coordinate `0` is large.
      have hcancel : 4 / rho ≤ α * lam 0 := by
        rw [div_le_iff₀ hrho]; nlinarith [hcase]
      have hcos : 0 ≤ α * lam 0 - 4 / rho := by linarith [hcancel]
      have hxc0abs : (1 : ℝ) / 2 ≤ |xc 0| := by
        have h1 : ((1 : ℝ) / 2) ^ 2 ≤ (xc 0) ^ 2 := by
          rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]; exact hx1
        have h2 := (sq_le_sq).mp h1
        rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h2
      have hg0eq : g 0 = xc 0 * (4 / rho - α * lam 0) - β * u 0 * lam 0 := by
        simp only [hgdef]; ring
      have hneg : 4 / rho - α * lam 0 ≤ 0 := by linarith [hcos]
      have habs1 : |4 / rho - α * lam 0| = α * lam 0 - 4 / rho := by
        rw [abs_of_nonpos hneg]; ring
      have hA : (1 / 2) * (α * lam 0 - 4 / rho)
          ≤ |xc 0| * |4 / rho - α * lam 0| := by
        rw [habs1]
        exact mul_le_mul_of_nonneg_right hxc0abs hcos
      have hbu : |β * u 0 * lam 0| ≤ (α / 4) * lam 0 := by
        have h1 : |β * u 0 * lam 0| ≤ β * Γ * lam 0 := by
          rw [show β * u 0 * lam 0 = (β * u 0) * lam 0 by ring, abs_mul, abs_mul,
            abs_of_nonneg hβ, abs_of_pos hlam0]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hu 0) hβ) (le_of_lt hlam0)
        have h2 : β * Γ * lam 0 ≤ (α / 4) * lam 0 :=
          mul_le_mul_of_nonneg_right hβΓ (le_of_lt hlam0)
        nlinarith [h1, h2]
      have hAB : |xc 0| * |4 / rho - α * lam 0| - |β * u 0 * lam 0| ≤ |g 0| := by
        rw [hg0eq]
        have h1 : |xc 0| * |4 / rho - α * lam 0| = |xc 0 * (4 / rho - α * lam 0)| :=
          (abs_mul _ _).symm
        rw [h1]
        exact abs_sub_abs_le_abs_sub _ _
      have h4rho : 4 / rho ≤ α * lam 0 / 4 := by
        rw [div_le_iff₀ hrho]
        nlinarith [hcase]
      have h2rho : (4 / rho) / 2 ≤ α * lam 0 / 8 := by linarith [h4rho]
      have hfin : α * lam 0 / 8 ≤ |g 0| := by
        have h3 : α * lam 0 / 8 ≤ (1 / 2) * (α * lam 0 - 4 / rho) - (α / 4) * lam 0 := by
          have e : (1 / 2) * (α * lam 0 - 4 / rho) - (α / 4) * lam 0 = α * lam 0 / 4 - (4 / rho) / 2 :=
            by ring
          rw [e]
          linarith [h2rho]
        linarith [hA, hbu, hAB, h3]
      have hg0sq : α ^ 2 * (lam 0) ^ 2 / 64 ≤ (g 0) ^ 2 := by
        have hnn : 0 ≤ α * lam 0 / 8 := by positivity
        have hsq := sq_abs (g 0)
        nlinarith [hfin, hnn, hsq]
      have hPge : (S - lam 0) * (α ^ 2 * (lam 0) ^ 2 / 64) ≤ P := by
        rw [hP]
        refine le_trans (mul_le_mul_of_nonneg_left hg0sq (hfsnn 0)) ?_
        exact Finset.single_le_sum (f := fun i => (S - lam i) * (g i) ^ 2)
          (fun i _ => mul_nonneg (hfsnn i) (sq_nonneg _)) (Finset.mem_univ 0)
      have hcomb_poly : (b / 36) * ((S - lam 0) * (α ^ 2 * (lam 0) ^ 2 / 64)) * rho ^ 2
          ≤ 324 * S := by
        have h1 := mul_le_mul_of_nonneg_left hPge (show (0 : ℝ) ≤ (b / 36) * rho ^ 2 by positivity)
        have e1 : (b / 36) * rho ^ 2 * ((S - lam 0) * (α ^ 2 * (lam 0) ^ 2 / 64))
            = (b / 36) * ((S - lam 0) * (α ^ 2 * (lam 0) ^ 2 / 64)) * rho ^ 2 := by ring
        have e2 : (b / 36) * rho ^ 2 * P = (b / 36) * P * rho ^ 2 := by ring
        rw [e1, e2] at h1
        exact le_trans h1 hkey_poly
      have hk : rho ^ 2 * b * (S - lam 0) * α ^ 2 * (lam 0) ^ 2 ≤ 746496 * S := by
        have h1 := mul_le_mul_of_nonneg_left hcomb_poly (show (0 : ℝ) ≤ 2304 by norm_num)
        have e : 2304 * ((b / 36) * ((S - lam 0) * (α ^ 2 * (lam 0) ^ 2 / 64)) * rho ^ 2)
            = rho ^ 2 * b * (S - lam 0) * α ^ 2 * (lam 0) ^ 2 := by ring
        have e2 : 2304 * (324 * S) = 746496 * S := by ring
        rw [e, e2] at h1
        exact h1
      have hSle : S ≤ 16 * ((S - lam 0) * (lam 0) ^ 2) := by linarith [hf0]
      have hstep1 : rho ^ 2 * b * α ^ 2 * S
          ≤ rho ^ 2 * b * α ^ 2 * (16 * ((S - lam 0) * (lam 0) ^ 2)) :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
      have heq1 : rho ^ 2 * b * α ^ 2 * (16 * ((S - lam 0) * (lam 0) ^ 2))
          = 16 * (rho ^ 2 * b * (S - lam 0) * α ^ 2 * (lam 0) ^ 2) := by ring
      have hstep2 : 16 * (rho ^ 2 * b * (S - lam 0) * α ^ 2 * (lam 0) ^ 2) ≤ 16 * (746496 * S) :=
        mul_le_mul_of_nonneg_left hk (by norm_num)
      have hObjS : rho ^ 2 * b * α ^ 2 * S ≤ 11943936 * S := by
        have h := hstep1
        rw [heq1] at h
        have h2 := le_trans h hstep2
        linarith [h2]
      exact le_of_mul_le_mul_right hObjS hS
    · -- Case B: `α * lam 0 * rho` is small.
      have hlt : α * lam 0 * rho < 16 := lt_of_not_ge hcase
      have hlam0sq : S ^ 2 ≤ 16 * (lam 0) ^ 2 := by
        have h1 : (S / 4) ^ 2 ≤ (lam 0) ^ 2 :=
          (sq_le_sq₀ (by positivity) (le_of_lt hlam0)).2 hlarge
        nlinarith [h1]
      have hpos : 0 ≤ α * lam 0 * rho := by positivity
      have hprod : rho ^ 2 * α ^ 2 * (lam 0) ^ 2 < 256 := by
        have h2 : (α * lam 0 * rho) ^ 2 < 256 := by nlinarith [hlt, hpos]
        nlinarith [h2]
      have hcoef : (0 : ℝ) ≤ rho ^ 2 * α ^ 2 := by positivity
      have hS2b : rho ^ 2 * α ^ 2 * S ^ 2 < 4096 := by
        have h1 : rho ^ 2 * α ^ 2 * S ^ 2 ≤ rho ^ 2 * α ^ 2 * (16 * (lam 0) ^ 2) :=
          mul_le_mul_of_nonneg_left hlam0sq hcoef
        have h2 : rho ^ 2 * α ^ 2 * (16 * (lam 0) ^ 2) = 16 * (rho ^ 2 * α ^ 2 * (lam 0) ^ 2) := by ring
        rw [h2] at h1
        nlinarith [h1, hprod]
      have hbnd : rho ^ 2 * b * α ^ 2 < 4096 := by
        have h1 : rho ^ 2 * b * α ^ 2 ≤ rho ^ 2 * S * α ^ 2 := by
          have := mul_le_mul_of_nonneg_left hbS hcoef
          nlinarith [this]
        have h2 : rho ^ 2 * S * α ^ 2 = rho ^ 2 * α ^ 2 * S ^ 2 / S := by
          rw [eq_div_iff (ne_of_gt hS)]; ring
        have h3 : rho ^ 2 * α ^ 2 * S ^ 2 / S < 4096 / S := div_lt_div_of_pos_right hS2b hS
        have h4 : 4096 / S ≤ 4096 := by
          rw [div_le_iff₀ hS]; nlinarith [hS1]
        calc rho ^ 2 * b * α ^ 2 ≤ rho ^ 2 * S * α ^ 2 := h1
          _ = rho ^ 2 * α ^ 2 * S ^ 2 / S := h2
          _ < 4096 / S := h3
          _ ≤ 4096 := h4
      exact le_trans (le_of_lt hbnd) (by norm_num)
  exact (le_div_iff₀ (pow_pos hα 2)).mpr hObj

end Commons.Analysis.Sigma2