import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open Complex

namespace Work.ZeroFreeTables.Rep9

/-- The norm of a real number seen in `ℂ`. -/
private lemma norm_ofReal3 (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x

/-- `‖P₃ w‖ ≤ (8/3)‖w‖` for `‖w‖ ≤ 1`. -/
private lemma P3_norm_le_of_norm_le_one3 (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖Work.ZeroFreeTables.P3 w‖ ≤ (8/3) * ‖w‖ := by
  have hcoef : (2/3 : ℂ) = (((2:ℝ)/3 : ℝ) : ℂ) := by norm_num
  have hsum : ‖Work.ZeroFreeTables.P3 w‖
      ≤ ‖w + w^2‖ + ‖(((2:ℝ)/3 : ℝ) : ℂ) * w^3‖ := by
    rw [Work.ZeroFreeTables.P3, hcoef]
    exact norm_add_le _ _
  have hsum2 : ‖w + w^2‖ ≤ ‖w‖ + ‖w^2‖ := norm_add_le _ _
  have hcoef2 : ‖(((2:ℝ)/3 : ℝ) : ℂ) * w^3‖ = (2/3) * ‖w^3‖ := by
    rw [norm_mul, norm_ofReal3, abs_of_pos (by norm_num : (0:ℝ) < 2/3)]
  have hw2 : ‖w^2‖ = ‖w‖^2 := norm_pow w 2
  have hw3 : ‖w^3‖ = ‖w‖^3 := norm_pow w 3
  have h1 : ‖Work.ZeroFreeTables.P3 w‖ ≤ ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := by
    rw [hcoef2, hw3] at hsum
    linarith
  have h2 : 1 + ‖w‖ + (2/3) * ‖w‖^2 ≤ 8/3 := by
    nlinarith [norm_nonneg w, hw, sq_nonneg (‖w‖)]
  have h3 : ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 = ‖w‖ * (1 + ‖w‖ + (2/3) * ‖w‖^2) := by ring
  calc ‖Work.ZeroFreeTables.P3 w‖ ≤ ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := h1
    _ = ‖w‖ * (1 + ‖w‖ + (2/3) * ‖w‖^2) := h3
    _ ≤ ‖w‖ * (8/3) := mul_le_mul_of_nonneg_left h2 (norm_nonneg w)
    _ = (8/3) * ‖w‖ := by ring

/-- `1 + 2i·Im ρ - conj ρ = (1 - Re ρ) + 3i·Im ρ`. -/
private lemma norm_conj_eq3 (ρ : ℂ) :
    (1 : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ
      = (((1 - ρ.re : ℝ)) : ℂ) + ((3 * ρ.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> ring

/-- The core norm bound of the "far" case for the order-3 point: if `0 ≤ lam ≤ M`, `L ≥ 2M/δ` and
`δ² < lam²/L² + 9γ²`, then the quotient `(a+lam)/(a + 3iγL)` has norm at most `2(a+M)/(δL)`. -/
private lemma farNormBound3 {a δ M L lam γ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hL : 0 < L) (hlam0 : 0 ≤ lam) (hlamM : lam ≤ M) (hLM : 2 * M / δ ≤ L)
    (hfar : δ ^ 2 < lam ^ 2 / L ^ 2 + 9 * γ ^ 2) :
    ‖((a + lam : ℝ) : ℂ) / ((a : ℂ) + ((3 * γ * L : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 * (a + M) / (δ * L) := by
  have hδL : 0 < δ * L := mul_pos hδ hL
  have hMsq : M ^ 2 / L ^ 2 ≤ δ ^ 2 / 4 := by
    have hML : M / L ≤ δ / 2 := by
      have h := (div_le_iff₀ hδ).mp hLM
      rw [div_le_iff₀ hL]
      linarith
    have h1 : (M / L) ^ 2 ≤ (δ / 2) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (div_nonneg hM hL.le),
        abs_of_pos (by linarith : (0:ℝ) < δ / 2)]
      exact hML
    have h2 : (M / L) ^ 2 = M ^ 2 / L ^ 2 := by rw [div_pow]
    have h3 : (δ / 2) ^ 2 = δ ^ 2 / 4 := by ring
    linarith
  have h9g : δ ^ 2 / 4 < 9 * γ ^ 2 := by
    have h2 : lam ^ 2 / L ^ 2 ≤ M ^ 2 / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ L ^ 2)
      nlinarith
    nlinarith [hfar, h2, hMsq, hδ]
  have h2g : (δ / 2) ^ 2 < (3 * γ) ^ 2 := by
    have h : (3 * γ) ^ 2 = 9 * γ ^ 2 := by ring
    linarith
  have hden : δ * L / 2 < ‖(a : ℂ) + ((3 * γ * L : ℝ) : ℂ) * Complex.I‖ := by
    rw [Complex.norm_def, Real.lt_sqrt (by positivity : (0:ℝ) ≤ δ * L / 2)]
    rw [Complex.normSq_add_mul_I]
    have hsq2 : (3 * γ * L) ^ 2 = (3 * γ) ^ 2 * L ^ 2 := by ring
    rw [hsq2]
    have hlt : (δ / 2) ^ 2 * L ^ 2 < (3 * γ) ^ 2 * L ^ 2 :=
      mul_lt_mul_of_pos_right h2g (by positivity : (0:ℝ) < L ^ 2)
    nlinarith [hlt, sq_nonneg a]
  rw [norm_div, norm_ofReal3, abs_of_nonneg (by linarith : (0:ℝ) ≤ a + lam)]
  have hDpos : 0 < ‖(a : ℂ) + ((3 * γ * L : ℝ) : ℂ) * Complex.I‖ := by linarith [hden, hδL]
  rw [div_le_iff₀ hDpos, div_mul_eq_mul_div, le_div_iff₀ hδL]
  nlinarith [hden, hlam0, hlamM, ha, hδ, hL, hM]

/-- The `P₃`-value at the far point is at most `e` once `L` dominates the three
thresholds coming from the bound `B`. -/
private lemma P3_bound_of_far3 {a M δ e L : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hL : 0 < L) (hM : 0 ≤ M) (he : 0 < e) {lam γ : ℝ} (hlam0 : 0 ≤ lam) (hlamM : lam ≤ M)
    (hLM : 2 * M / δ ≤ L) (hLM2 : 2 * (a + M) / δ ≤ L)
    (hLM3 : 16 * (a + M) / (3 * δ * e) ≤ L)
    (hfar : δ ^ 2 < lam ^ 2 / L ^ 2 + 9 * γ ^ 2) :
    (Work.ZeroFreeTables.P3
        (((a + lam : ℝ) : ℂ) / ((a : ℂ) + ((3 * γ * L : ℝ) : ℂ) * Complex.I))).re ≤ e := by
  set Z : ℂ := ((a + lam : ℝ) : ℂ) / ((a : ℂ) + ((3 * γ * L : ℝ) : ℂ) * Complex.I) with hZ
  have hnorm : ‖Z‖ ≤ 2 * (a + M) / (δ * L) := farNormBound3 ha hδ hM hL hlam0 hlamM hLM hfar
  have hXle1 : ‖Z‖ ≤ 1 := by
    have h1 : 2 * (a + M) / (δ * L) ≤ 1 := by
      rw [div_le_one (mul_pos hδ hL)]
      have h := (div_le_iff₀ hδ).mp hLM2
      linarith
    linarith [hnorm, h1]
  have hP3 : ‖Work.ZeroFreeTables.P3 Z‖ ≤ (8/3) * ‖Z‖ := P3_norm_le_of_norm_le_one3 Z hXle1
  have hmid : (8/3) * ‖Z‖ ≤ 16 * (a + M) / (3 * δ * L) := by
    have h1 := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ) ≤ 8/3)
    have h2 : (8/3) * (2 * (a + M) / (δ * L)) = 16 * (a + M) / (3 * δ * L) := by ring
    linarith [h1, h2]
  have hee : 16 * (a + M) / (3 * δ * L) ≤ e := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * δ * L)]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 3 * δ * e)).mp hLM3
    nlinarith [h]
  calc (Work.ZeroFreeTables.P3 Z).re ≤ ‖Work.ZeroFreeTables.P3 Z‖ := Complex.re_le_norm _
    _ ≤ (8/3) * ‖Z‖ := hP3
    _ ≤ 16 * (a + M) / (3 * δ * L) := hmid
    _ ≤ e := hee

theorem order3_extraM_far {a δ e M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (he : 0 < e) (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ (ρ₁ : ℂ),
      0 ≤ Work.LinnikContract.lamOf q ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ →
      Work.LinnikContract.lamOf q ρ₁ ≤ M →
      ¬ (‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ) →
      (Work.ZeroFreeTables.P3
          (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
            / ((a : ℂ) + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re ≤ e := by
  set B : ℝ := 2 * M / δ + 2 * (a + M) / δ + 16 * (a + M) / (3 * δ * e) + 1 with hB
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt (max 2 (Real.exp B))
  refine ⟨q₀, ?_⟩
  intro q hqq ρ₁ hlam0 hδL hlamM hfar
  have hq2 : 2 ≤ q := by
    have h2q0 : (2 : ℝ) < (q₀ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq₀
    have h2 : 2 < q₀ := by exact_mod_cast h2q0
    omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hexp_le : Real.exp B ≤ (q : ℝ) := by
    have h1 : Real.exp B ≤ max 2 (Real.exp B) := le_max_right _ _
    have h2 : (q₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqq
    linarith
  have hBle : B ≤ Real.log (q : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith : (0:ℝ) < (q:ℝ))).mpr hexp_le
  have ht1 : 2 * M / δ ≤ Real.log (q : ℝ) := by
    have h2 : 0 ≤ 2 * (a + M) / δ := by positivity
    have h3 : 0 ≤ 16 * (a + M) / (3 * δ * e) := by positivity
    linarith [hBle, hB, h2, h3]
  have ht2 : 2 * (a + M) / δ ≤ Real.log (q : ℝ) := by
    have h1 : 0 ≤ 2 * M / δ := by positivity
    have h3 : 0 ≤ 16 * (a + M) / (3 * δ * e) := by positivity
    linarith [hBle, hB, h1, h3]
  have ht3 : 16 * (a + M) / (3 * δ * e) ≤ Real.log (q : ℝ) := by
    have h1 : 0 ≤ 2 * M / δ := by positivity
    have h2 : 0 ≤ 2 * (a + M) / δ := by positivity
    linarith [hBle, hB, h1, h2]
  have hrel : (1 - ρ₁.re) * Real.log (q : ℝ) = Work.LinnikContract.lamOf q ρ₁ := by
    rw [Work.LinnikContract.lamOf]
  have hlogq : Real.log (q : ℝ) ≠ 0 := ne_of_gt hLpos
  have hfar2 : δ ^ 2 < Work.LinnikContract.lamOf q ρ₁ ^ 2 / (Real.log (q:ℝ)) ^ 2
      + 9 * ρ₁.im ^ 2 := by
    have hδlt : δ < ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ :=
      not_le.mp hfar
    have hSsq : ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ^ 2
        = (1 - ρ₁.re) ^ 2 + (3 * ρ₁.im) ^ 2 := by
      rw [Complex.sq_norm, norm_conj_eq3, Complex.normSq_add_mul_I]
    have h1 : δ ^ 2 < (1 - ρ₁.re) ^ 2 + (3 * ρ₁.im) ^ 2 := by
      nlinarith [hδlt, hSsq,
        norm_nonneg ((1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁), hδ]
    have h2 : (1 - ρ₁.re) ^ 2 = Work.LinnikContract.lamOf q ρ₁ ^ 2 / (Real.log (q:ℝ)) ^ 2 := by
      have h3 : (1 - ρ₁.re) = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
        rw [eq_div_iff hlogq]
        exact hrel
      rw [h3, div_pow]
    have h4 : (3 * ρ₁.im) ^ 2 = 9 * ρ₁.im ^ 2 := by ring
    rw [h2, h4] at h1
    exact h1
  rw [← Complex.ofReal_add]
  exact P3_bound_of_far3 ha hδ hLpos hM he hlam0 hlamM ht1 ht2 ht3 hfar2

end Work.ZeroFreeTables.Rep9
