import Mathlib

/-!
# The circle integral of a product of two absolutely convergent Laurent series

The main result of this file, `seriesMulCircleIntegral`, computes

`∮_{|w| = R} (∑_k a_k w^k) (∑_j b_j w^{-j}) dw = 2πi ∑_k a_k b_{k+1}`

for `R > 0` and coefficients with `∑ ‖a_k‖ R^k < ∞` and `∑ ‖b_j‖ / R^j < ∞`.  This is the
residue computation ("only the coefficient of `w⁻¹` of the product survives") underlying the
Laurent/Laurent-expansion manipulations of the repelling-petal part of the proof.

The proof is the standard three-step one:

* the product of the two series is, on the circle, an absolutely convergent double series
  (`tsum_mul_tsum_of_summable_norm`), and integrating term by term is justified by dominated
  convergence for interval integrals (`intervalIntegral.hasSum_integral_of_dominated_convergence`);
* each monomial term integrates to `2πi a_m b_k δ_{k,m+1}`;
* the remaining double series is supported on the graph `m ↦ (m, m+1)`, so it may be reindexed
  along that injection (`hasSum_iff_hasSum_of_ne_zero_bij`).
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology

namespace Work.Repel.Koebe

/-! ### Summability of the diagonal series `∑ a_m b_{m+1}` -/

/-- If `∑ ‖a_m‖ R^m` and `∑ ‖b_k‖ / R^k` converge (`R > 0`), then so does the "diagonal"
series `∑ a_m b_{m+1}`. -/
theorem summable_diagonal_mul {α γ : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hα : Summable (fun m : ℕ => ‖α m‖ * R ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / R ^ k)) :
    Summable (fun m : ℕ => α m * γ (m + 1)) := by
  have hγ' : Summable (fun m : ℕ => ‖γ (m + 1)‖ / R ^ (m + 1)) :=
    hγ.comp_injective (i := fun m : ℕ => m + 1) (fun _ _ h => Nat.succ.inj h)
  have hprod : Summable (fun p : ℕ × ℕ =>
      (‖α p.1‖ * R ^ p.1) * (‖γ (p.2 + 1)‖ / R ^ (p.2 + 1))) :=
    Summable.mul_of_nonneg hα hγ'
      (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hR.le m))
      (fun m => div_nonneg (norm_nonneg _) (pow_nonneg hR.le _))
  have hdiag : Summable (fun m : ℕ => (‖α m‖ * R ^ m) * (‖γ (m + 1)‖ / R ^ (m + 1))) :=
    hprod.comp_injective (i := fun m : ℕ => (m, m)) (fun _ _ h => (Prod.ext_iff.mp h).1)
  have hmain : Summable (fun m : ℕ => ‖α m‖ * ‖γ (m + 1)‖) := by
    have heq : (fun m : ℕ => R * ((‖α m‖ * R ^ m) * (‖γ (m + 1)‖ / R ^ (m + 1))))
        = fun m : ℕ => ‖α m‖ * ‖γ (m + 1)‖ := by
      funext m
      have hRne : R ≠ 0 := ne_of_gt hR
      rw [pow_succ]
      field_simp
    rw [← heq]
    exact hdiag.mul_left R
  have hnorm : (fun m : ℕ => ‖α m * γ (m + 1)‖) = fun m : ℕ => ‖α m‖ * ‖γ (m + 1)‖ := by
    funext m; rw [norm_mul]
  refine Summable.of_norm ?_
  rw [hnorm]
  exact hmain

/-- Reindexing the double series `∑_{m,k} a_m b_k [k = m+1]` along the injection
`m ↦ (m, m+1)` of `ℕ` into `ℕ × ℕ`. -/
theorem hasSum_prod_diagonal' {α γ : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hα : Summable (fun m : ℕ => ‖α m‖ * R ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / R ^ k)) :
    HasSum (fun p : ℕ × ℕ => α p.1 * γ p.2 * (if p.2 = p.1 + 1 then 1 else 0))
      (∑' m : ℕ, α m * γ (m + 1)) := by
  have hG : Summable (fun m : ℕ => α m * γ (m + 1)) := summable_diagonal_mul hR hα hγ
  refine (hasSum_iff_hasSum_of_ne_zero_bij
    (f := fun p : ℕ × ℕ => α p.1 * γ p.2 * (if p.2 = p.1 + 1 then 1 else 0))
    (g := fun m : ℕ => α m * γ (m + 1))
    (a := ∑' m : ℕ, α m * γ (m + 1))
    (i := fun x : Function.support (fun m : ℕ => α m * γ (m + 1)) =>
        (((x : ℕ), (x : ℕ) + 1) : ℕ × ℕ)) ?_ ?_ ?_).mpr hG.hasSum
  · intro x y h
    exact Subtype.ext (by simpa using (Prod.ext_iff.mp h).1 : (x : ℕ) = (y : ℕ))
  · intro p hp
    rw [Function.mem_support] at hp
    have h2 : p.2 = p.1 + 1 := by
      by_contra hc
      exact hp (by simp [hc])
    refine ⟨⟨p.1, ?_⟩, ?_⟩
    · simpa [h2] using hp
    · exact Prod.ext rfl h2.symm
  · intro x
    simp

/-! ### The product of the two summability bounds -/

/-- The product of the two summability bounds is summable with the expected value. -/
theorem summable_bound_prod' {α γ : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hα : Summable (fun m : ℕ => ‖α m‖ * R ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / R ^ k)) :
    Summable (fun p : ℕ × ℕ => R * ((‖α p.1‖ * R ^ p.1) * (‖γ p.2‖ / R ^ p.2)))
      ∧ (∑' p : ℕ × ℕ, R * ((‖α p.1‖ * R ^ p.1) * (‖γ p.2‖ / R ^ p.2)))
        = R * ((∑' m : ℕ, ‖α m‖ * R ^ m) * (∑' k : ℕ, ‖γ k‖ / R ^ k)) := by
  have hF : 0 ≤ fun m : ℕ => ‖α m‖ * R ^ m :=
    fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hR.le m)
  have hG : 0 ≤ fun k : ℕ => ‖γ k‖ / R ^ k :=
    fun k => div_nonneg (norm_nonneg _) (pow_nonneg hR.le k)
  have hprod : Summable (fun p : ℕ × ℕ => (‖α p.1‖ * R ^ p.1) * (‖γ p.2‖ / R ^ p.2)) :=
    Summable.mul_of_nonneg hα hγ hF hG
  refine ⟨hprod.mul_left R, ?_⟩
  rw [tsum_mul_left, Summable.tsum_mul_tsum hα hγ hprod]

/-! ### The circle integral of a product of two monomials -/

/-- **Circle integral of a product of two monomials.**  For `R > 0` and complex `a b`,
`∮_{|z|=R} (a z^m) (b / z^k) dz = 2πi · a b · [k = m + 1]`. -/
theorem monomial_mul_circleIntegral {R : ℝ} (hR : 0 < R) (a b : ℂ) (m k : ℕ) :
    circleIntegral (fun z : ℂ => (a * z ^ m) * (b / z ^ k)) 0 R
      = 2 * (Real.pi : ℂ) * Complex.I * (a * b * (if k = m + 1 then 1 else 0)) := by
  have hcongr : circleIntegral (fun z : ℂ => (a * z ^ m) * (b / z ^ k)) 0 R
      = circleIntegral (fun z : ℂ => a * b * (z - 0) ^ ((m : ℤ) - (k : ℤ))) 0 R := by
    refine circleIntegral.integral_congr hR.le (fun z hz => ?_)
    have hz0 : z ≠ 0 := by
      have h1 : ‖z‖ = R := by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        exact hz
      intro h; rw [h, norm_zero] at h1; linarith
    rw [sub_zero, zpow_sub₀ hz0, zpow_natCast, zpow_natCast]
    ring
  rw [hcongr, circleIntegral.integral_const_mul]
  by_cases hk : k = m + 1
  · have hn : ((m : ℤ) - (k : ℤ)) = -1 := by
      subst hk; push_cast; ring
    rw [hn, ite_eq_left hk]
    have hsub : circleIntegral (fun z : ℂ => (z - 0) ^ (-1 : ℤ)) 0 R
        = 2 * (Real.pi : ℂ) * Complex.I := by
      simp only [zpow_neg_one]
      rw [circleIntegral.integral_sub_center_inv 0 hR.ne']
    rw [hsub]; ring
  · have hn : ((m : ℤ) - (k : ℤ)) ≠ -1 := by
      intro h; exact hk (by omega)
    rw [ite_eq_right hk]
    have hzero : circleIntegral (fun z : ℂ => (z - 0) ^ ((m : ℤ) - (k : ℤ))) 0 R = 0 :=
      circleIntegral.integral_sub_zpow_of_ne hn 0 0 R
    rw [hzero]; ring

/-! ### Term-by-term integration of the double series -/

private def integrand (α γ : ℕ → ℂ) (R : ℝ) (p : ℕ × ℕ) (θ : ℝ) : ℂ :=
  deriv (circleMap 0 R) θ • ((α p.1 * (circleMap 0 R θ) ^ p.1) * (γ p.2 / (circleMap 0 R θ) ^ p.2))

private def intlimit (α γ : ℕ → ℂ) (R : ℝ) (θ : ℝ) : ℂ :=
  deriv (circleMap 0 R) θ •
    ((∑' m : ℕ, α m * (circleMap 0 R θ) ^ m) * (∑' k : ℕ, γ k / (circleMap 0 R θ) ^ k))

private def intbound (α γ : ℕ → ℂ) (R : ℝ) (p : ℕ × ℕ) : ℝ :=
  R * (‖α p.1‖ * R ^ p.1 * (‖γ p.2‖ / R ^ p.2))

/-- The circle integrals of the monomial terms sum to the circle integral of the product of the
two series (dominated convergence for the interval integral over `[0, 2π]`). -/
theorem circleIntegral_tsum_mul_tsum_hasSum' {α γ : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hα : Summable (fun m : ℕ => ‖α m‖ * R ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / R ^ k)) :
    HasSum (fun p : ℕ × ℕ =>
      circleIntegral (fun z : ℂ => (α p.1 * z ^ p.1) * (γ p.2 / z ^ p.2)) 0 R)
      (circleIntegral (fun z : ℂ => (∑' m : ℕ, α m * z ^ m) * (∑' k : ℕ, γ k / z ^ k)) 0 R) := by
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun (n : ℕ × ℕ) (θ : ℝ) => integrand α γ R n θ)
    (f := fun (θ : ℝ) => intlimit α γ R θ)
    (bound := fun (p : ℕ × ℕ) (_ : ℝ) => intbound α γ R p)
    ?_ ?_ ?_ ?_ ?_
  · intro p
    simp only [integrand]
    apply Continuous.aestronglyMeasurable
    have hcw : Continuous fun θ : ℝ => circleMap 0 R θ := continuous_circleMap 0 R
    have hd : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ := by
      rw [show (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I
            from funext (fun θ => deriv_circleMap 0 R θ)]
      exact hcw.mul continuous_const
    have hw0 : ∀ θ : ℝ, (circleMap 0 R θ) ^ p.2 ≠ 0 := fun θ =>
      pow_ne_zero _ (by
        intro hz
        have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
        rw [hz, norm_zero] at h1
        exact hR.ne' h1.symm)
    exact hd.smul (((hcw.pow p.1).const_mul (α p.1)).mul
      (continuous_const.div (hcw.pow p.2) hw0))
  · intro p
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    simp only [integrand, intbound]
    have hw : ‖circleMap 0 R t‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    have hd : ‖deriv (circleMap 0 R) t‖ = R := by
      rw [deriv_circleMap, norm_mul, hw, Complex.norm_I, mul_one]
    have hX : ‖(α p.1 * (circleMap 0 R t) ^ p.1) * (γ p.2 / (circleMap 0 R t) ^ p.2)‖
        = ‖α p.1‖ * R ^ p.1 * (‖γ p.2‖ / R ^ p.2) := by
      rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, hw]
    rw [norm_smul, hd, hX]
  · exact Filter.Eventually.of_forall (fun _ _ => by
      simp only [intbound]
      exact (summable_bound_prod' hR hα hγ).1)
  · simp only [intbound]
    rw [show (fun t : ℝ => ∑' n : ℕ × ℕ, R * (‖α n.1‖ * R ^ n.1 * (‖γ n.2‖ / R ^ n.2)))
          = fun _ => R * ((∑' m, ‖α m‖ * R ^ m) * (∑' k, ‖γ k‖ / R ^ k))
          from funext (fun _ => (summable_bound_prod' hR hα hγ).2)]
    exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun t _ => ?_)
    simp only [integrand, intlimit]
    have hwn : ‖circleMap 0 R t‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    have hα' : Summable (fun m : ℕ => ‖α m * (circleMap 0 R t) ^ m‖) := by
      simpa only [norm_mul, norm_pow, hwn] using hα
    have hγ' : Summable (fun k : ℕ => ‖γ k / (circleMap 0 R t) ^ k‖) := by
      simpa only [norm_div, norm_pow, hwn] using hγ
    have hprod : Summable (fun p : ℕ × ℕ =>
        (α p.1 * (circleMap 0 R t) ^ p.1) * (γ p.2 / (circleMap 0 R t) ^ p.2)) :=
      summable_mul_of_summable_norm (f := fun m : ℕ => α m * (circleMap 0 R t) ^ m)
        (g := fun k : ℕ => γ k / (circleMap 0 R t) ^ k) hα' hγ'
    have hsumprod : (∑' m : ℕ, α m * (circleMap 0 R t) ^ m) *
          (∑' k : ℕ, γ k / (circleMap 0 R t) ^ k)
        = ∑' p : ℕ × ℕ, (α p.1 * (circleMap 0 R t) ^ p.1) * (γ p.2 / (circleMap 0 R t) ^ p.2) :=
      tsum_mul_tsum_of_summable_norm (f := fun m : ℕ => α m * (circleMap 0 R t) ^ m)
        (g := fun k : ℕ => γ k / (circleMap 0 R t) ^ k) hα' hγ'
    have hHas : HasSum (fun p : ℕ × ℕ =>
        (α p.1 * (circleMap 0 R t) ^ p.1) * (γ p.2 / (circleMap 0 R t) ^ p.2))
        ((∑' m : ℕ, α m * (circleMap 0 R t) ^ m) * (∑' k : ℕ, γ k / (circleMap 0 R t) ^ k)) := by
      rw [hsumprod]
      exact hprod.hasSum
    have hml := hHas.mul_left (deriv (circleMap 0 R) t)
    simpa only [smul_eq_mul] using hml

/-- The circle integral of a product of two Laurent series only sees the coefficient of `z⁻¹`. -/
theorem circleIntegral_tsum_mul_tsum_div' {α γ : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hα : Summable (fun m : ℕ => ‖α m‖ * R ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / R ^ k)) :
    circleIntegral (fun z : ℂ => (∑' m : ℕ, α m * z ^ m) * (∑' k : ℕ, γ k / z ^ k)) 0 R
      = 2 * (Real.pi : ℂ) * Complex.I * (∑' m : ℕ, α m * γ (m + 1)) := by
  have hmain := circleIntegral_tsum_mul_tsum_hasSum' hR hα hγ
  have hterm : ∀ p : ℕ × ℕ,
      circleIntegral (fun z : ℂ => (α p.1 * z ^ p.1) * (γ p.2 / z ^ p.2)) 0 R
      = 2 * (Real.pi : ℂ) * Complex.I * (α p.1 * γ p.2 * (if p.2 = p.1 + 1 then 1 else 0)) :=
    fun p => monomial_mul_circleIntegral hR _ _ _ _
  have hG : HasSum (fun p : ℕ × ℕ => α p.1 * γ p.2 * (if p.2 = p.1 + 1 then 1 else 0))
      (∑' m : ℕ, α m * γ (m + 1)) := hasSum_prod_diagonal' hR hα hγ
  have h2 : HasSum (fun p : ℕ × ℕ => 2 * (Real.pi : ℂ) * Complex.I *
      (α p.1 * γ p.2 * (if p.2 = p.1 + 1 then 1 else 0)))
      (2 * (Real.pi : ℂ) * Complex.I * (∑' m : ℕ, α m * γ (m + 1))) := hG.mul_left _
  exact (hmain.congr_fun (fun p => (hterm p).symm)).unique h2

/-! ### The requested statement -/

theorem seriesMulCircleIntegral {a b : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : Summable (fun k : ℕ => ‖a k‖ * R ^ k))
    (hb : Summable (fun j : ℕ => ‖b j‖ / R ^ j)) :
    circleIntegral (fun w : ℂ => (∑' k : ℕ, a k * w ^ k) * (∑' j : ℕ, b j * w ^ (-(j : ℤ)))) 0 R
      = 2 * (Real.pi : ℂ) * Complex.I * (∑' k : ℕ, a k * b (k + 1)) := by
  have hcongr : circleIntegral (fun w : ℂ =>
        (∑' k : ℕ, a k * w ^ k) * (∑' j : ℕ, b j * w ^ (-(j : ℤ)))) 0 R
      = circleIntegral (fun w : ℂ =>
        (∑' k : ℕ, a k * w ^ k) * (∑' j : ℕ, b j / w ^ j)) 0 R := by
    refine circleIntegral.integral_congr hR.le (fun z _ => ?_)
    have h2 : (∑' j : ℕ, b j * z ^ (-(j : ℤ))) = ∑' j : ℕ, b j / z ^ j :=
      tsum_congr (fun j => by rw [zpow_neg, zpow_natCast, div_eq_mul_inv])
    rw [h2]
  rw [hcongr]
  exact circleIntegral_tsum_mul_tsum_div' hR ha hb

end Work.Repel.Koebe
