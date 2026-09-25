import Mathlib
import Submission.Work.IonescuWainger.tsum_inv_one_add_sq_mul_le
import Submission.Work.BourgainPlan.IonescuWainger.int_summable_rpow_inv_two

/-!
# The weighted `ℓ²`-mass of rapidly decaying kernels

This file supplies the second weight-norm constant of the `p = ∞` endpoint of Tao's
`ortho-apply`(ii) (arXiv:2008.05066, §4): for a sequence whose Fourier coefficients decay as
`‖K m‖ ≤ C ε (1 + (εQm)²)^{-3/2}`, the weighted lattice sum
`Σ_m ‖(1 + ε²(Qm)²)·K m‖²` is at most `4 C² ε Q`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- Elementary pointwise estimate: if `u ≥ 1` and `‖z‖ ≤ C ε u^{-3/2}` then
`(u‖z‖)² ≤ C²ε²u⁻¹`. -/
private lemma sq_norm_le_of_decay {u C ε : ℝ} (hu : 1 ≤ u) {z : ℂ}
    (hz : ‖z‖ ≤ C * ε / u ^ ((3:ℝ)/2)) :
    (u * ‖z‖) ^ 2 ≤ C ^ 2 * ε ^ 2 * u⁻¹ := by
  have hupos : 0 < u := lt_of_lt_of_le one_pos hu
  have hsq : u ^ ((3:ℝ)/2) = u * Real.sqrt u := by
    rw [show ((3:ℝ)/2) = (1:ℝ) + 1/2 by norm_num, Real.rpow_add hupos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  have h1 : u * ‖z‖ ≤ C * ε * (Real.sqrt u)⁻¹ := by
    calc u * ‖z‖ ≤ u * (C * ε / u ^ ((3:ℝ)/2)) := mul_le_mul_of_nonneg_left hz hupos.le
      _ = C * ε * (Real.sqrt u)⁻¹ := by
          rw [hsq]
          field_simp
  calc (u * ‖z‖) ^ 2 ≤ (C * ε * (Real.sqrt u)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ = C ^ 2 * ε ^ 2 * u⁻¹ := by
        rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hupos.le]

/-- **The second weight-norm constant of the `p = ∞` endpoint of Tao's `ortho-apply`(ii).**
For `ε > 0`, `Q ≥ 1` with `εQ ≤ 1/2` and a kernel sequence decaying as
`‖K m‖ ≤ C ε (1 + (εQm)²)^{-3/2}`, the weighted `ℓ²`-mass of `K` over the lattice is at most
`8 C² ε Q`.  The summand is `(1 + (εQm)²)²‖K m‖² ≤ C²ε²/(1 + (εQm)²)`, so the claim reduces to
`Σ_m (1 + (εQm)²)⁻¹ ≤ 8Q²`, which follows from the lattice-sum bound
`Work.IonescuWainger.tsum_inv_one_add_sq_mul_le` (`≤ 1 + π/(εQ)`) together with `εQ ≤ 1/2` and
`Q ≥ 1`. -/
theorem tsum_weighted_kernel_sq_le_half {K : ℤ → ℂ} {ε Q C : ℝ} (hε : 0 < ε) (hQ : 1 ≤ Q)
    (_hC : 0 ≤ C) (hεQ : ε * Q ≤ 1 / 2)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * Q * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2)) :
    ∑' m : ℤ, ‖(1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m‖ ^ 2
      ≤ 8 * C ^ 2 * ε * Q := by
  set a : ℝ := ε * Q with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  -- the pointwise bound by `C²ε²/(1 + (a m)²)`
  have hpt : ∀ m : ℤ,
      ‖(1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m‖ ^ 2
        ≤ C ^ 2 * ε ^ 2 * (1 + (a * (m : ℝ)) ^ 2)⁻¹ := by
    intro m
    set u : ℝ := 1 + (a * (m : ℝ)) ^ 2 with hu
    have hu1 : 1 ≤ u := by rw [hu]; linarith [sq_nonneg (a * (m : ℝ))]
    have hupos : 0 < u := lt_of_lt_of_le one_pos hu1
    have hz : (1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2 = ((u : ℝ) : ℂ) := by
      rw [hu, ha]; push_cast; ring
    have hnorm : ‖((u : ℝ) : ℂ)‖ = u := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (le_of_lt hupos)]
    have hdec : ‖K m‖ ≤ C * ε / u ^ ((3:ℝ)/2) := by
      have h := hdecay m
      rw [hu]
      exact h
    rw [hz, norm_mul, hnorm]
    have hsq2 := sq_norm_le_of_decay hu1 hdec
    rw [hu] at hsq2
    exact hsq2
  -- the lattice sum bound
  have hsum : ∑' m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹ ≤ 1 + Real.pi / a := by
    have h := Work.IonescuWainger.tsum_inv_one_add_sq_mul_le (ε := a) (Q := 1) hapos one_pos
    simpa using h
  -- summability of that lattice sum, by comparison with `(1 + |a m|)^{-2}`
  have hM : Summable fun m : ℤ => (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) :=
    int_summable_rpow_inv_two a hapos
  have hcmp : ∀ m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹
      ≤ 2 * (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) := by
    intro m
    set s : ℝ := a * (m : ℝ) with hs
    have hs1 : 0 < 1 + |s| := by positivity
    have hsq : (1 + |s|) ^ 2 ≤ 2 * (1 + s ^ 2) := by
      nlinarith [abs_nonneg s, sq_abs s, sq_nonneg (|s| - 1)]
    have h3 : (1 + s ^ 2)⁻¹ ≤ 2 * ((1 + |s|) ^ 2)⁻¹ := by
      have h2 : (2 * (1 + s ^ 2))⁻¹ ≤ ((1 + |s|) ^ 2)⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le (by positivity : (0:ℝ) < (1 + |s|) ^ 2) hsq
      rw [mul_inv] at h2
      nlinarith [h2, inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 1 + s ^ 2)]
    rw [Real.rpow_neg (le_of_lt hs1), Real.rpow_two]
    exact h3
  have hsummable_inv : Summable fun m : ℤ => (1 + (a * (m : ℝ)) ^ 2)⁻¹ :=
    Summable.of_nonneg_of_le (fun m => by positivity) hcmp (hM.mul_left 2)
  -- the weighted sum is summable and dominated by the lattice sum
  have hG : Summable fun m : ℤ =>
      ‖(1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun m => by positivity) hpt
      (hsummable_inv.mul_left (C ^ 2 * ε ^ 2))
  have hle := Summable.tsum_le_tsum hpt hG (hsummable_inv.mul_left (C ^ 2 * ε ^ 2))
  rw [tsum_mul_left] at hle
  -- the algebraic conclusion `C²ε²(1 + π/a) ≤ 4C²εQ`
  have hεle : ε ≤ 1 / (2 * Q) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Q)]
    linarith
  have hkey : ε + Real.pi / Q ≤ 8 * Q := by
    have h2 : (1 : ℝ) / (2 * Q) + Real.pi / Q ≤ 8 * Q := by
      have h3 : (1 : ℝ) / (2 * Q) = (1 / 2 : ℝ) / Q := by field_simp
      rw [h3, ← add_div, div_le_iff₀ hQpos]
      have hQQ : (1 : ℝ) ≤ Q * Q := by nlinarith
      nlinarith [Real.pi_lt_four, hQQ]
    linarith
  have hfinal : C ^ 2 * ε ^ 2 * (1 + Real.pi / a) ≤ 8 * C ^ 2 * ε * Q := by
    have hεa : ε * (1 + Real.pi / a) = ε + Real.pi / Q := by
      rw [ha]; field_simp
    calc C ^ 2 * ε ^ 2 * (1 + Real.pi / a)
        = (C ^ 2 * ε) * (ε * (1 + Real.pi / a)) := by ring
      _ = (C ^ 2 * ε) * (ε + Real.pi / Q) := by rw [hεa]
      _ ≤ (C ^ 2 * ε) * (8 * Q) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 8 * C ^ 2 * ε * Q := by ring
  refine hle.trans ?_
  calc C ^ 2 * ε ^ 2 * ∑' m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹
      ≤ C ^ 2 * ε ^ 2 * (1 + Real.pi / a) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 8 * C ^ 2 * ε * Q := hfinal

/-- **The second weight-norm constant, in the form needed downstream**: the *torsion kernel*
`n ↦ Q · K(Qm)` of the shifted torsion arc carries an extra factor `Q`, and the sharp estimate for
`Σ_m ‖Q(1 + ε²Q²m²)K(Qm)‖²` is again `8 C² ε Q` (the `Q²` of the factor is absorbed by
`ε²Q² ≤ εQ`, valid because `εQ ≤ 1`).  This is exactly the `hC₂` hypothesis of
`opArc_sup_torsion_family`. -/
theorem tsum_weighted_kernel_sq_le_half_mul {K : ℤ → ℂ} {ε Q C : ℝ} (hε : 0 < ε) (hQ : 1 ≤ Q)
    (hεQ : ε * Q ≤ 1 / 2)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * Q * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2)) :
    ∑' m : ℤ, ‖(Q : ℂ) * ((1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m)‖ ^ 2
      ≤ 8 * C ^ 2 * ε * Q := by
  set a : ℝ := ε * Q with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hQQ : (0 : ℝ) < (Q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hpt : ∀ m : ℤ,
      ‖(1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m‖ ^ 2
        ≤ C ^ 2 * ε ^ 2 * (1 + (a * (m : ℝ)) ^ 2)⁻¹ := by
    intro m
    set u : ℝ := 1 + (a * (m : ℝ)) ^ 2 with hu
    have hu1 : 1 ≤ u := by rw [hu]; linarith [sq_nonneg (a * (m : ℝ))]
    have hupos : 0 < u := lt_of_lt_of_le one_pos hu1
    have hz : (1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2 = ((u : ℝ) : ℂ) := by
      rw [hu, ha]; push_cast; ring
    have hnorm : ‖((u : ℝ) : ℂ)‖ = u := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (le_of_lt hupos)]
    have hdec : ‖K m‖ ≤ C * ε / u ^ ((3:ℝ)/2) := by
      have h := hdecay m
      rw [hu]
      exact h
    rw [hz, norm_mul, hnorm]
    have hsq2 := sq_norm_le_of_decay hu1 hdec
    rw [hu] at hsq2
    exact hsq2
  have hsum : ∑' m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹ ≤ 1 + Real.pi / a := by
    have h := Work.IonescuWainger.tsum_inv_one_add_sq_mul_le (ε := a) (Q := 1) hapos one_pos
    simpa using h
  have hM : Summable fun m : ℤ => (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) :=
    int_summable_rpow_inv_two a hapos
  have hcmp : ∀ m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹
      ≤ 2 * (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) := by
    intro m
    set s : ℝ := a * (m : ℝ) with hs
    have hs1 : 0 < 1 + |s| := by positivity
    have hsq : (1 + |s|) ^ 2 ≤ 2 * (1 + s ^ 2) := by
      nlinarith [abs_nonneg s, sq_abs s, sq_nonneg (|s| - 1)]
    have h3 : (1 + s ^ 2)⁻¹ ≤ 2 * ((1 + |s|) ^ 2)⁻¹ := by
      have h2 : (2 * (1 + s ^ 2))⁻¹ ≤ ((1 + |s|) ^ 2)⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le (by positivity : (0:ℝ) < (1 + |s|) ^ 2) hsq
      rw [mul_inv] at h2
      nlinarith [h2, inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 1 + s ^ 2)]
    rw [Real.rpow_neg (le_of_lt hs1), Real.rpow_two]
    exact h3
  have hsummable_inv : Summable fun m : ℤ => (1 + (a * (m : ℝ)) ^ 2)⁻¹ :=
    Summable.of_nonneg_of_le (fun m => by positivity) hcmp (hM.mul_left 2)
  have hptQ : ∀ m : ℤ,
      ‖(Q : ℂ) * ((1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m)‖ ^ 2
        ≤ Q ^ 2 * (C ^ 2 * ε ^ 2) * (1 + (a * (m : ℝ)) ^ 2)⁻¹ := by
    intro m
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQQ]
    have h1 := hpt m
    nlinarith [h1, sq_nonneg (Q : ℝ)]
  have hG : Summable fun m : ℤ =>
      ‖(Q : ℂ) * ((1 + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2) * K m)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun m => by positivity) hptQ
      (hsummable_inv.mul_left (Q ^ 2 * (C ^ 2 * ε ^ 2)))
  have hle := Summable.tsum_le_tsum hptQ hG (hsummable_inv.mul_left (Q ^ 2 * (C ^ 2 * ε ^ 2)))
  rw [tsum_mul_left] at hle
  refine hle.trans ?_
  have hkey : Q ^ 2 * ε ^ 2 * (1 + Real.pi / a) ≤ 8 * ε * Q := by
    have hεQ' : ε * Q ≤ 1 := by linarith
    have h1 : ε ^ 2 * Q ^ 2 ≤ ε * Q := by
      nlinarith [hεQ', mul_nonneg hε.le hQQ.le]
    have h3 : ε ^ 2 * Q ^ 2 * (Real.pi / a) = Real.pi * ε * Q := by
      rw [ha]
      field_simp
    have h4 : Q ^ 2 * ε ^ 2 * (1 + Real.pi / a)
        = ε ^ 2 * Q ^ 2 + Real.pi * ε * Q := by
      have h4a : Q ^ 2 * ε ^ 2 * (1 + Real.pi / a)
          = ε ^ 2 * Q ^ 2 + ε ^ 2 * Q ^ 2 * (Real.pi / a) := by ring
      rw [h4a, h3]
    rw [h4]
    nlinarith [h1, Real.pi_lt_four, mul_nonneg hε.le hQQ.le]
  calc Q ^ 2 * (C ^ 2 * ε ^ 2) * ∑' m : ℤ, (1 + (a * (m : ℝ)) ^ 2)⁻¹
      ≤ Q ^ 2 * (C ^ 2 * ε ^ 2) * (1 + Real.pi / a) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C ^ 2 * (Q ^ 2 * ε ^ 2 * (1 + Real.pi / a)) := by ring
    _ ≤ C ^ 2 * (8 * ε * Q) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 8 * C ^ 2 * ε * Q := by ring

end

end Work.BourgainPlan.IonescuWainger

