import Mathlib
import Submission.Work.A3.singInt_bound
import Submission.Work.A3.majorArcKernel

namespace Work.A3

open MeasureTheory Polynomial

noncomputable section

/-- `mArcKernel N d 0 = N` for `d ≥ 1` (the kernel at `β = 0` is the (regularised) value `N`;
the identity holds for every `N`, including `N = 0` where both sides are `0`). -/
private lemma mArcKernel_zero_eq (d N : ℕ) (hd : 1 ≤ d) :
    mArcKernel N d 0 = (N : ℝ) := by
  rw [mArcKernel, abs_zero, zero_add]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  have hkey : (-(d : ℝ)) * (-(1 : ℝ) / (d : ℝ)) = 1 := by
    have hd0 : ((d : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [hkey, Real.rpow_one]

/-- The boundary case `β = 0` of the pointwise bound: `‖singInt Q N 0‖ = N = mArcKernel N d 0`. -/
private lemma norm_singInt_zero_le_mArcKernel_aux (Q : Polynomial ℤ)
    (hd : 1 ≤ Polynomial.natDegree Q) (N : ℕ) :
    ‖singInt Q N 0‖ ≤ mArcKernel N (Polynomial.natDegree Q) 0 := by
  have h1 : singInt Q N 0 = (N : ℂ) := by rw [singInt]; simp
  rw [h1, Complex.norm_natCast, mArcKernel_zero_eq (Polynomial.natDegree Q) N hd]

/-- The elementary comparison behind the pointwise bound: the two-regime bound
`‖singInt Q N β‖ ≤ min N (C|β|^{-1/d})` dominates `mArcKernel N d β` at least up to the constant
`max 1 C * 2^{1/d}`, because `mArcKernel N d β = (|β| + N^{-d})^{-1/d}` is `≥ 2^{-1/d}|β|^{-1/d}`
in the regime `|β| ≥ N^{-d}` and `≥ 2^{-1/d} N` in the regime `|β| ≤ N^{-d}`. -/
private lemma min_le_mul_mArcKernel_aux {d : ℕ} (hd : 1 ≤ d) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (N : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    min (N : ℝ) (C₁ * |β| ^ (-(1 : ℝ) / (d : ℝ)))
      ≤ max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) * mArcKernel N d β := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  set e : ℝ := -(1 : ℝ) / (d : ℝ) with he
  have he_nonpos : e ≤ 0 := by
    rw [he]
    simp only [neg_div]
    exact neg_nonpos.mpr (div_nonneg zero_le_one hdpos.le)
  have hexp : e = -((1 : ℝ) / (d : ℝ)) := by rw [he]; simp only [neg_div]
  have h2inv : ((2 : ℝ) ^ e)⁻¹ = (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by
    rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have h2e_pos : 0 < (2 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
  have h2inv_nonneg : 0 ≤ ((2 : ℝ) ^ e)⁻¹ := by positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h4 : (0 : ℝ) ≤ mArcKernel 0 d β := by
      rw [mArcKernel]
      simp only [Nat.cast_zero]
      apply Real.rpow_nonneg
      rw [Real.zero_rpow (ne_of_lt (by linarith : (-(d : ℝ)) < 0)), add_zero]
      exact abs_nonneg β
    have hmin : min ((0 : ℕ) : ℝ) (C₁ * |β| ^ e) = 0 := by
      rw [Nat.cast_zero]
      exact min_eq_left (mul_nonneg hC₁.le (Real.rpow_nonneg (abs_nonneg β) e))
    rw [hmin]
    have hthis : (0 : ℝ) ≤ max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) * mArcKernel 0 d β :=
      mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) h3) h4
    linarith [hthis]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNd_pos : 0 < (N : ℝ) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have hMpos : 0 < mArcKernel N d β := mArcKernel_pos hN1 hd β
    have hMnonneg : 0 ≤ mArcKernel N d β := hMpos.le
    rcases le_total ((N : ℝ) ^ (-(d : ℝ))) |β| with hcase | hcase
    · have hxpos : 0 < |β| + (N : ℝ) ^ (-(d : ℝ)) := by linarith
      have hxy : |β| + (N : ℝ) ^ (-(d : ℝ)) ≤ 2 * |β| := by linarith
      have hmono : (2 * |β|) ^ e ≤ (|β| + (N : ℝ) ^ (-(d : ℝ))) ^ e :=
        Real.rpow_le_rpow_of_nonpos hxpos hxy he_nonpos
      have hmul : (2 * |β|) ^ e = (2 : ℝ) ^ e * |β| ^ e :=
        Real.mul_rpow (by norm_num) (abs_nonneg β)
      have hMdef : mArcKernel N d β = (|β| + (N : ℝ) ^ (-(d : ℝ))) ^ e := by
        rw [mArcKernel, he]
      have hstep : (2 : ℝ) ^ e * |β| ^ e ≤ mArcKernel N d β := by
        rw [← hmul, hMdef]
        exact hmono
      have hAle : |β| ^ e ≤ ((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β := by
        have h := mul_le_mul_of_nonneg_left hstep h2inv_nonneg
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2e_pos), one_mul] at h
        exact h
      calc min (N : ℝ) (C₁ * |β| ^ e) ≤ C₁ * |β| ^ e := min_le_right _ _
        _ ≤ C₁ * (((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β) := mul_le_mul_of_nonneg_left hAle hC₁.le
        _ ≤ max 1 C₁ * (((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β) :=
            mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C₁)
              (mul_nonneg h2inv_nonneg hMnonneg)
        _ = max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) * mArcKernel N d β := by
            rw [h2inv]; ring
    · have hxpos : 0 < |β| + (N : ℝ) ^ (-(d : ℝ)) := by linarith
      have hxy : |β| + (N : ℝ) ^ (-(d : ℝ)) ≤ 2 * (N : ℝ) ^ (-(d : ℝ)) := by linarith
      have hmono : (2 * (N : ℝ) ^ (-(d : ℝ))) ^ e ≤ (|β| + (N : ℝ) ^ (-(d : ℝ))) ^ e :=
        Real.rpow_le_rpow_of_nonpos hxpos hxy he_nonpos
      have hmul : (2 * (N : ℝ) ^ (-(d : ℝ))) ^ e = (2 : ℝ) ^ e * ((N : ℝ) ^ (-(d : ℝ))) ^ e :=
        Real.mul_rpow (by norm_num) hNd_pos.le
      have hNd_pow : ((N : ℝ) ^ (-(d : ℝ))) ^ e = (N : ℝ) := by
        rw [← Real.rpow_mul hNpos.le]
        have hkey : (-(d : ℝ)) * e = 1 := by rw [he]; field_simp
        rw [hkey, Real.rpow_one]
      have hMdef : mArcKernel N d β = (|β| + (N : ℝ) ^ (-(d : ℝ))) ^ e := by
        rw [mArcKernel, he]
      have hstep : (2 : ℝ) ^ e * (N : ℝ) ≤ mArcKernel N d β := by
        rw [← hNd_pow, ← hmul, hMdef]
        exact hmono
      have hNle : (N : ℝ) ≤ ((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β := by
        have h := mul_le_mul_of_nonneg_left hstep h2inv_nonneg
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2e_pos), one_mul] at h
        exact h
      calc min (N : ℝ) (C₁ * |β| ^ e) ≤ (N : ℝ) := min_le_left _ _
        _ ≤ ((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β := hNle
        _ = 1 * (((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β) := (one_mul _).symm
        _ ≤ max 1 C₁ * (((2 : ℝ) ^ e)⁻¹ * mArcKernel N d β) :=
            mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C₁)
              (mul_nonneg h2inv_nonneg hMnonneg)
        _ = max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / (d : ℝ)) * mArcKernel N d β := by
            rw [h2inv]; ring

/-- Pointwise bound for the singular integral in the exact shape (`mArcKernel`) used by the transition-arc estimate: `‖singInt Q N β‖ ≤ C * mArcKernel N d β`, `d = Q.natDegree`.  Derive it from `Work.A3.singInt_pointwise` (discharging its two hypotheses with `Work.A3.oscInt_levelSet_le` and `Work.A3.real_poly_levelSet_volume_le`, as `singInt_bound` does) plus the elementary comparison `min N (C|β|^{-1/d}) ≤ max 1 C * 2^{1/d} * mArcKernel N d β`; the case `β = 0` is immediate since `mArcKernel N d 0 = N = ‖singInt Q N 0‖` for `N ≥ 1` and `singInt Q 0 β = 0`. -/
lemma singInt_le_mArcKernel (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (β : ℝ),
      ‖Work.A3.singInt Q N β‖ ≤ C * Work.A3.mArcKernel N (Polynomial.natDegree Q) β := by
  have hd1 : 1 ≤ Polynomial.natDegree Q := by omega
  obtain ⟨C₁, hC₁pos, hpt⟩ := singInt_pointwise Q hd
    (fun f u v m hu hv hf hp => oscInt_levelSet_le f hu hv hf hp)
    (fun R hR => real_poly_levelSet_volume_le R hR)
  refine ⟨max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / ((Polynomial.natDegree Q : ℕ) : ℝ)),
    by positivity, ?_⟩
  have hK1 : (1 : ℝ) ≤ max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / ((Polynomial.natDegree Q : ℕ) : ℝ)) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _)
      (Real.one_le_rpow (by norm_num) (by positivity))
  intro N β
  rcases eq_or_ne β 0 with rfl | hβ
  · have hMnn : (0 : ℝ) ≤ mArcKernel N (Polynomial.natDegree Q) 0 := by
      rw [mArcKernel]
      apply Real.rpow_nonneg
      rw [abs_zero, zero_add]
      exact Real.rpow_nonneg (Nat.cast_nonneg N) _
    calc ‖singInt Q N 0‖ ≤ mArcKernel N (Polynomial.natDegree Q) 0 :=
          norm_singInt_zero_le_mArcKernel_aux Q hd1 N
      _ = 1 * mArcKernel N (Polynomial.natDegree Q) 0 := (one_mul _).symm
      _ ≤ max 1 C₁ * (2 : ℝ) ^ ((1 : ℝ) / ((Polynomial.natDegree Q : ℕ) : ℝ))
            * mArcKernel N (Polynomial.natDegree Q) 0 := mul_le_mul_of_nonneg_right hK1 hMnn
  · exact le_trans (hpt N β hβ) (min_le_mul_mArcKernel_aux hd1 hC₁pos N hβ)

end

end Work.A3
