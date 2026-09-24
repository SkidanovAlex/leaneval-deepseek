import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral Set

private lemma integral_one_div_mul_sub (α β D : ℝ) (hαβ : α ≤ β) (hα0 : 0 < α) (hβD : β < D) :
    (∫ u in α..β, 1/(u*(D-u))) = (Real.log β - Real.log (D-β))/D - (Real.log α - Real.log (D-α))/D := by
  have hD0 : 0 < D := lt_of_lt_of_le hα0 (le_of_lt (lt_of_le_of_lt hαβ hβD))
  have hcont : ContinuousOn (fun u : ℝ => (Real.log u - Real.log (D - u))/D) (Icc α β) := by
    have h1 : ContinuousOn (fun u : ℝ => Real.log u) (Icc α β) :=
      ContinuousOn.log continuousOn_id (fun u hu => ne_of_gt (lt_of_lt_of_le hα0 hu.1))
    have h2 : ContinuousOn (fun u : ℝ => Real.log (D - u)) (Icc α β) :=
      ContinuousOn.log (continuousOn_const.sub continuousOn_id)
        (fun u hu => ne_of_gt (by linarith [hu.2, hβD]))
    exact (h1.sub h2).div_const D
  have hderiv : ∀ u ∈ Ioo α β,
      HasDerivAt (fun u : ℝ => (Real.log u - Real.log (D - u))/D) (1/(u*(D-u))) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans hα0 hu.1)
    have hDu : D - u ≠ 0 := ne_of_gt (by linarith [hu.2, hβD])
    have hd1 : HasDerivAt (fun u : ℝ => Real.log u) u⁻¹ u := Real.hasDerivAt_log hu0
    have hd2 : HasDerivAt (fun u : ℝ => D - u) (-1) u := (hasDerivAt_id u).const_sub D
    have hd3 : HasDerivAt (fun u : ℝ => Real.log (D - u)) ((-1)/(D-u)) u := hd2.log hDu
    have hd4 : HasDerivAt (fun u : ℝ => Real.log u - Real.log (D-u)) (u⁻¹ - (-1)/(D-u)) u :=
      hd1.sub hd3
    have hd5 := hd4.div_const D
    have hval : (u⁻¹ - (-1)/(D-u))/D = 1/(u*(D-u)) := by
      field_simp [hD0.ne']; ring
    rw [hval] at hd5
    exact hd5
  have hint : IntervalIntegrable (fun u : ℝ => 1/(u*(D-u))) volume α β := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hαβ]
    exact ContinuousOn.div continuousOn_const
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun u hu => mul_ne_zero (ne_of_gt (lt_of_lt_of_le hα0 hu.1))
        (ne_of_gt (by linarith [hu.2, hβD])))
  rw [integral_eq_sub_of_hasDerivAt_of_le hαβ hcont hderiv hint]

/-- The inner (over `q₂`) integral of the `B`-term estimate, with the lower limit `A` allowed to undershoot `(x+2)^{1/3}` by up to `3` (the slack costs only `1000/(x^{1/3} log(x+2))`). For `1 < x`, `0 < q`, `q³ ≤ x+2` (so `β = log q/log(x+2) ≤ 1/3`) and `e ≤ A ≤ B ≤ √((x+2)/q)` with `A ≥ (x+2)^{1/3} − 3`,
`∫_A^B dt/(t log t log((x+2)/(q t))) ≤ log(2−3β)/((1−β)log(x+2)) + 1000/(x^{1/3} log(x+2))`.
(The exact-endpoint identity, antiderivative `t ↦ (log log t − log(log(x+2) − log q − log t))/(log(x+2) − log q)`, is the case `A = (x+2)^{1/3}`, `B = √((x+2)/q)`.) -/
theorem innerIntegral_bound (x q A B : ℝ) (hx : 1 < x) (hq : 0 < q) (hq3 : q^3 ≤ x + 2)
    (hA : Real.exp 1 ≤ A) (hA' : (x + 2) ^ ((1:ℝ)/3) - 3 ≤ A) (hAB : A ≤ B)
    (hB : B ≤ Real.sqrt ((x + 2) / q)) :
    (∫ t in A..B, 1 / (t * Real.log t * Real.log ((x + 2) / (q * t))))
      ≤ Real.log (2 - 3 * (Real.log q / Real.log (x + 2))) /
          ((1 - Real.log q / Real.log (x + 2)) * Real.log (x + 2))
        + 1000 / (x ^ ((1:ℝ)/3) * Real.log (x + 2)) := by
  set L := Real.log (x + 2) with hL
  set D := L - Real.log q with hD
  set c := (x + 2) ^ ((1:ℝ)/3) with hc
  set m := L / 3 with hm
  set α := Real.log A with hα
  set β := Real.log B with hβ
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have hx2 : (0:ℝ) < x + 2 := by linarith
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hx13 : (0:ℝ) < x ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos hx0 _
  have hlogq3 : 3 * Real.log q ≤ L := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < q^3) hq3
    rw [Real.log_pow] at h
    push_cast at h
    rw [← hL] at h
    linarith
  have hDpos : 0 < D := by rw [hD]; linarith
  have hApos : (0:ℝ) < A := lt_of_lt_of_le (Real.exp_pos 1) hA
  have hA1 : 1 < A := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hA
  have hlogA1 : 1 ≤ α := by
    rw [hα]
    have h := Real.log_le_log (Real.exp_pos 1) hA
    rwa [Real.log_exp] at h
  have hα0 : 0 < α := lt_of_lt_of_le one_pos hlogA1
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le hApos hAB
  have hαβ : α ≤ β := by rw [hα, hβ]; exact Real.log_le_log hApos hAB
  have hβ1 : 1 ≤ β := le_trans hlogA1 hαβ
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hx2 _
  have hcx : x ^ ((1:ℝ)/3) ≤ c := by
    rw [hc]; exact Real.rpow_le_rpow (le_of_lt hx0) (by linarith) (by norm_num)
  have hlogc : Real.log c = m := by
    rw [hc, hm, Real.log_rpow hx2, ← hL]; ring
  have hmpos : 0 < m := by rw [hm]; linarith
  have hAquarter : x ^ ((1:ℝ)/3) / 4 ≤ A := by
    by_cases hcase : x ^ ((1:ℝ)/3) ≤ 4
    · have h1 : x ^ ((1:ℝ)/3) / 4 ≤ (1:ℝ) := by linarith
      linarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
    · rw [not_le] at hcase
      have h1 : x ^ ((1:ℝ)/3) / 4 ≤ x ^ ((1:ℝ)/3) - 3 := by linarith
      linarith [hcx]
  have hB2 : B^2 ≤ (x + 2)/q := by
    have hr : 0 ≤ (x + 2)/q := by positivity
    have h1 : B^2 ≤ (Real.sqrt ((x + 2)/q))^2 := pow_le_pow_left₀ hBpos.le hB 2
    rwa [Real.sq_sqrt hr] at h1
  have h2β : 2*β ≤ D := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < B^2) hB2
    rw [Real.log_pow] at h
    rw [Real.log_div hx2.ne' hq.ne'] at h
    rw [← hβ, ← hL, ← hD] at h
    push_cast at h
    linarith
  have hDm : 0 < D - m := by
    have h1 : m ≤ D - m := by rw [hD, hm]; linarith [hlogq3]
    linarith
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := A) (b := B) (f := Real.log) (f' := fun u : ℝ => u⁻¹)
    (g := fun u : ℝ => 1/(u * (D - u)))
    (by
      rw [uIcc_of_le hAB]
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le hApos ht.1)))
    (by
      rw [min_eq_left hAB, max_eq_right hAB]
      intro u hu
      exact Real.hasDerivAt_log (ne_of_gt (lt_trans hApos hu.1)))
    (by
      rw [min_eq_left hAB, max_eq_right hAB]
      intro u hu
      exact inv_nonneg.mpr (le_of_lt (lt_trans hApos hu.1)))
  rw [← hα, ← hβ] at hsub
  have hI1 : (∫ t in A..B, 1 / (t * Real.log t * Real.log ((x + 2) / (q * t))))
      = ∫ u in α..β, 1/(u*(D-u)) := by
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hAB] at ht
    simp only [Function.comp_apply]
    have htpos : (0:ℝ) < t := lt_of_lt_of_le hApos ht.1
    have hltβ : Real.log t ≤ β := by
      rw [hβ]; exact Real.log_le_log htpos ht.2
    have hDtpos : 0 < D - Real.log t := by linarith [h2β, hltβ]
    have hlog : Real.log ((x + 2) / (q * t)) = D - Real.log t := by
      rw [Real.log_div hx2.ne' (by positivity), Real.log_mul hq.ne' htpos.ne', hD, hL]
      ring
    rw [← hlog]
    have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (lt_of_lt_of_le hA1 ht.1))
    have hDt : Real.log ((x + 2) / (q * t)) ≠ 0 := ne_of_gt (by rw [hlog]; exact hDtpos)
    have htne : t ≠ 0 := ne_of_gt htpos
    field_simp
  have hI2 : (∫ u in α..β, 1/(u*(D-u)))
      = (Real.log β - Real.log (D-β))/D - (Real.log α - Real.log (D-α))/D :=
    integral_one_div_mul_sub α β D hαβ hα0 (by linarith [h2β])
  have hI3 : (Real.log β - Real.log (D-β))/D - (Real.log α - Real.log (D-α))/D
      ≤ (Real.log (D-α) - Real.log α)/D := by
    have hX : Real.log β - Real.log (D-β) ≤ 0 := by
      have h1 : Real.log β ≤ Real.log (D - β) :=
        Real.log_le_log (lt_of_lt_of_le one_pos hβ1) (by linarith [h2β])
      linarith
    rw [div_sub_div_same]
    apply div_le_div_of_nonneg_right _ hDpos.le
    linarith
  have hstep5 : Real.log (D - α) - Real.log α
      ≤ (Real.log (D - m) - Real.log m) + 1000*D/(x^((1:ℝ)/3)*L) := by
    by_cases hcA : c ≤ A
    · have hmα : m ≤ α := by
        rw [← hlogc, hα]
        exact Real.log_le_log hcpos hcA
      have hDα : 0 < D - α := by linarith [h2β, hαβ, hlogA1]
      have h1 : Real.log (D - α) ≤ Real.log (D - m) := Real.log_le_log hDα (by linarith)
      have h2 : Real.log m ≤ Real.log α := Real.log_le_log hmpos hmα
      have h3 : (0:ℝ) ≤ 1000*D/(x^((1:ℝ)/3)*L) := by positivity
      linarith
    · rw [not_le] at hcA
      have hmα : α < m := by
        rw [← hlogc, hα]
        exact Real.log_lt_log hApos hcA
      have hm1 : 1 < m := by
        rw [← hlogc]
        have h := Real.log_lt_log (Real.exp_pos 1) (lt_of_le_of_lt hA hcA)
        rwa [Real.log_exp] at h
      have hδ : 0 < m - α := by linarith
      have ha : Real.log (D - α) - Real.log (D - m) ≤ (m - α)/(D - m) := by
        have hfac : D - α = (D - m) * (1 + (m - α)/(D - m)) := by field_simp; ring
        have hfpos : 0 < 1 + (m - α)/(D - m) := by positivity
        have hlog : Real.log (D - α)
            = Real.log (D - m) + Real.log (1 + (m - α)/(D - m)) := by
          rw [hfac, Real.log_mul hDm.ne' hfpos.ne']
        rw [hlog]
        have h := Real.log_le_sub_one_of_pos hfpos
        linarith
      have hb : Real.log m - Real.log α ≤ (m - α)/α := by
        have hma : 0 < m/α := div_pos hmpos hα0
        have h := Real.log_le_sub_one_of_pos hma
        rw [Real.log_div hmpos.ne' hα0.ne'] at h
        have he : m/α - 1 = (m - α)/α := by field_simp
        linarith
      have hDm1 : 1 ≤ D - m := by
        have h1 : m ≤ D - m := by rw [hD, hm]; linarith [hlogq3]
        linarith
      have hsum : Real.log (D - α) - Real.log α - (Real.log (D - m) - Real.log m)
          ≤ 2*(m - α) := by
        have h1 : (m - α)/(D - m) ≤ m - α := by
          rw [div_le_iff₀ hDm]
          exact le_mul_of_one_le_right hδ.le hDm1
        have h2 : (m - α)/α ≤ m - α := by
          rw [div_le_iff₀ hα0]
          exact le_mul_of_one_le_right hδ.le hlogA1
        linarith
      have hδle : m - α ≤ 12/x^((1:ℝ)/3) := by
        have h1 : m - α = Real.log (c/A) := by
          rw [← hlogc, hα, Real.log_div hcpos.ne' hApos.ne']
        rw [h1]
        have h2 : Real.log (c/A) ≤ c/A - 1 := Real.log_le_sub_one_of_pos (by positivity)
        have h3 : c/A - 1 = (c - A)/A := by field_simp
        have h4 : (c - A)/A ≤ 3/A := div_le_div_of_nonneg_right (by linarith [hA']) hApos.le
        have h5 : 3/A ≤ 12/x^((1:ℝ)/3) := by
          rw [div_le_iff₀ hApos]
          rw [show (12:ℝ)/x^((1:ℝ)/3) * A = 12*A/x^((1:ℝ)/3) by ring]
          rw [le_div_iff₀ hx13]
          linarith [hAquarter]
        linarith
      have h24 : 2*(m - α) ≤ 1000*D/(x^((1:ℝ)/3)*L) := by
        have hDL : (24:ℝ) ≤ 1000*D/L := by
          have h1 : (2:ℝ)/3 ≤ D/L := by
            rw [hD, show (L - Real.log q)/L = 1 - Real.log q/L by
              rw [sub_div, div_self hLpos.ne']]
            have h2 : Real.log q/L ≤ 1/3 := by rw [div_le_iff₀ hLpos]; linarith [hlogq3]
            linarith
          rw [mul_div_assoc]
          linarith
        have hA1 : (24:ℝ)/x^((1:ℝ)/3) ≤ 1000*D/(x^((1:ℝ)/3)*L) := by
          rw [show (1000:ℝ)*D/(x^((1:ℝ)/3)*L) = (1000*D/L)/x^((1:ℝ)/3) by
            field_simp [hLpos.ne', hx13.ne']]
          exact div_le_div_of_nonneg_right hDL hx13.le
        have h2δ : 2*(m - α) ≤ 24/x^((1:ℝ)/3) := by
          have h := mul_le_mul_of_nonneg_left hδle (by norm_num : (0:ℝ) ≤ (2:ℝ))
          rw [show (2:ℝ) * (12/x^((1:ℝ)/3)) = 24/x^((1:ℝ)/3) by ring] at h
          exact h
        linarith [h2δ, hA1]
      linarith [hsum, h24]
  have hstep6 : Real.log (D - m) - Real.log m = Real.log (2 - 3*(Real.log q/L)) := by
    rw [← Real.log_div hDm.ne' hmpos.ne']
    congr 1
    rw [hD, hm]
    field_simp
    ring
  have hI4 : (Real.log (D-α) - Real.log α)/D
      ≤ ((Real.log (D-m) - Real.log m) + 1000*D/(x^((1:ℝ)/3)*L))/D :=
    div_le_div_of_nonneg_right hstep5 hDpos.le
  have hI5 : ((Real.log (D-m) - Real.log m) + 1000*D/(x^((1:ℝ)/3)*L))/D
      = Real.log (2 - 3*(Real.log q/L))/((1 - Real.log q/L)*L) + 1000/(x^((1:ℝ)/3)*L) := by
    have hLD : (1 - Real.log q/L)*L = D := by rw [hD]; field_simp
    rw [hstep6.symm, hLD]
    field_simp
  calc (∫ t in A..B, 1 / (t * Real.log t * Real.log ((x + 2) / (q * t))))
      = ∫ u in α..β, 1/(u*(D-u)) := hI1
    _ = (Real.log β - Real.log (D-β))/D - (Real.log α - Real.log (D-α))/D := hI2
    _ ≤ (Real.log (D-α) - Real.log α)/D := hI3
    _ ≤ ((Real.log (D-m) - Real.log m) + 1000*D/(x^((1:ℝ)/3)*L))/D := hI4
    _ = Real.log (2 - 3*(Real.log q/L))/((1 - Real.log q/L)*L)
          + 1000/(x^((1:ℝ)/3)*L) := hI5

end Work.NumberTheory.Chen.BTermCount
