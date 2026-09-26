import Mathlib

namespace Work.Generic

/-- Double Rolle: if `F` is `C²` and vanishes at three points `a < x < b`, then `F''` has a zero
in `(a, b)`. -/
private lemma exists_second_deriv_zero_of_three_zeros {F : ℝ → ℝ} {a x b : ℝ}
    (hax : a < x) (hxb : x < b) (hF : ContDiff ℝ 2 F)
    (ha : F a = 0) (hx : F x = 0) (hb : F b = 0) :
    ∃ ζ ∈ Set.Ioo a b, deriv (deriv F) ζ = 0 := by
  have hcontF : Continuous F := hF.continuous
  have hcontDF : Continuous (deriv F) := by
    have := hF.continuous_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  obtain ⟨c₁, hc₁, hdc₁⟩ := exists_deriv_eq_zero hax hcontF.continuousOn (by rw [ha, hx])
  obtain ⟨c₂, hc₂, hdc₂⟩ := exists_deriv_eq_zero hxb hcontF.continuousOn (by rw [hx, hb])
  have h12 : c₁ < c₂ := lt_trans hc₁.2 hc₂.1
  obtain ⟨ζ, hζ, hdζ⟩ := exists_deriv_eq_zero h12 hcontDF.continuousOn (by rw [hdc₁, hdc₂])
  exact ⟨ζ, ⟨hc₁.1.trans hζ.1, hζ.2.trans hc₂.2⟩, hdζ⟩

/-- **The interpolation error of a `C²` function, in mean-value (signed) form.**  For a `C²`
function on `[a,b]` and `ξ ∈ [0,1]` there is an interior point `ζ` at which

    f (a + ξ * (b - a)) - ((1 - ξ) * f a + ξ * f b) = -(ξ (1 - ξ) / 2) * (b - a)² * f'' ζ .

(The absolute-value version, with a bound on `f''` in place of the mean value, is
`Work.Drive.interp_error_upper`; the point here is the *sign*, i.e. that the mean value can be taken
with a single interior `ζ`.) -/
theorem interp_error_meanValue {f : ℝ → ℝ} {a b ξ : ℝ} (hab : a < b)
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (hf : ContDiff ℝ 2 f) :
    ∃ ζ ∈ Set.Ioo a b,
      f (a + ξ * (b - a)) - ((1 - ξ) * f a + ξ * f b)
        = -((ξ * (1 - ξ) / 2) * (b - a) ^ 2 * deriv (deriv f) ζ) := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  rcases eq_or_lt_of_le hξ0 with h0 | hξpos
  · subst h0
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    have e1 : a + (0 : ℝ) * (b - a) = a := by ring
    have e2 : (1 - (0 : ℝ)) * f a + (0 : ℝ) * f b = f a := by ring
    have e3 : -(((0 : ℝ) * (1 - 0) / 2) * (b - a) ^ 2 * deriv (deriv f) ((a + b) / 2)) = 0 := by
      ring
    rw [e1, e2, e3]
    ring
  rcases eq_or_lt_of_le hξ1 with h1 | hξlt1
  · subst h1
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    have e1 : a + (1 : ℝ) * (b - a) = b := by ring
    have e2 : (1 - (1 : ℝ)) * f a + (1 : ℝ) * f b = f b := by ring
    have e3 : -(((1 : ℝ) * (1 - 1) / 2) * (b - a) ^ 2 * deriv (deriv f) ((a + b) / 2)) = 0 := by
      ring
    rw [e1, e2, e3]
    ring
  -- main case: `0 < ξ < 1`
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hbane : b - a ≠ 0 := ne_of_gt hba
  set t : ℝ := a + ξ * (b - a) with ht_def
  have ht_gt : a < t := by
    have : 0 < ξ * (b - a) := mul_pos hξpos hba
    rw [ht_def]; linarith
  have ht_lt : t < b := by
    have h : ξ * (b - a) < b - a := by
      have := mul_lt_mul_of_pos_right hξlt1 hba
      simpa using this
    rw [ht_def]; linarith
  have hta : t - a = ξ * (b - a) := by rw [ht_def]; ring
  have htb : t - b = (ξ - 1) * (b - a) := by rw [ht_def]; ring
  set m : ℝ := (f b - f a) / (b - a) with hm_def
  set L : ℝ → ℝ := fun y => f a + (y - a) * m with hL_def
  have hLa : L a = f a := by
    simp only [hL_def]; ring
  have hLb : L b = f b := by
    simp only [hL_def, hm_def]
    field_simp
    ring
  have hLt : L t = (1 - ξ) * f a + ξ * f b := by
    simp only [hL_def]
    rw [hta, hm_def]
    field_simp
    ring
  set C : ℝ := (f t - L t) / ((t - a) * (t - b)) with hC_def
  have hden : (t - a) * (t - b) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact ne_of_gt (sub_pos.mpr ht_gt)
    · exact ne_of_lt (sub_neg.mpr ht_lt)
  have hCt : C * ((t - a) * (t - b)) = f t - L t := by
    rw [hC_def]
    exact div_mul_cancel₀ _ hden
  set G : ℝ → ℝ := fun y => f y - L y - C * ((y - a) * (y - b)) with hG_def
  have hcontG : ContDiff ℝ 2 G := by
    rw [hG_def, hL_def]
    fun_prop
  have hGa : G a = 0 := by
    simp only [hG_def]
    rw [hLa]
    ring
  have hGb : G b = 0 := by
    simp only [hG_def]
    rw [hLb]
    ring
  have hGt : G t = 0 := by
    simp only [hG_def]
    rw [hCt]
    ring
  obtain ⟨ζ, hζ, hdζ⟩ :=
    exists_second_deriv_zero_of_three_zeros ht_gt ht_lt hcontG hGa hGt hGb
  have hderG : deriv G = fun y => deriv f y - m - C * (2 * y - a - b) := by
    funext y
    have h1 : HasDerivAt f (deriv f y) y := (hf.differentiable (by norm_num) y).hasDerivAt
    have hlin0 : HasDerivAt (fun z : ℝ => z - a) 1 y := by
      simpa using (hasDerivAt_id y).sub_const a
    have hlin : HasDerivAt (fun z : ℝ => (z - a) * m) m y := by
      have h := hlin0.mul_const m
      rw [one_mul] at h
      exact h
    have h2 : HasDerivAt (fun z : ℝ => f a + (z - a) * m) m y := by
      have h := (hasDerivAt_const y (f a)).add hlin
      rw [zero_add] at h
      exact h
    have hq : HasDerivAt (fun z : ℝ => (z - a) * (z - b)) (2 * y - a - b) y := by
      have hB : HasDerivAt (fun z : ℝ => z - b) 1 y := by
        simpa using (hasDerivAt_id y).sub_const b
      have hmul := hlin0.mul hB
      have hval : (1 * (y - b) + (y - a) * 1 : ℝ) = 2 * y - a - b := by ring
      rwa [hval] at hmul
    have h3 : HasDerivAt (fun z : ℝ => C * ((z - a) * (z - b))) (C * (2 * y - a - b)) y :=
      hq.const_mul C
    have h4 : HasDerivAt (fun z : ℝ => f z - (f a + (z - a) * m) - C * ((z - a) * (z - b)))
        (deriv f y - m - C * (2 * y - a - b)) y := (h1.sub h2).sub h3
    rw [hG_def, hL_def]
    exact h4.deriv
  have hder2G : deriv (deriv G) ζ = deriv (deriv f) ζ - 2 * C := by
    have hdf : Differentiable ℝ (deriv f) := by
      have := hf.differentiable_iteratedDeriv 1 (by norm_num)
      simpa [iteratedDeriv_one] using this
    have h1 : HasDerivAt (deriv f) (deriv (deriv f) ζ) ζ := (hdf ζ).hasDerivAt
    have hlin : HasDerivAt (fun z : ℝ => 2 * z - a - b) 2 ζ := by
      have h0 : HasDerivAt (fun z : ℝ => 2 * z) 2 ζ := by
        simpa using (hasDerivAt_id ζ).const_mul (2 : ℝ)
      simpa [sub_sub] using h0.sub_const (a + b)
    have h2' : HasDerivAt (fun z : ℝ => C * (2 * z - a - b)) (C * 2) ζ := hlin.const_mul C
    have h3 : HasDerivAt (fun z : ℝ => deriv f z - m - C * (2 * z - a - b))
        (deriv (deriv f) ζ - C * 2) ζ := (h1.sub_const m).sub h2'
    rw [hderG, h3.deriv]
    ring
  have hK : deriv (deriv f) ζ = 2 * C := by linarith [hdζ, hder2G]
  refine ⟨ζ, hζ, ?_⟩
  have hprod : (t - a) * (t - b) = -(ξ * (1 - ξ)) * (b - a) ^ 2 := by
    rw [hta, htb]; ring
  rw [hK, ← hLt, ← hCt, hprod]
  ring

end Work.Generic
