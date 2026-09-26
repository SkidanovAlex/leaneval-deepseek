import Mathlib

namespace Work.Drive

/-- **Rolle-based second-order envelope.** If `F` is `C²` on `[a, b]`, vanishes at both
endpoints, and `|F''| ≤ B` there, then for `x ∈ (a, b)`
`|F x| ≤ B (x - a) (b - x) / 2`. -/
private lemma interp_error_aux {F : ℝ → ℝ} {a b B x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hF : ContDiff ℝ 2 F) (ha : F a = 0) (hb : F b = 0)
    (hbd : ∀ y ∈ Set.Icc a b, |deriv (deriv F) y| ≤ B) :
    |F x| ≤ B * (x - a) * (b - x) / 2 := by
  obtain ⟨hax, hxb⟩ := hx
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hax)
  have hxb' : x - b ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxb)
  have hprod : (x - a) * (x - b) ≠ 0 := mul_ne_zero hxa hxb'
  set K : ℝ := F x / ((x - a) * (x - b)) with hK
  set G : ℝ → ℝ := fun y => F y - K * ((y - a) * (y - b)) with hG
  have hFx : K * ((x - a) * (x - b)) = F x := by
    rw [hK]; exact div_mul_cancel₀ _ hprod
  have hGa : G a = 0 := by simp [hG, ha]
  have hGb : G b = 0 := by simp [hG, hb]
  have hGx : G x = 0 := by
    simp only [hG]
    rw [hFx]
    ring
  have hcontG : Continuous G := by
    rw [hG]
    fun_prop
  have hderivG : deriv G = fun y => deriv F y - K * (2*y - a - b) := by
    funext y
    have h1 : HasDerivAt F (deriv F y) y := (hF.differentiable (by norm_num) y).hasDerivAt
    have hq : HasDerivAt (fun z : ℝ => (z - a) * (z - b)) (2*y - a - b) y := by
      have hA : HasDerivAt (fun z : ℝ => z - a) 1 y := by simpa using (hasDerivAt_id y).sub_const a
      have hB : HasDerivAt (fun z : ℝ => z - b) 1 y := by simpa using (hasDerivAt_id y).sub_const b
      have hm := hA.mul hB
      have hval : (1 * (y - b) + (y - a) * 1 : ℝ) = 2*y - a - b := by ring
      rwa [hval] at hm
    have h2 : HasDerivAt (fun z : ℝ => K * ((z - a) * (z - b))) (K * (2*y - a - b)) y := hq.const_mul K
    have h3 : HasDerivAt (fun z : ℝ => F z - K * ((z - a) * (z - b))) (deriv F y - K * (2*y - a - b)) y := h1.sub h2
    rw [hG]
    exact h3.deriv
  have hdf : Differentiable ℝ (deriv F) := by
    have := hF.differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have hcontDG : Continuous (deriv G) := by
    rw [hderivG]
    have hcdf : Continuous (deriv F) := by
      have := hF.continuous_iteratedDeriv 1 (by norm_num)
      simpa [iteratedDeriv_one] using this
    fun_prop
  obtain ⟨y1, hy1, hdy1⟩ := exists_deriv_eq_zero hax (hcontG.continuousOn) (by rw [hGa, hGx])
  obtain ⟨y2, hy2, hdy2⟩ := exists_deriv_eq_zero hxb (hcontG.continuousOn) (by rw [hGx, hGb])
  have hy12 : y1 < y2 := lt_trans hy1.2 hy2.1
  obtain ⟨η, hη, hdη⟩ := exists_deriv_eq_zero hy12 (hcontDG.continuousOn) (by rw [hdy1, hdy2])
  have hηmem : η ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hy1.1 hη.1), le_of_lt (lt_trans hη.2 hy2.2)⟩
  have h2deriv : deriv (deriv G) η = deriv (deriv F) η - 2 * K := by
    have h1 : HasDerivAt (deriv F) (deriv (deriv F) η) η := (hdf η).hasDerivAt
    have hlin : HasDerivAt (fun z : ℝ => 2*z - a - b) 2 η := by
      have h0 : HasDerivAt (fun z : ℝ => 2 * z) 2 η := by
        simpa using (hasDerivAt_id η).const_mul (2:ℝ)
      simpa [sub_sub] using h0.sub_const (a + b)
    have h2' : HasDerivAt (fun z : ℝ => K * (2*z - a - b)) (K * 2) η := hlin.const_mul K
    have h3 : HasDerivAt (fun z : ℝ => deriv F z - K*(2*z-a-b)) (deriv (deriv F) η - K*2) η := h1.sub h2'
    rw [hderivG, h3.deriv]
    ring
  have hk2 : deriv (deriv F) η = 2 * K := by linarith [hdη, h2deriv]
  have hbnd : |2 * K| ≤ B := by
    have h := hbd η hηmem
    rwa [hk2] at h
  have hKle : |K| ≤ B / 2 := by
    have h2K : |2 * K| = 2 * |K| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [h2K] at hbnd
    linarith
  have hxa_pos : 0 < x - a := sub_pos.mpr hax
  have hxbn : x - b < 0 := sub_neg.mpr hxb
  have hnonneg : 0 ≤ (x - a) * (b - x) := mul_nonneg (le_of_lt hxa_pos) (by linarith)
  have habs : |F x| = |K| * ((x - a) * (b - x)) := by
    rw [← hFx, abs_mul, abs_mul, abs_of_pos hxa_pos, abs_of_neg hxbn]
    ring
  calc |F x| = |K| * ((x - a) * (b - x)) := habs
    _ ≤ (B / 2) * ((x - a) * (b - x)) := mul_le_mul_of_nonneg_right hKle hnonneg
    _ = B * (x - a) * (b - x) / 2 := by ring

/-- **Linear-interpolation error bound.** For a `C²` function `f` with `|f''| ≤ B` on
`[a, a + w]` and `ξ ∈ [0, 1]`,
`|f (a + ξ w) - ((1 - ξ) f a + ξ f (a + w))| ≤ (ξ (1 - ξ) / 2) w² B`. -/
theorem interp_error_upper {f : ℝ → ℝ} {a w ξ B : ℝ} (hw : 0 ≤ w) (hB : 0 ≤ B)
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    (hf : ContDiff ℝ 2 f)
    (hbd : ∀ x ∈ Set.Icc a (a + w), |deriv (deriv f) x| ≤ B) :
    |f (a + ξ * w) - ((1 - ξ) * f a + ξ * f (a + w))| ≤ (ξ * (1 - ξ) / 2) * w ^ 2 * B := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  rcases eq_or_lt_of_le hw with hw0 | hwpos
  · subst hw0
    have hh : (1 - ξ) * f a + ξ * f a = f a := by ring
    simp only [add_zero, mul_zero]
    rw [hh]
    simp
  have hwne : w ≠ 0 := ne_of_gt hwpos
  rcases eq_or_lt_of_le hξ0 with h0 | hξpos
  · subst h0; simp
  rcases eq_or_lt_of_le hξ1 with h1 | hξlt1
  · subst h1; simp
  set m : ℝ := (f (a + w) - f a) / w with hm
  set F : ℝ → ℝ := fun t => f t - (f a + (t - a) * m) with hFdef
  set x : ℝ := a + ξ * w with hxdef
  have hx_in : x ∈ Set.Ioo a (a + w) := by
    refine ⟨?_, ?_⟩
    · rw [hxdef]; nlinarith [hξpos, hwpos]
    · rw [hxdef]
      have h := mul_lt_mul_of_pos_right hξlt1 hwpos
      rw [one_mul] at h
      linarith
  have hFcont : ContDiff ℝ 2 F := by
    rw [hFdef]
    fun_prop
  have ha : F a = 0 := by rw [hFdef]; simp
  have hb : F (a + w) = 0 := by
    simp only [hFdef, hm]
    rw [show a + w - a = w by ring]
    have hwA : w * ((f (a + w) - f a) / w) = f (a + w) - f a := by field_simp
    rw [hwA]; ring
  have hbdF : ∀ y ∈ Set.Icc a (a + w), |deriv (deriv F) y| ≤ B := by
    intro y hy
    have hdd : deriv (deriv F) y = deriv (deriv f) y := by
      have hderF : deriv F = fun z => deriv f z - m := by
        funext z
        have h1 : HasDerivAt f (deriv f z) z := (hf.differentiable (by norm_num) z).hasDerivAt
        have hlin0 : HasDerivAt (fun t : ℝ => t - a) 1 z := by
          simpa using (hasDerivAt_id z).sub_const a
        have hlin : HasDerivAt (fun t : ℝ => (t - a) * m) m z := by
          have h := hlin0.mul_const m
          rw [one_mul] at h
          exact h
        have h2 : HasDerivAt (fun t : ℝ => f a + (t - a) * m) m z := by
          have h := (hasDerivAt_const z (f a)).add hlin
          rw [zero_add] at h
          exact h
        have h3 : HasDerivAt (fun t : ℝ => f t - (f a + (t - a) * m)) (deriv f z - m) z := h1.sub h2
        rw [hFdef]
        exact h3.deriv
      have hdf : Differentiable ℝ (deriv f) := by
        have := hf.differentiable_iteratedDeriv 1 (by norm_num)
        simpa [iteratedDeriv_one] using this
      have h1 : HasDerivAt (deriv f) (deriv (deriv f) y) y := (hdf y).hasDerivAt
      have h2 : HasDerivAt (fun _ : ℝ => m) 0 y := hasDerivAt_const y m
      have h3 : HasDerivAt (fun z => deriv f z - m) (deriv (deriv f) y - 0) y := h1.sub h2
      rw [hderF, h3.deriv]
      simp
    rw [hdd]
    exact hbd y hy
  have hmain := interp_error_aux hx_in hFcont ha hb hbdF
  have hFx_eq : F x = f x - ((1 - ξ) * f a + ξ * f (a + w)) := by
    simp only [hFdef, hm]
    have hxw : x - a = ξ * w := by rw [hxdef]; ring
    rw [hxw]
    have hwA : w * ((f (a + w) - f a) / w) = f (a + w) - f a := by field_simp
    rw [mul_assoc, hwA]
    ring
  have hright : B * (x - a) * ((a + w) - x) / 2 = (ξ * (1 - ξ) / 2) * w ^ 2 * B := by
    rw [hxdef]; ring
  rw [hFx_eq, hright] at hmain
  exact hmain

end Work.Drive
