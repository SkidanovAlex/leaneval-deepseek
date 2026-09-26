import Mathlib

namespace Work.CKFinal.Socket

open UpperHalfPlane Matrix Polynomial

/-- Elementary complex analysis input: for real `a b c d` and `z : ℂ`, the real part of the
Möbius ratio `(az+b)/(cz+d)` vanishes exactly when an explicit real quadratic expression
vanishes, provided the denominator is nonzero. -/
private lemma re_div_eq_zero_iff (z : ℂ) (a b c d : ℝ) (hD : (c : ℂ) * z + d ≠ 0) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).re = 0 ↔
      a * c * (z.re ^ 2 + z.im ^ 2) + (a * d + b * c) * z.re + b * d = 0 := by
  rw [Complex.div_re]
  have hNre : (((a : ℂ) * z + b)).re = a * z.re + b := by simp
  have hNim : (((a : ℂ) * z + b)).im = a * z.im := by simp
  have hDre : (((c : ℂ) * z + d)).re = c * z.re + d := by simp
  have hDim : (((c : ℂ) * z + d)).im = c * z.im := by simp
  have hns : Complex.normSq ((c : ℂ) * z + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [Complex.normSq_apply, hDre, hDim]; ring
  have hnsne : ((c * z.re + d) ^ 2 + (c * z.im) ^ 2) ≠ 0 := by
    rw [← hns]; exact (Complex.normSq_pos).mpr hD |>.ne'
  have heq : (a * z.re + b) * (c * z.re + d) + a * z.im * (c * z.im)
      = a * c * (z.re ^ 2 + z.im ^ 2) + (a * d + b * c) * z.re + b * d := by ring
  rw [hNre, hNim, hDre, hDim, hns, ← add_div, div_eq_zero_iff, heq]
  simp [hnsne]

/-- The determinant identity for `SL(2,ℤ)` transported to `ℝ`. -/
private lemma det_eq_one (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 1)
      - algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 0) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  have := congrArg (algebraMap ℤ ℝ) h
  simpa only [map_sub, map_mul, map_one] using this

/-- The real part of `γ • w` vanishes exactly on an explicit real quadratic expression in the
entries of `γ` and the coordinates of `w`. -/
private lemma re_smul_eq_zero_iff (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (w : ℍ) :
    (γ • w).re = 0 ↔
      (algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 0)) * (w.re ^ 2 + w.im ^ 2)
      + (algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 1)
          + algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 0)) * w.re
      + algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 1) = 0 := by
  have hdet := det_eq_one γ
  have hcd : ¬(algebraMap ℤ ℝ (γ 1 0) = 0 ∧ algebraMap ℤ ℝ (γ 1 1) = 0) := by
    rintro ⟨hc, hd⟩
    rw [hc, hd] at hdet
    linarith
  have hne : ![(algebraMap ℤ ℝ (γ 1 0)), (algebraMap ℤ ℝ (γ 1 1))] ≠ 0 := by
    intro h
    exact hcd ⟨by simpa using congr_fun h 0, by simpa using congr_fun h 1⟩
  have hD := UpperHalfPlane.linear_ne_zero (τ := w) hne
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hD
  rw [show (γ • w).re = (↑(γ • w) : ℂ).re from rfl,
      UpperHalfPlane.coe_specialLinearGroup_apply γ w]
  rw [re_div_eq_zero_iff (w : ℂ) _ _ _ _ hD]
  simp

/-- For a fixed `γ ∈ SL(2,ℤ)`, the set of real shifts `s` for which `γ • (s +ᵥ u)` lands on the
imaginary axis (i.e. has zero real part) is finite. -/
theorem orbit_free_bad_finite (u : UpperHalfPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ({s : ℝ | (γ • (s +ᵥ u)).re = 0} : Set ℝ).Finite := by
  -- Write the coefficient of `w.re^2` as `A`, of `w.re` as `B`, and the constant as `Cv`.
  set A : ℝ := algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 0) with hA
  set B : ℝ := algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 1)
      + algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 0) with hB
  set Cv : ℝ := algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 1) with hC
  -- The corresponding polynomial in `s`, obtained by substituting `w = s +ᵥ u`.
  set p : ℝ[X] := Polynomial.monomial 2 A + Polynomial.monomial 1 (A * (2 * u.re) + B)
      + Polynomial.monomial 0 (A * (u.re ^ 2 + u.im ^ 2) + B * u.re + Cv) with hp
  -- `A` and `B` cannot both vanish, otherwise `det γ = 1` would fail.
  have hne : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    obtain ⟨hA0, hB0⟩ := h
    rw [hA] at hA0
    rw [hB] at hB0
    have hdet := det_eq_one γ
    have hz : algebraMap ℤ ℝ (γ 0 0) * algebraMap ℤ ℝ (γ 1 1)
        - algebraMap ℤ ℝ (γ 0 1) * algebraMap ℤ ℝ (γ 1 0) = 0 := by
      rcases mul_eq_zero.mp hA0 with h1 | h1
      · rw [h1] at hB0 ⊢; linarith
      · rw [h1] at hB0 ⊢; linarith
    linarith
  -- Hence `p` is a nonzero polynomial, so it has finitely many roots.
  have hp0 : p ≠ 0 := by
    intro h
    have h2 : A = 0 := by
      have hc : p.coeff 2 = 0 := by rw [h]; simp
      rw [hp] at hc
      simp only [Polynomial.coeff_add, Polynomial.coeff_monomial] at hc
      norm_num at hc
      exact hc
    have h1 : B = 0 := by
      have hc : p.coeff 1 = 0 := by rw [h]; simp
      rw [hp] at hc
      have h1' : A * (2 * u.re) + B = 0 := by
        simp only [Polynomial.coeff_add, Polynomial.coeff_monomial] at hc
        norm_num at hc
        exact hc
      rw [h2] at h1'
      simpa using h1'
    rcases hne with hh | hh
    · exact hh h2
    · exact hh h1
  refine (Polynomial.finite_setOfPred_isRoot hp0).subset ?_
  intro s hs
  have hs' : (γ • (s +ᵥ u)).re = 0 := hs
  change p.IsRoot s
  rw [Polynomial.IsRoot.def]
  have hkey := (re_smul_eq_zero_iff γ (s +ᵥ u)).mp hs'
  simp only [UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im] at hkey
  rw [← hA, ← hB, ← hC] at hkey
  have hpv : p.eval s = A * s ^ 2 + (A * (2 * u.re) + B) * s
      + (A * (u.re ^ 2 + u.im ^ 2) + B * u.re + Cv) := by
    rw [hp]; simp only [Polynomial.eval_add, Polynomial.eval_monomial]; ring
  rw [hpv]
  have heq2 : A * ((s + u.re) ^ 2 + u.im ^ 2) + B * (s + u.re) + Cv
      = A * s ^ 2 + (A * (2 * u.re) + B) * s
        + (A * (u.re ^ 2 + u.im ^ 2) + B * u.re + Cv) := by ring
  rw [heq2] at hkey
  exact hkey

end Work.CKFinal.Socket
