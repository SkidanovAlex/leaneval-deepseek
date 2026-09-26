/-
# Non-coincidence of `j(u)` with the `j`-values on the imaginary axis

The modular `j`-invariant `j = Work.Kernels.jInvariantFun` identifies `SL(2,ℤ)`-orbits: two
points of `ℍ` have the same `j`-value exactly when they are conjugate under `SL(2,ℤ)`
(`Work.Asymptotics.jInvariantFun_eq_smul_of_eq`).  Points of the imaginary axis are equivalent
to `u` precisely when `u` is in the orbit of `it` for some `t > 0`.

The point of the present lemma is the elementary observation, on which the "non-coincidence"
analysis of the CKMRV cusp expansion rests, that if `u = γ • (it)` for `γ ∈ SL(2,ℤ)` and
`1/2 < u.im`, then `u.re` is an integer.  Indeed writing `γ = !![A,B;C,D]` (with `A D - B C = 1`)
and `z = it`, the relation `u = (A z + B)/(C z + D)` has real and imaginary parts

  `u.re * D - u.im * C * t = B`,   `u.re * C * t + u.im * D = A * t`,

so that `u.im * (C² t² + D²) = t`.  Since `1/2 < u.im`, this gives `C² t² + D² < 2 t`, whence
after multiplying by `C²` and completing the square, `C² D² < 1`.  As `C, D` are integers this
forces `C = 0` or `D = 0`; in the first case `A D = 1` shows `D = ±1` and `u.re = B D ∈ ℤ`,
in the second `B C = -1` shows `C = ±1` and `u.re = A C ∈ ℤ`.

Consequently, for `u` with `1/2 < u.im` and non-integral real part, `j(u)` differs from the
`j`-value of every point of the imaginary axis.
-/
import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.HalfFunnel.tangKaxisFlatLow
import Submission.Work.Kernels.Theorem31

namespace Work.Asymptotics.NonCoincidence

open UpperHalfPlane Matrix ModularGroup

/-- If `γ • (it) = u` for some `γ ∈ SL(2,ℤ)`, `t > 0`, and `1/2 < u.im`, then `u.re` is an
integer.  This is the elementary orbit computation behind
`jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half`. -/
lemma re_mem_intRange_of_smul_imagAxis (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (t : ℝ) (ht : 0 < t) (u : ℍ)
    (hγ : γ • (Work.Kernels.imagAxis t ht) = u) (him : (1 / 2 : ℝ) < u.im) :
    u.re ∈ Set.range (fun n : ℤ => (n : ℝ)) := by
  set A : ℝ := algebraMap ℤ ℝ (γ 0 0) with hA
  set B : ℝ := algebraMap ℤ ℝ (γ 0 1) with hB
  set C : ℝ := algebraMap ℤ ℝ (γ 1 0) with hC
  set D : ℝ := algebraMap ℤ ℝ (γ 1 1) with hD
  -- the Möbius formula for the action, with `z = it`
  have hcoe : (↑u : ℂ) =
      ((A : ℂ) * ((t : ℂ) * Complex.I) + (B : ℂ)) /
        ((C : ℂ) * ((t : ℂ) * Complex.I) + (D : ℂ)) := by
    rw [← hγ, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
    rfl
  have hcoe_γ : (↑(γ • (Work.Kernels.imagAxis t ht)) : ℂ) =
      ((A : ℂ) * ((t : ℂ) * Complex.I) + (B : ℂ)) /
        ((C : ℂ) * ((t : ℂ) * Complex.I) + (D : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
    rfl
  -- the denominator is nonzero (the image has positive imaginary part)
  have hww : ((C : ℂ) * ((t : ℂ) * Complex.I) + (D : ℂ)) ≠ 0 := by
    intro h0
    have him0 : (↑(γ • (Work.Kernels.imagAxis t ht)) : ℂ).im = 0 := by
      rw [hcoe_γ, h0, div_zero]; simp
    rw [UpperHalfPlane.coe_im] at him0
    exact (γ • (Work.Kernels.imagAxis t ht)).im_ne_zero him0
  have hmul : (↑u : ℂ) * ((C : ℂ) * ((t : ℂ) * Complex.I) + (D : ℂ))
      = (A : ℂ) * ((t : ℂ) * Complex.I) + (B : ℂ) := by
    rw [hcoe]
    exact div_mul_cancel₀ _ hww
  -- separate real and imaginary parts of `u (C i t + D) = A i t + B`
  have heq1 : u.re * D - u.im * C * t = B := by
    have h := congrArg Complex.re hmul
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] at h
    linarith [h]
  have heq2 : u.re * C * t + u.im * D = A * t := by
    have h := congrArg Complex.im hmul
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] at h
    linarith [h]
  -- the entries are integer casts
  have hAi : A = ((γ 0 0 : ℤ) : ℝ) := by rw [hA, algebraMap_int_eq]; rfl
  have hBi : B = ((γ 0 1 : ℤ) : ℝ) := by rw [hB, algebraMap_int_eq]; rfl
  have hCi : C = ((γ 1 0 : ℤ) : ℝ) := by rw [hC, algebraMap_int_eq]; rfl
  have hDi : D = ((γ 1 1 : ℤ) : ℝ) := by rw [hD, algebraMap_int_eq]; rfl
  have hdet_int : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    simpa using h
  have hdet : A * D - B * C = 1 := by
    rw [hAi, hBi, hCi, hDi]
    exact_mod_cast hdet_int
  -- the two linear combinations
  have hy : u.im * (C ^ 2 * t ^ 2 + D ^ 2) = t := by
    linear_combination D * heq2 - (C * t) * heq1 + t * hdet
  have hx : u.re * (C ^ 2 * t ^ 2 + D ^ 2) = B * D + A * C * t ^ 2 := by
    linear_combination D * heq1 + (C * t) * heq2
  -- `C² t² + D²` is positive and `< 2t`
  have hQpos : 0 < C ^ 2 * t ^ 2 + D ^ 2 := by
    by_contra h
    push Not at h
    have hC : C = 0 := by
      have h1' : C ^ 2 * t ^ 2 = 0 := by
        nlinarith [sq_nonneg C, sq_nonneg D, sq_nonneg (C * t)]
      rcases mul_eq_zero.mp h1' with h' | h'
      · exact sq_eq_zero_iff.mp h'
      · exact absurd h' (pow_ne_zero 2 ht.ne')
    have hD : D = 0 := by nlinarith [sq_nonneg D]
    rw [hC, hD] at hdet
    norm_num at hdet
  have hy' : u.im = t / (C ^ 2 * t ^ 2 + D ^ 2) := by
    rw [eq_div_iff hQpos.ne']; exact hy
  have hQlt : C ^ 2 * t ^ 2 + D ^ 2 < 2 * t := by
    have := (lt_div_iff₀ hQpos).mp (by rw [← hy']; exact him)
    linarith
  -- hence `C² D² < 1`
  have hCDlt : C ^ 2 * D ^ 2 < 1 := by
    rcases eq_or_ne C 0 with hC0 | hCne
    · rw [hC0]; norm_num
    · have hC2 : 0 < C ^ 2 := sq_pos_of_ne_zero hCne
      have hkey : 0 < C ^ 2 * (2 * t - C ^ 2 * t ^ 2 - D ^ 2) := mul_pos hC2 (by linarith)
      nlinarith [hkey, sq_nonneg (C ^ 2 * t - 1)]
  -- `C² D² < 1` with integer `C, D` forces `C = 0` or `D = 0`
  have hlt1 : ((γ 1 0) ^ 2 * (γ 1 1) ^ 2 : ℤ) < 1 := by
    have h : (((γ 1 0) ^ 2 * (γ 1 1) ^ 2 : ℤ) : ℝ) < 1 := by
      rw [hCi, hDi] at hCDlt
      push_cast at hCDlt ⊢
      exact hCDlt
    exact_mod_cast h
  have hzero : (γ 1 0) ^ 2 * (γ 1 1) ^ 2 = 0 := by
    have hnn : 0 ≤ (γ 1 0) ^ 2 * (γ 1 1) ^ 2 := by positivity
    omega
  have hCD_zero : γ 1 0 = 0 ∨ γ 1 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact Or.inl (sq_eq_zero_iff.mp h')
    · exact Or.inr (sq_eq_zero_iff.mp h')
  rcases hCD_zero with hC0int | hD0int
  · -- `C = 0`: then `A D = 1`, so `D = ±1` and `u.re = B D`
    have hC0r : C = 0 := by rw [hCi, hC0int]; norm_num
    have hAD : A * D = 1 := by have := hdet; rw [hC0r] at this; linarith
    have hADint : γ 0 0 * γ 1 1 = 1 := by
      rw [hAi, hDi] at hAD
      exact_mod_cast hAD
    have hADint' : γ 1 1 * γ 0 0 = 1 := by rw [mul_comm]; exact hADint
    have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hADint'
    have hD2 : D ^ 2 = 1 := by rcases hd with hd | hd <;> rw [hDi, hd] <;> norm_num
    have hxr : u.re = B * D := by
      have hh := hx
      rw [hC0r] at hh
      ring_nf at hh
      rw [hD2, mul_one] at hh
      linarith [hh]
    exact ⟨γ 0 1 * γ 1 1, by rw [hxr, hBi, hDi]; push_cast; ring⟩
  · -- `D = 0`: then `B C = -1`, so `C = ±1` and `u.re = A C`
    have hD0r : D = 0 := by rw [hDi, hD0int]; norm_num
    have hBC : B * C = -1 := by have := hdet; rw [hD0r] at this; linarith
    have hBCint' : γ 0 1 * γ 1 0 = -1 := by
      have hR : (((γ 0 1 * γ 1 0) : ℤ) : ℝ) = -1 := by
        have h := hBC; rw [hBi, hCi] at h; push_cast at h ⊢; exact h
      exact_mod_cast hR
    have hBCint : γ 1 0 * γ 0 1 = -1 := by simpa [mul_comm (γ 0 1) (γ 1 0)] using hBCint'
    have hc : γ 1 0 = 1 ∨ γ 1 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_neg_one hBCint
    have hC2 : C ^ 2 = 1 := by rcases hc with hc | hc <;> rw [hCi, hc] <;> norm_num
    have hxr : u.re = A * C := by
      have hh := hx
      rw [hD0r, hC2] at hh
      ring_nf at hh
      nlinarith [hh, pow_pos ht 2]
    exact ⟨γ 0 0 * γ 1 0, by rw [hxr, hAi, hCi]; push_cast; ring⟩

theorem jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half (u : UpperHalfPlane)
    (hre : u.re ∉ Set.range (fun n : ℤ => (n : ℝ))) (him : (1 / 2 : ℝ) < u.im)
    {t : ℝ} (ht : 0 < t) :
    Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro h
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  exact hre (re_mem_intRange_of_smul_imagAxis γ t ht u hγ him)

end Work.Asymptotics.NonCoincidence
