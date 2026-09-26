import Mathlib
import Submission.Work.Asymptotics.Basic
import Submission.Work.Kernels.All

namespace Work.Asymptotics

open scoped UpperHalfPlane

/-! ## The stabiliser of the positive imaginary axis is `{±I, ±S}`

We show that if `γ ∈ SL(2,ℤ)` carries the point `it` (`t > 0`) of the positive imaginary axis
to another point `iu` (`u > 0`) of that axis, then `γ ∈ {1, -1, S, -S}`.

The argument is elementary and completely algebraic.  Writing `γ = !![a,b;c,d]`, the two
complex equations obtained by taking the real and imaginary parts of `γ • (it) = iu` read

* `a * t = u * d`   (imaginary parts),
* `b = -u * c * t`  (real parts).

Together with `a * d - b * c = 1` these force `(a,b,c,d)` to be one of
`(1,0,0,1)`, `(-1,0,0,-1)`, `(0,-1,1,0)`, `(0,1,-1,0)`. -/

/-- The real and imaginary parts of the equation `γ • (it) = iu`, for `γ = !![a,b;c,d]`.
These are the two numerical relations from which the classification of `γ` is deduced. -/
private lemma entries_of_smul_imagAxis {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u)
    (h : γ • Work.Kernels.imagAxis t ht = Work.Kernels.imagAxis u hu) :
    ((γ 0 0 : ℤ) : ℝ) * t = u * ((γ 1 1 : ℤ) : ℝ) ∧
    ((γ 0 1 : ℤ) : ℝ) = -u * ((γ 1 0 : ℤ) : ℝ) * t := by
  -- Compare the two points of `ℍ` as complex numbers.
  have hcoe : ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) =
      ((Work.Kernels.imagAxis u hu : ℍ) : ℂ) := by rw [h]
  -- Insert the fractional-linear expression for the action and the explicit value of `it`.
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
  simp only [Work.Kernels.imagAxis] at hcoe
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  simp only [hcast] at hcoe
  -- The denominator does not vanish: otherwise the bottom row of `γ` would be zero, which
  -- is incompatible with `det γ = 1`.
  have hden : ((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at hre him
    have h11 : γ 1 1 = 0 := by
      have hh : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using hre
      exact_mod_cast hh
    have h10 : γ 1 0 = 0 := by
      have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
      have hh : ((γ 1 0 : ℤ) : ℝ) * t = 0 := by simpa using him
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hh).resolve_right ht0
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [h10, h11] at hdet
    norm_num at hdet
  -- Clear denominators and read off the real and imaginary parts.
  have hmain : ((γ 0 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 0 1 : ℤ) : ℂ) =
      (u : ℂ) * Complex.I *
        (((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ)) :=
    (div_eq_iff hden).mp hcoe
  have hre := congrArg Complex.re hmain
  have him := congrArg Complex.im hmain
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_sub, zero_add] at hre him
  constructor
  · simpa using him
  · show ((γ 0 1 : ℤ) : ℝ) = -u * ((γ 1 0 : ℤ) : ℝ) * t
    rw [hre]; ring

/-- **The algebraic heart of the classification.**  Let `a b c d ∈ ℤ` and `t u ∈ ℝ` satisfy
`a·t = u·d`, `b = -u·c·t` and `a·d - b·c = 1`.  Then `(a,b,c,d)` is one of the four sign
patterns of the identity and of `S = !![0,-1;1,0]`.

The key point is that the three relations give `u·(d² + c²t²) = t`; hence `0 ≤ a·d ≤ 1`, so the
integer `a·d` is `0` or `1`, and the remainder is a short case analysis. -/
private lemma int_classification {a b c d : ℤ} {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hA : (a : ℝ) * t = u * (d : ℝ))
    (hB : (b : ℝ) = -u * (c : ℝ) * t)
    (hdet : a * d - b * c = 1) :
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) ∨
    (a = 0 ∧ b = -1 ∧ c = 1 ∧ d = 0) ∨ (a = 0 ∧ b = 1 ∧ c = -1 ∧ d = 0) := by
  have hdetR : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet
  have hADt : (a : ℝ) * (d : ℝ) * t = u * (d : ℝ) ^ 2 := by
    linear_combination (d : ℝ) * hA
  have hBCt : (b : ℝ) * (c : ℝ) * t + u * (c : ℝ) ^ 2 * t ^ 2 = 0 := by
    linear_combination ((c : ℝ) * t) * hB
  have h3' : (a : ℝ) * (d : ℝ) * t - (b : ℝ) * (c : ℝ) * t = t := by
    have h3 : ((a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ)) * t = t := by rw [hdetR]; ring
    linear_combination h3
  -- `u (d² + c² t²) = t`
  have hmain : u * ((d : ℝ) ^ 2 + (c : ℝ) ^ 2 * t ^ 2) = t := by
    linear_combination h3' - hADt + hBCt
  -- hence `0 ≤ a·d ≤ 1`
  have hADle : (a : ℝ) * (d : ℝ) ≤ 1 := by
    have hcsq : 0 ≤ u * ((c : ℝ) ^ 2 * t ^ 2) :=
      mul_nonneg hu.le (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have huD2 : u * (d : ℝ) ^ 2 ≤ t := by nlinarith [hmain, hcsq]
    have hle' : (a : ℝ) * (d : ℝ) * t ≤ 1 * t := by linarith [hADt, huD2]
    exact le_of_mul_le_mul_right hle' ht
  have hADge : 0 ≤ (a : ℝ) * (d : ℝ) := by
    have hnonneg : 0 ≤ u * (d : ℝ) ^ 2 := mul_nonneg hu.le (sq_nonneg _)
    have hge' : 0 * t ≤ (a : ℝ) * (d : ℝ) * t := by linarith [hADt, hnonneg]
    exact le_of_mul_le_mul_right hge' ht
  have hleZ : a * d ≤ 1 := by exact_mod_cast hADle
  have hgeZ : 0 ≤ a * d := by exact_mod_cast hADge
  rcases (show a * d = 0 ∨ a * d = 1 by omega) with had | had
  · -- `a·d = 0`, so `b·c = -1`; the relations force `a = d = 0` and `(b,c) = ±(1,-1)`.
    have hbc : b * c = -1 := by omega
    have had0 : a = 0 ∧ d = 0 := by
      rcases mul_eq_zero.mp had with ha | hd
      · refine ⟨ha, ?_⟩
        have hh := hA
        rw [ha] at hh
        have h1 : u * (d : ℝ) = 0 := by simpa using hh.symm
        have h2 : (d : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_left (ne_of_gt hu)
        exact_mod_cast h2
      · refine ⟨?_, hd⟩
        have hh := hA
        rw [hd] at hh
        have h1 : (a : ℝ) * t = 0 := by simpa using hh
        have h2 : (a : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right (ne_of_gt ht)
        exact_mod_cast h2
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inr (Or.inr (Or.inr ⟨had0.1, hb, hc, had0.2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨had0.1, hb, hc, had0.2⟩))
  · -- `a·d = 1`, so `b·c = 0`; the relations force `b = c = 0` and `(a,d) = ±(1,1)`.
    have hbc : b * c = 0 := by omega
    have hbc0 : b = 0 ∧ c = 0 := by
      rcases mul_eq_zero.mp hbc with hb | hc
      · refine ⟨hb, ?_⟩
        have hh := hB
        rw [hb] at hh
        simp only [Int.cast_zero] at hh
        have h1 : u * (c : ℝ) * t = 0 := by linarith [hh]
        have h2 : (c : ℝ) = 0 := by
          rcases mul_eq_zero.mp h1 with h3 | h3
          · exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hu)
          · exact absurd h3 (ne_of_gt ht)
        exact_mod_cast h2
      · refine ⟨?_, hc⟩
        have hh := hB
        rw [hc] at hh
        have h1 : (b : ℝ) = 0 := by simpa using hh
        exact_mod_cast h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · exact Or.inl ⟨ha, hbc0.1, hbc0.2, hd⟩
    · exact Or.inr (Or.inl ⟨ha, hbc0.1, hbc0.2, hd⟩)

/-- Entrywise recognition of `1 ∈ SL(2,ℤ)`. -/
private lemma eq_one_of_entries {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h00 : γ 0 0 = 1) (h01 : γ 0 1 = 0) (h10 : γ 1 0 = 0) (h11 : γ 1 1 = 1) : γ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.SpecialLinearGroup.coe_one]

/-- Entrywise recognition of `-1 ∈ SL(2,ℤ)`. -/
private lemma eq_neg_one_of_entries {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h00 : γ 0 0 = -1) (h01 : γ 0 1 = 0) (h10 : γ 1 0 = 0) (h11 : γ 1 1 = -1) :
    γ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg]

/-- Entrywise recognition of `S ∈ SL(2,ℤ)`. -/
private lemma eq_S_of_entries {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h00 : γ 0 0 = 0) (h01 : γ 0 1 = -1) (h10 : γ 1 0 = 1) (h11 : γ 1 1 = 0) :
    γ = ModularGroup.S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [ModularGroup.coe_S]

/-- Entrywise recognition of `-S ∈ SL(2,ℤ)`. -/
private lemma eq_neg_S_of_entries {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h00 : γ 0 0 = 0) (h01 : γ 0 1 = 1) (h10 : γ 1 0 = -1) (h11 : γ 1 1 = 0) :
    γ = -ModularGroup.S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_S, Matrix.SpecialLinearGroup.coe_neg]

/-- The positive imaginary axis meets each `SL(2,ℤ)`-orbit only in the points fixed by
`I` and `S`: if `γ • (it) = iu` with `t, u > 0` then `γ ∈ {±I, ±S}`.  This is the geometric
fact that makes the contour `{it : t > 0}` free of *non-removable* poles for the CKMRV kernels
(the poles at `τ = it` and `τ = i/t` have vanishing residues because `φ(I) = φ(S) = 0`). -/
theorem eq_one_or_neg_one_or_S_of_smul_imagAxis {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (h : γ • Work.Kernels.imagAxis t ht = Work.Kernels.imagAxis u hu) :
    γ = 1 ∨ γ = -1 ∨ γ = ModularGroup.S ∨ γ = -ModularGroup.S := by
  obtain ⟨hA, hB⟩ := entries_of_smul_imagAxis ht hu h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hh := γ.2
    rw [Matrix.det_fin_two] at hh
    exact hh
  rcases int_classification ht hu hA hB hdet with
    ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ |
      ⟨h00, h01, h10, h11⟩
  · exact Or.inl (eq_one_of_entries h00 h01 h10 h11)
  · exact Or.inr (Or.inl (eq_neg_one_of_entries h00 h01 h10 h11))
  · exact Or.inr (Or.inr (Or.inl (eq_S_of_entries h00 h01 h10 h11)))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_S_of_entries h00 h01 h10 h11)))

end Work.Asymptotics
