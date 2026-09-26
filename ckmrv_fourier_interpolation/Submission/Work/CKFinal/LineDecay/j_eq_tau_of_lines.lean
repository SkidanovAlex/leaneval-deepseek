/-
# The orbit classification on the two lines `Re τ = ±1/2, Im τ ≥ 3`

If `τ` lies on one of the two vertical lines `Re τ = ±1/2` with `Im τ ≥ 3` and
`ζ ∈ ℍ` satisfies `-1 ≤ Re ζ ≤ 1`, `Im ζ ≥ 1` and `j ζ = j τ`, then `ζ` is one of
`τ`, `τ - 1`, `τ + 1`.

The input is `Work.Asymptotics.jInvariantFun_eq_smul_of_eq` (equal `j`-values mean equal
`SL(2,ℤ)`-orbits): some `γ ∈ SL(2,ℤ)` carries `τ` to `ζ`.  Writing `γ = !![a,b;c,d]` we
have `Im ζ = Im τ / ‖c τ + d‖²`; since `‖c τ + d‖² ≥ (c · Im τ)²` and `Im ζ ≥ 1`,
`(c · Im τ)² ≤ Im τ`, and `Im τ ≥ 3` forces `c = 0`.  Then `a d = 1`, so `a = d = ±1` and
the Möbius map is the translation by `a b ∈ ℤ`; comparing real parts with
`-1 ≤ Re ζ ≤ 1` leaves the three possibilities above.
-/
import Mathlib
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- The norm-square of the denominator `c z + d` of the Möbius map `γ`, in coordinates. -/
private lemma normSq_denom_eq (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    Complex.normSq (UpperHalfPlane.denom
        (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
        (z : ℂ))
      = (((γ 1 0 : ℤ) : ℝ) * z.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2
        + (((γ 1 0 : ℤ) : ℝ) * z.im) ^ 2 := by
  rw [ModularGroup.denom_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem j_eq_tau_of_lines (τ ζ : UpperHalfPlane)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 3 ≤ τ.im)
    (hζa : -1 ≤ ζ.re) (hζb : ζ.re ≤ 1) (hζim : 1 ≤ ζ.im)
    (hj : Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun τ) :
    ζ = τ ∨ ζ = ((-1 : ℝ) +ᵥ τ) ∨ ζ = ((1 : ℝ) +ᵥ τ) := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  set D : ℂ := UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      (τ : ℂ) with hD
  have hNform : Complex.normSq D = (((γ 1 0 : ℤ) : ℝ) * τ.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2
      + (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by
    rw [hD]; exact normSq_denom_eq γ τ
  have himζ : ζ.im = τ.im / Complex.normSq D := by
    have h := ModularGroup.im_smul_eq_div_normSq γ τ
    rw [hγ] at h
    rw [hD]; exact h
  have hNne : Complex.normSq D ≠ 0 := by
    intro h0
    rw [h0, div_zero] at himζ
    linarith
  have hNpos : 0 < Complex.normSq D := lt_of_le_of_ne (Complex.normSq_nonneg D) (Ne.symm hNne)
  have hle : Complex.normSq D ≤ τ.im := by
    have h := hζim
    rw [himζ, le_div_iff₀ hNpos] at h
    simpa using h
  have hc2 : (((γ 1 0 : ℤ) : ℝ)) ^ 2 < 1 := by
    have hτpos : (0 : ℝ) < τ.im := by linarith
    have hN_ge : (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 ≤ Complex.normSq D := by
      rw [hNform]
      nlinarith [sq_nonneg (((γ 1 0 : ℤ) : ℝ) * τ.re + ((γ 1 1 : ℤ) : ℝ))]
    have hkey : (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 ≤ τ.im := le_trans hN_ge hle
    have hkey' : (((γ 1 0 : ℤ) : ℝ)) ^ 2 * τ.im ^ 2 ≤ τ.im := by nlinarith [hkey]
    have h3 : (((γ 1 0 : ℤ) : ℝ)) ^ 2 * τ.im ≤ 1 := by nlinarith [hkey', hτpos]
    have h4 : 3 * (((γ 1 0 : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      calc 3 * (((γ 1 0 : ℤ) : ℝ)) ^ 2 = (((γ 1 0 : ℤ) : ℝ)) ^ 2 * 3 := by ring
        _ ≤ (((γ 1 0 : ℤ) : ℝ)) ^ 2 * τ.im := mul_le_mul_of_nonneg_left him (sq_nonneg _)
        _ ≤ 1 := h3
    linarith
  have hc0 : γ 1 0 = 0 := by
    have hlt : (((γ 1 0 : ℤ)) ^ 2 : ℝ) < 1 := hc2
    have hlt' : (γ 1 0 : ℤ) ^ 2 < 1 := by exact_mod_cast hlt
    have hnn : (0 : ℤ) ≤ (γ 1 0) ^ 2 := sq_nonneg _
    have h0 : (γ 1 0 : ℤ) ^ 2 = 0 := by omega
    exact sq_eq_zero_iff.mp h0
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have had : γ 0 0 * γ 1 1 = 1 := by rw [hc0, mul_zero, sub_zero] at hdet; exact hdet
  have hmain : ((ζ : ℂ)) = (τ : ℂ) + (((γ 0 0) * (γ 0 1) : ℤ) : ℂ) := by
    have hγτ : ((ζ : ℂ)) = (((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) /
        (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
      rw [← hγ]
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [algebraMap_int_eq]
      simp
    have ha : γ 0 0 = 1 ∨ γ 0 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one had
    rcases ha with ha | ha
    · have hd : γ 1 1 = 1 := by rw [ha] at had; simpa using had
      rw [ha, hd, hc0] at hγτ
      rw [hγτ, ha]
      push_cast
      field_simp
      ring
    · have hd : γ 1 1 = -1 := by rw [ha] at had; omega
      rw [ha, hd, hc0] at hγτ
      rw [hγτ, ha]
      push_cast
      field_simp
      ring
  have hreζ : ζ.re = τ.re + (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) := by
    have h := congrArg Complex.re hmain
    simp only [Complex.add_re, UpperHalfPlane.coe_re, Complex.intCast_re] at h
    exact h
  rcases hre with hre | hre
  · have hn : (γ 0 0 * γ 0 1 = -1) ∨ (γ 0 0 * γ 0 1 = 0) := by
      have h1 : ζ.re = 1 / 2 + (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) := by rw [hreζ, hre]
      have h2 : (-2 : ℤ) < γ 0 0 * γ 0 1 := by
        have : (-2 : ℝ) < (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) := by linarith
        exact_mod_cast this
      have h3 : γ 0 0 * γ 0 1 < 1 := by
        have : (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) < 1 := by linarith
        exact_mod_cast this
      omega
    rcases hn with hn | hn
    · right; left
      apply UpperHalfPlane.ext
      rw [hmain, hn, UpperHalfPlane.coe_vadd]
      push_cast
      ring
    · left
      apply UpperHalfPlane.ext
      rw [hmain, hn]
      simp
  · have hn : (γ 0 0 * γ 0 1 = 0) ∨ (γ 0 0 * γ 0 1 = 1) := by
      have h1 : ζ.re = -1 / 2 + (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) := by rw [hreζ, hre]
      have h2 : (-1 : ℤ) < γ 0 0 * γ 0 1 := by
        have : (-1 : ℝ) < (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) := by linarith
        exact_mod_cast this
      have h3 : γ 0 0 * γ 0 1 < 2 := by
        have : (((γ 0 0) * (γ 0 1) : ℤ) : ℝ) < 2 := by linarith
        exact_mod_cast this
      omega
    rcases hn with hn | hn
    · left
      apply UpperHalfPlane.ext
      rw [hmain, hn]
      simp
    · right; right
      apply UpperHalfPlane.ext
      rw [hmain, hn, UpperHalfPlane.coe_vadd]
      push_cast
      ring

end Work.CKFinal.LineDecay
