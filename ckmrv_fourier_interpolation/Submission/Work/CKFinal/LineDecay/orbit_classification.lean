import Mathlib

/-!
# Classification of the `SL(2,ℤ)`-orbit points of the lines `Re τ = ±1/2`

A point `τ ∈ ℍ` with `Re τ = ±1/2` and `Im τ ≥ 12` lies far above the fundamental domain of
`SL(2,ℤ)`.  If an `SL(2,ℤ)`-translate `γ • τ` lands in the strip `-1 ≤ Re ≤ 1` (the horizontal
range containing the fundamental domain) and still has height at least `1`, then `γ` must be an
upper-triangular element, i.e. a translation: the lower-left entry `γ 1 0` vanishes.

Indeed the height of `γ • τ = (aτ+b)/(cτ+d)` is `Im τ / ‖cτ+d‖²`, and
`‖cτ+d‖² ≥ (c Im τ)² ≥ Im τ²` for `c ≠ 0`; a height `≥ 1` therefore forces `c = 0`, because
`Im τ ≥ 12 > 1`.  With `c = 0` the determinant gives `a·d = 1`, so `a = d = ±1` and the Möbius
action is a translation `τ ↦ τ + a·b`.  The constraint `-1 ≤ Re(γ • τ) ≤ 1` together with
`Re τ = ±1/2` then pins the translation to `0` or `∓1`, which is the claim.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- The Möbius action of an element `γ` with vanishing lower-left entry `γ 1 0 = 0` is the
translation `τ ↦ τ + γ 0 0 · γ 0 1` (the determinant gives `γ 0 0 = γ 1 1 = ±1`). -/
lemma smul_eq_vadd_of_apply_one_zero_eq_zero (τ : UpperHalfPlane)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : γ 1 0 = 0) :
    (γ • τ : UpperHalfPlane) = ((γ 0 0 * γ 0 1 : ℤ) : ℝ) +ᵥ τ := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [hc, mul_zero, sub_zero] at h
    exact h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_specialLinearGroup_apply, ha, hd, hc]
    norm_num
    ring
  · apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_specialLinearGroup_apply, ha, hd, hc]
    norm_num
    ring

theorem orbit_classification (τ : UpperHalfPlane) (hre : τ.re = 1/2 ∨ τ.re = -1/2) (him : 12 ≤ τ.im)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : 1 ≤ (γ • τ).im) (hre₁ : -1 ≤ (γ • τ).re)
    (hre₂ : (γ • τ).re ≤ 1) :
    (γ • τ) = τ ∨ (γ • τ) = ((-1:ℝ)+ᵥτ) ∨ (γ • τ) = ((1:ℝ)+ᵥτ) := by
  have hypos : 0 < τ.im := τ.im_pos
  -- The lower-left entry of `γ` must vanish: otherwise the height of `γ • τ` is too small.
  have hc : γ 1 0 = 0 := by
    by_contra hc
    -- Height bound: `1 ≤ Im(γ • τ) = Im τ / ‖denom‖²` gives `‖denom‖² ≤ Im τ`.
    have hNle :
        Complex.normSq (UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ))
          (↑τ)) ≤ τ.im := by
      have h1 := hγ
      rw [ModularGroup.im_smul_eq_div_normSq] at h1
      rw [le_div_iff₀ (Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero _ τ))] at h1
      linarith
    -- `‖denom‖² ≥ (γ 1 0 · Im τ)²`.
    have hbound :
        (((γ 1 0 : ℤ) : ℝ) * τ.im)^2 ≤
          Complex.normSq (UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ))
            (↑τ)) := by
      have hb := UpperHalfPlane.c_mul_im_sq_le_normSq_denom
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) τ
      simpa using hb
    have hmain : (((γ 1 0 : ℤ) : ℝ) * τ.im)^2 ≤ τ.im := le_trans hbound hNle
    -- Since the integer `γ 1 0` is nonzero, its square is at least `1`.
    have hcsq : (1:ℝ) ≤ ((γ 1 0 : ℤ) : ℝ)^2 := by
      rcases lt_or_gt_of_ne hc with h | h
      · have h2 : ((γ 1 0 : ℤ) : ℝ) ≤ -1 := by
          have : γ 1 0 ≤ -1 := by omega
          exact_mod_cast this
        nlinarith
      · have h2 : (1:ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) := by
          have : (1:ℤ) ≤ γ 1 0 := by omega
          exact_mod_cast this
        nlinarith
    have hy2 : τ.im^2 ≤ (((γ 1 0 : ℤ) : ℝ) * τ.im)^2 := by
      rw [mul_pow]
      nlinarith [hcsq, sq_nonneg τ.im]
    have hsq : τ.im^2 ≤ τ.im := le_trans hy2 hmain
    have hle1 : τ.im ≤ 1 := by
      by_contra h
      rw [not_le] at h
      nlinarith [mul_pos hypos (by linarith : (0:ℝ) < τ.im - 1)]
    linarith
  -- With `γ 1 0 = 0` the action is a translation `τ ↦ τ + m`, `m = γ 0 0 · γ 0 1 ∈ ℤ`.
  let m : ℤ := γ 0 0 * γ 0 1
  have hγeq : (γ • τ) = (m : ℝ) +ᵥ τ :=
    smul_eq_vadd_of_apply_one_zero_eq_zero τ γ hc
  rw [hγeq] at hre₁ hre₂
  rw [UpperHalfPlane.vadd_re] at hre₁ hre₂
  rw [hγeq]
  rcases hre with hre | hre
  · -- `Re τ = 1/2`: the translation is `0` or `-1`.
    have hm0 : m = 0 ∨ m = -1 := by
      have hle : (m:ℝ) ≤ 1/2 := by linarith [hre₂, hre]
      have hge : -(3:ℝ)/2 ≤ (m:ℝ) := by linarith [hre₁, hre]
      have h1 : m ≤ 0 := by
        by_contra h
        rw [not_le] at h
        have h2 : (1:ℤ) ≤ m := by omega
        have h3 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h2
        linarith
      have h2 : -1 ≤ m := by
        by_contra h
        rw [not_le] at h
        have h3 : m ≤ -2 := by omega
        have h4 : (m:ℝ) ≤ -2 := by exact_mod_cast h3
        linarith
      omega
    rcases hm0 with h | h
    · left; rw [h]; simp
    · right; left; rw [h]; norm_num
  · -- `Re τ = -1/2`: the translation is `0` or `1`.
    have hm0 : m = 0 ∨ m = 1 := by
      have hle : (m:ℝ) ≤ 3/2 := by linarith [hre₂, hre]
      have hge : -(1:ℝ)/2 ≤ (m:ℝ) := by linarith [hre₁, hre]
      have h1 : m ≤ 1 := by
        by_contra h
        rw [not_le] at h
        have h2 : (2:ℤ) ≤ m := by omega
        have h3 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast h2
        linarith
      have h2 : 0 ≤ m := by
        by_contra h
        rw [not_le] at h
        have h3 : m ≤ -1 := by omega
        have h4 : (m:ℝ) ≤ -1 := by exact_mod_cast h3
        linarith
      omega
    rcases hm0 with h | h
    · left; rw [h]; simp
    · right; right; rw [h]; norm_num

end Work.CKFinal.LineDecay
