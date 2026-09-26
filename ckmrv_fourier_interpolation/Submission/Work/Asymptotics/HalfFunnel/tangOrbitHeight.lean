/-
# The height bound on the orbit of a point of the closed tangency region

Every point of the orbit of `τ ∈ ctanCl` has height `< 3/2`, so the cut at `t = 3/2` lies
strictly above all the poles of `z ↦ K(τ,z)`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs

open UpperHalfPlane ModularGroup

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics.HalfFunnel

noncomputable section

/-- Membership in `ctanCl` gives `Im τ ∈ [1/2,5/8]`. -/
lemma ctanCl_im_bounds (τ : ℍ) (hτ : τ ∈ ctanCl) :
    (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 5 / 8 := ⟨hτ.1, hτ.2.1⟩

/-- Membership in `ctanCl` gives `|Re τ| ∈ [3/8,5/8]`. -/
lemma ctanCl_abs_re_bounds (τ : ℍ) (hτ : τ ∈ ctanCl) :
    3 / 8 ≤ |τ.re| ∧ |τ.re| ≤ 5 / 8 := by
  obtain ⟨-, -, -, -, hb⟩ := hτ
  have hreP : |τ.re - 1 / 2| ≤ ‖(τ : ℂ) - ctanP‖ := by
    have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
    rwa [show ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 by simp [ctanP, Complex.sub_re]] at h
  have hreM : |τ.re + 1 / 2| ≤ ‖(τ : ℂ) - ctanM‖ := by
    have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
    rwa [show ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 by simp [ctanM, Complex.sub_re]] at h
  have hb' : (3 / 8 ≤ τ.re ∧ τ.re ≤ 5 / 8) ∨ (-(5 / 8) ≤ τ.re ∧ τ.re ≤ -(3 / 8)) := by
    rcases hb with hbP | hbM
    · have h := abs_le.mp (le_trans hreP hbP)
      exact Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩
    · have h := abs_le.mp (le_trans hreM hbM)
      exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩
  rcases hb' with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · have h0 : (0 : ℝ) ≤ τ.re := by linarith
    rw [abs_of_nonneg h0]; exact ⟨hlo, hhi⟩
  · have h0 : τ.re ≤ 0 := by linarith
    rw [abs_of_nonpos h0]; exact ⟨by linarith, by linarith⟩

/-- An integer translate of a real number in `±[3/8,5/8]` stays at distance `≥ 3/8` from `0`. -/
lemma int_shift_abs {v : ℝ} (h1 : 3 / 8 ≤ |v|) (h2 : |v| ≤ 5 / 8) (m : ℤ) :
    3 / 8 ≤ |v + (m : ℝ)| := by
  rcases le_or_gt 0 v with hv | hv
  · have hv1 : 3 / 8 ≤ v := by rwa [abs_of_nonneg hv] at h1
    have hv2 : v ≤ 5 / 8 := by rwa [abs_of_nonneg hv] at h2
    rcases le_or_gt 0 (m : ℝ) with hm | hm
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have hm1 : (m : ℝ) ≤ -1 := by
        have hm0 : m < 0 := by exact_mod_cast hm
        have : m ≤ -1 := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
  · have hv1 : 3 / 8 ≤ -v := by rwa [abs_of_neg hv] at h1
    have hv2 : -v ≤ 5 / 8 := by rwa [abs_of_neg hv] at h2
    rcases le_or_gt (m : ℝ) 0 with hm | hm
    · rw [abs_of_nonpos (by linarith)]; linarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        have hm0 : 0 < m := by exact_mod_cast hm
        have : (1 : ℤ) ≤ m := by omega
        exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; linarith

/-- The real-arithmetic core of the height bound. -/
lemma height_aux {X Y : ℝ} (hY1 : (1 : ℝ) / 2 ≤ Y) (hY2 : Y ≤ 5 / 8)
    (hX : 3 / 8 ≤ |X|) : Y / (X ^ 2 + Y ^ 2) < 3 / 2 := by
  have hYpos : 0 < Y := by linarith
  have hX2 : (3 / 8 : ℝ) ^ 2 ≤ X ^ 2 := by nlinarith [abs_nonneg X, sq_abs X, hX]
  have h1 : Y / (X ^ 2 + Y ^ 2) ≤ Y / ((3 / 8 : ℝ) ^ 2 + Y ^ 2) := by
    apply div_le_div_of_nonneg_left hYpos.le (by positivity) (by linarith)
  have h2 : Y / ((3 / 8 : ℝ) ^ 2 + Y ^ 2) ≤ 32 / 25 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Y - 1 / 2), hY1]
  linarith

/-- **Every point of the orbit of `τ ∈ ctanCl` has height `< 3/2`.** -/
theorem tangOrbitHeight (τ : ℍ) (hτ : τ ∈ ctanCl)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : (γ • τ).im < 3 / 2 := by
  obtain ⟨hY1, hY2⟩ := ctanCl_im_bounds τ hτ
  obtain ⟨hre1, hre2⟩ := ctanCl_abs_re_bounds τ hτ
  set c : ℤ := γ 1 0 with hc
  set d : ℤ := γ 1 1 with hd
  set X : ℝ := (c : ℝ) * τ.re + (d : ℝ) with hXdef
  set D : ℝ := ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 + ((c : ℝ) * τ.im) ^ 2 with hDdef
  have him : (γ • τ).im = τ.im / D := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    have hD' : ((↑(γ 1 0) : ℂ) * ↑τ + ↑(γ 1 1)) = ((c : ℝ) : ℂ) * (τ : ℂ) + ((d : ℝ) : ℂ) := by
      rw [hc, hd]; push_cast; ring
    rw [hD', Complex.normSq_apply, hDdef]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [him]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.2
    rwa [Matrix.det_fin_two] at h
  rcases eq_or_ne c 0 with hc0 | hcne
  · -- `c = 0`: the determinant forces `|d| = 1`, so `D = 1`
    have hd1 : d = 1 ∨ d = -1 := by
      have h : γ 0 0 * d = 1 := by
        rw [← hd, ← hc, hc0] at hdet
        simpa using hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inl h2
      · exact Or.inr h2
    have hD1 : D = 1 := by
      rw [hDdef, hc0]
      rcases hd1 with h | h <;> rw [h] <;> norm_num
    have hDge : 1 ≤ D := by rw [hD1]
    have : τ.im / D ≤ τ.im / 1 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hDge
    linarith
  · rcases le_or_gt 2 |(c : ℝ)| with hc2 | hc2
    · -- `|c| ≥ 2`: the denominator is at least `1`
      have hDge : 1 ≤ D := by
        have hcs : (2 : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 := by
          nlinarith [abs_nonneg (c : ℝ), sq_abs (c : ℝ), hc2]
        have hYsq : ((1 : ℝ) / 2) ^ 2 ≤ τ.im ^ 2 := by nlinarith [hY1]
        have hmul : (2 : ℝ) ^ 2 * (1 / 2) ^ 2 ≤ (c : ℝ) ^ 2 * τ.im ^ 2 :=
          mul_le_mul hcs hYsq (by norm_num) (by positivity)
        have hterm : ((c : ℝ) * τ.im) ^ 2 = (c : ℝ) ^ 2 * τ.im ^ 2 := by ring
        rw [hDdef]
        nlinarith [hmul, hterm, sq_nonneg ((c : ℝ) * τ.re + (d : ℝ))]
      have : τ.im / D ≤ τ.im / 1 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hDge
      linarith
    · -- `|c| = 1`: `X` stays `3/8` away from `0` and `D = X² + Im²τ`
      have hcm : (c : ℝ) = 1 ∨ (c : ℝ) = -1 := by
        have hcint : c = 1 ∨ c = -1 ∨ c = 0 := by
          have h1 : (c : ℝ) < 2 := (abs_lt.mp hc2).2
          have h2 : -(2 : ℝ) < (c : ℝ) := (abs_lt.mp hc2).1
          have h1' : c < 2 := by exact_mod_cast h1
          have h2' : (-2 : ℤ) < c := by exact_mod_cast h2
          omega
        rcases hcint with h | h | h
        · exact Or.inl (by rw [h]; norm_num)
        · exact Or.inr (by rw [h]; norm_num)
        · exact absurd h hcne
      have hX3 : 3 / 8 ≤ |X| := by
        rw [hXdef]
        rcases hcm with h1 | h1
        · have he : (c : ℝ) * τ.re + (d : ℝ) = τ.re + (d : ℝ) := by rw [h1]; ring
          rw [he]; exact int_shift_abs hre1 hre2 d
        · have he : (c : ℝ) * τ.re + (d : ℝ) = -τ.re + (d : ℝ) := by rw [h1]; ring
          rw [he]
          have h := int_shift_abs (v := -τ.re) (by rwa [abs_neg]) (by rwa [abs_neg]) d
          simpa using h
      have hDsq : D = X ^ 2 + τ.im ^ 2 := by
        rw [hDdef, hXdef]
        rcases hcm with h1 | h1 <;> rw [h1] <;> ring
      rw [hDsq]
      exact height_aux hY1 hY2 hX3

end

end Work.Asymptotics.HalfFunnel
