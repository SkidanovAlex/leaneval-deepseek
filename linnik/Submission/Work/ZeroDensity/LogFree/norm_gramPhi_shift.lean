import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramResidueDefs
import Submission.Work.ZeroDensity.LogFree.principalImagAxisBound

namespace Work.ZeroDensity.LogFree

/-- **The shifted `gramPhi` bound.**  On the vertical line `Re z = Re s = δ ∈ (-1,0)` the
integrand `gramPhi = Γ(z)(X^z - U'^z)·ζ(z-s)·gramA(z)` splits into
`|Γ(z)|·|X^z - U'^z|·|ζ(z-s)|·|gramA(z)|`, and each factor is bounded: `|Γ|` is kept,
`|X^z - U'^z| ≤ X^δ + U'^δ`, `|gramA| ≤ (2W)^2`, while `z - s = i(t - Im s)` is purely imaginary
so that the convexity bound `‖ζ(iy)‖ ≤ C(2+|y|)^{1/2+η}` (`zetaImagAxisBound`) applies. -/
theorem norm_gramPhi_shift (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W X U' : ℝ) (s : ℂ), 1 < W → 0 < X → 0 < U' → -1 < s.re → s.re < 0 →
      ∀ t : ℝ, ‖Work.ZeroDensity.LogFree.gramPhi W X U' s (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η)
          * ‖Complex.Gamma (((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by
  obtain ⟨Cζ, hCζpos, hCζ⟩ := zetaImagAxisBound η hη
  refine ⟨Cζ, hCζpos, ?_⟩
  intro W X U' s hW hX hU' hsre1 hsre0 t
  set z : ℂ := ((s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I with hzdef
  have hzre : z.re = s.re := by rw [hzdef]; simp
  have hzne : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re, hzre] at hre
    linarith
  have hzsub : z - s = ((t - s.im : ℝ) : ℂ) * Complex.I := by
    rw [hzdef]
    apply Complex.ext <;> simp
  have hgp : gammaPow X U' z = Complex.Gamma z * ((X : ℂ) ^ z - (U' : ℂ) ^ z) :=
    gammaPow_of_ne X U' hzne
  -- `|X^z - U'^z| ≤ X^δ + U'^δ`
  have hpow : ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖ ≤ X ^ (s.re) + U' ^ (s.re) := by
    have hXz := Complex.norm_cpow_eq_rpow_re_of_pos hX z
    have hUz := Complex.norm_cpow_eq_rpow_re_of_pos hU' z
    calc ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖ ≤ ‖(X : ℂ) ^ z‖ + ‖(U' : ℂ) ^ z‖ := norm_sub_le _ _
      _ = X ^ (s.re) + U' ^ (s.re) := by rw [hXz, hUz, hzre]
  -- `|ζ(z-s)| ≤ Cζ (2+|Im s|+|t|)^{1/2+η}`
  have htau : |t - s.im| ≤ |t| + |s.im| := by
    rw [sub_eq_add_neg]
    calc |t + -(s.im)| ≤ |t| + |-(s.im)| := abs_add_le _ _
      _ = |t| + |s.im| := by rw [abs_neg]
  have hzeta : ‖riemannZeta (z - s)‖ ≤ Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η) := by
    have h1 := hCζ (t - s.im)
    rw [hzsub]
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hCζpos.le)
    exact Real.rpow_le_rpow (by linarith [abs_nonneg (t - s.im)])
      (by linarith [htau]) (by linarith)
  -- `|gramA| ≤ (2W)^2`
  have hgramA : ‖gramA W s z‖ ≤ (2 * W) ^ 2 := by
    refine le_trans (norm_gramA_le W hW s z hzre) ?_
    have hceil : (Nat.ceil W : ℝ) < W + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (lt_trans one_pos hW))
    have hceil2 : (Nat.ceil W : ℝ) ≤ 2 * W := by linarith
    have h1 : 0 ≤ (Nat.ceil W : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * W := by linarith
    nlinarith [hceil2, h1, h2]
  -- assembly
  have hBnn : 0 ≤ X ^ (s.re) + U' ^ (s.re) :=
    add_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hU'.le _)
  have hSnn : 0 ≤ (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η) :=
    Real.rpow_nonneg (by linarith [abs_nonneg s.im, abs_nonneg t]) _
  have hAB : ‖Complex.Gamma z‖ * ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖
      ≤ ‖Complex.Gamma z‖ * (X ^ (s.re) + U' ^ (s.re)) :=
    mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hABnn : 0 ≤ ‖Complex.Gamma z‖ * (X ^ (s.re) + U' ^ (s.re)) :=
    mul_nonneg (norm_nonneg _) hBnn
  have hZnn : 0 ≤ Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η) :=
    mul_nonneg hCζpos.le hSnn
  have step1 : (‖Complex.Gamma z‖ * ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖) * ‖riemannZeta (z - s)‖
      ≤ (‖Complex.Gamma z‖ * (X ^ (s.re) + U' ^ (s.re)))
          * (Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η)) :=
    mul_le_mul hAB hzeta (norm_nonneg _) hABnn
  have step2 :
      ((‖Complex.Gamma z‖ * ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖) * ‖riemannZeta (z - s)‖)
          * ‖gramA W s z‖
      ≤ ((‖Complex.Gamma z‖ * (X ^ (s.re) + U' ^ (s.re)))
          * (Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η))) * (2 * W) ^ 2 :=
    mul_le_mul step1 hgramA (norm_nonneg _) (mul_nonneg hABnn hZnn)
  calc ‖gramPhi W X U' s z‖
      = ((‖Complex.Gamma z‖ * ‖(X : ℂ) ^ z - (U' : ℂ) ^ z‖) * ‖riemannZeta (z - s)‖)
          * ‖gramA W s z‖ := by
        rw [gramPhi, hgp, norm_mul, norm_mul, norm_mul]
    _ ≤ ((‖Complex.Gamma z‖ * (X ^ (s.re) + U' ^ (s.re)))
          * (Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η))) * (2 * W) ^ 2 := step2
    _ = Cζ * (2 + |s.im| + |t|) ^ ((1 : ℝ) / 2 + η) * ‖Complex.Gamma z‖
          * (X ^ (s.re) + U' ^ (s.re)) * (2 * W) ^ 2 := by ring

end Work.ZeroDensity.LogFree
