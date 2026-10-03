import Mathlib
import Submission.Work.FatouL1.existsLeSinSqOnIcc
import Submission.Work.FatouL1.normSqSinComplex
import Submission.Work.FatouL1.normSqCosComplex

/-!
# Boundedness of `2π² · cos (π ·) / sin (π ·)^3` on a vertical strip inside `(-1,0)`

For real `p q` with `-1 < p` and `q < 0` the vertical strip
`{s : ℂ | p ≤ Re s ≤ q}` is contained in `(-1, 0) × ℝ`, which contains no pole of
`sin (π ·)` (the poles are the integers).  Writing `s = x + iy` and using

  `‖sin (π s)‖² = sin (π x)² + sinh (π y)²`,  `‖cos (π s)‖² = cos (π x)² + sinh (π y)²`,

the squared modulus of the quotient equals `(cos (π x)² + u)/(sin (π x)² + u)³`
with `u = sinh (π y)²`.  Since `sin (π x)²` admits a positive lower bound `m` on the
compact interval `[p,q]`, and `m ≤ 1`, one shows `m⁶ (1 + u) ≤ (m + u)³`, which yields
the uniform bound `‖cos‖/‖sin‖³ ≤ 1/m³` (independently of `y`).  Hence
`C = 2π²/m³` works.
-/

namespace Work.FatouL1

theorem existsNormCosDivSinCubeLe {p q : ℝ} (hp : -1 < p) (hq : q < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Set.Icc p q →
      ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * s) /
        (Complex.sin (Real.pi * s)) ^ 3‖ ≤ C := by
  obtain ⟨m, hm0, hm1, hm⟩ := existsLeSinSqOnIcc hp hq
  refine ⟨2 * Real.pi ^ 2 / m ^ 3, by positivity, ?_⟩
  intro s hs
  have hnorm : ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * s) /
      (Complex.sin (Real.pi * s)) ^ 3‖
      = 2 * Real.pi ^ 2 *
        (‖Complex.cos (Real.pi * s)‖ / ‖Complex.sin (Real.pi * s)‖ ^ 3) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    rw [Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    ring
  rw [hnorm]
  set A := ‖Complex.cos (Real.pi * s)‖ with hA
  set B := ‖Complex.sin (Real.pi * s)‖ with hB
  set u := Real.sinh (Real.pi * s).im ^ 2 with hu
  set c := Real.cos (Real.pi * s).re with hc
  set sn := Real.sin (Real.pi * s).re with hsn
  have hre : (Real.pi * s).re = Real.pi * s.re := by simp
  have hcos : A ^ 2 = c ^ 2 + u := by
    rw [hA, hc, hu]; exact normSqCosComplex _
  have hsin : B ^ 2 = sn ^ 2 + u := by
    rw [hB, hsn, hu]; exact normSqSinComplex _
  have hs2 : m ≤ sn ^ 2 := by rw [hsn, hre]; exact hm s.re hs
  have hcs : c ^ 2 + sn ^ 2 = 1 := by rw [hc, hsn]; exact Real.cos_sq_add_sin_sq _
  have hunn : 0 ≤ u := by rw [hu]; positivity
  -- the crux: `m⁶ (1 + u) ≤ (m + u)³` for `0 < m ≤ 1`, `u ≥ 0`
  have hkey : m ^ 6 * (1 + u) ≤ (m + u) ^ 3 := by
    have hm6 : m ^ 6 ≤ m ^ 3 := by
      have := pow_le_pow_of_le_one hm0.le hm1 (by norm_num : (3:ℕ) ≤ 6)
      simpa using this
    have h1 : m ^ 6 * (1 + u) ≤ m ^ 3 * (1 + u) :=
      mul_le_mul_of_nonneg_right hm6 (by positivity)
    have key : (m + u) ^ 3 - m ^ 3 * (1 + u) = u * (m ^ 2 * (3 - m) + 3 * m * u + u ^ 2) := by
      ring
    have hbracket : 0 ≤ m ^ 2 * (3 - m) + 3 * m * u + u ^ 2 := by
      nlinarith [hm0, hm1, hunn, sq_nonneg m, sq_nonneg u]
    have h2 : m ^ 3 * (1 + u) ≤ (m + u) ^ 3 := by
      nlinarith [key, mul_nonneg hunn hbracket]
    linarith [h1, h2]
  have hSq : (m ^ 3 * A) ^ 2 ≤ (B ^ 3) ^ 2 := by
    have hA2 : A ^ 2 ≤ 1 + u := by nlinarith [hcos, hcs, sq_nonneg sn]
    have hB2 : m + u ≤ B ^ 2 := by nlinarith [hsin, hs2]
    calc (m ^ 3 * A) ^ 2 = m ^ 6 * A ^ 2 := by ring
      _ ≤ m ^ 6 * (1 + u) := mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ ≤ (m + u) ^ 3 := hkey
      _ ≤ (B ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hB2 3
      _ = (B ^ 3) ^ 2 := by ring
  have hmain : m ^ 3 * A ≤ B ^ 3 := by
    have hX : 0 ≤ m ^ 3 * A := by positivity
    have hY : 0 ≤ B ^ 3 := by positivity
    have := Real.sqrt_le_sqrt hSq
    rwa [Real.sqrt_sq hX, Real.sqrt_sq hY] at this
  have hBsq : 0 < B ^ 2 := by nlinarith [hsin, hs2, hm0, hunn]
  have hBpos : 0 < B ^ 3 := by
    have hBnn : 0 ≤ B := by rw [hB]; exact norm_nonneg _
    have hBp : 0 < B := by nlinarith [hBsq, hBnn]
    exact pow_pos hBp 3
  have hratio : A / B ^ 3 ≤ 1 / m ^ 3 := by
    rw [div_le_div_iff₀ hBpos (by positivity)]
    nlinarith [hmain]
  calc 2 * Real.pi ^ 2 * (A / B ^ 3)
      ≤ 2 * Real.pi ^ 2 * (1 / m ^ 3) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2 * Real.pi ^ 2 / m ^ 3 := by ring

end Work.FatouL1
