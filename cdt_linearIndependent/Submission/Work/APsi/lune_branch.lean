import Mathlib
import Submission.Work.APsi.defs

/-!
# Area `Ψ_A`: the branch / baseline analysis of the lune radicand `luneR c`

This module isolates the *elementary* (real-algebraic) part of the analysis of the lune map

`lune c z = (z B - B + √(R z)) / (2 C)`,  `B = 1 + c²`, `C = c² - 1`,
`R z = luneR c z = B²(1+z)² - 16c²z`,

of Calegari--Dimitrov--Tang (arXiv:2408.15403, eq. `(firstgobble)`), for `c > 1`.

The key structural fact is the factorization

`R z = B² (z² - 2αz + 1)`,  `α = (8c² - B²)/B²`,

with `1 - α² = 16c²(c²-1)²/B⁴ > 0`: the quadratic in the bracket has two complex conjugate
roots of modulus `1`.  It follows that if `R z` is a nonpositive real, `R z = -s` with `s ≥ 0`,
then `z` is (at least) on the unit circle, `‖z‖² = 1 + s/B²`.  Consequently `R` avoids the
branch cut `(-∞,0]` on the closed unit disc, except that it may vanish there (at the two points
of the unit circle which are the critical values of the inverse map `luneF`).
-/

namespace Work.APsi

open Submission.CDTPlan Complex
open scoped ComplexConjugate

noncomputable section

/-- `α = (8c² - (1+c²)²)/(1+c²)²`, so that `luneR c z = B² (z² - 2αz + 1)`, `B = 1 + c²`. -/
noncomputable def luneAlpha (c : ℝ) : ℝ := (8 * c ^ 2 - (1 + c ^ 2) ^ 2) / (1 + c ^ 2) ^ 2

/-- `B² α = 8c² - B²` (division-free form of the definition of `α`). -/
theorem luneB_sq_mul_luneAlpha (c : ℝ) :
    luneB c ^ 2 * (luneAlpha c : ℂ) = ((8 * c ^ 2 - (1 + c ^ 2) ^ 2 : ℝ) : ℂ) := by
  have hB : (1 + (c : ℂ) ^ 2) ^ 2 ≠ 0 := by
    have h1 : (1 + (c : ℂ) ^ 2) = ((1 + c ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, pow_ne_zero_iff (by norm_num)]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [luneAlpha, luneB, luneBr]
  push_cast
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ hB

/-- **Factorization of the lune radicand**: `luneR c z = B²(z² - 2αz + 1)`. -/
theorem luneR_eq_factor (c : ℝ) (z : ℂ) :
    luneR c z = luneB c ^ 2 * (z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1) := by
  rw [show luneB c ^ 2 * (z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1)
      = luneB c ^ 2 * z ^ 2 - 2 * (luneB c ^ 2 * (luneAlpha c : ℂ)) * z + luneB c ^ 2 from by
        ring]
  rw [luneB_sq_mul_luneAlpha]
  simp only [luneR, luneB, luneBr]
  push_cast
  ring

theorem conj_luneB (c : ℝ) : conj (luneB c) = luneB c := by simp [luneB]

/-- `1 - α² = 16c²(c²-1)²/(1+c²)⁴`, in particular `α² < 1` for `c > 1` (`α = ±1` exactly at the
degenerate values `c = 0, 1`). -/
theorem one_sub_luneAlpha_sq_pos {c : ℝ} (hc : 1 < c) : 0 < 1 - luneAlpha c ^ 2 := by
  rw [show 1 - luneAlpha c ^ 2 = 16 * c ^ 2 * (c ^ 2 - 1) ^ 2 / (1 + c ^ 2) ^ 4 from by
    simp only [luneAlpha]; field_simp; ring]
  have h1 : (0 : ℝ) < c ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < c ^ 2 - 1 := by nlinarith
  have h3 : (0 : ℝ) < 1 + c ^ 2 := by positivity
  positivity

/-- **Baseline analysis of the lune radicand.**  If `R z = -s` with `s ≥ 0` a nonnegative real,
then `‖z‖² = 1 + s/B² ≥ 1`: `z` is (at least) on the unit circle.  Equivalently, the two roots of
the quadratic `z² - 2αz + 1` are complex conjugate of modulus `1`, and moving the real parameter
`-s/B²` only moves the product of the roots away from `1`. -/
theorem luneR_neg_real {c : ℝ} (hc : 1 < c) {z : ℂ} {s : ℝ}
    (h : luneR c z = -(s : ℂ)) (hs : 0 ≤ s) : ‖z‖ ^ 2 = 1 + s / luneBr c ^ 2 := by
  have hfac : luneB c ^ 2 * (z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1) = -(s : ℂ) := by
    rw [luneR_eq_factor] at h; exact h
  have hconj : luneB c ^ 2 * ((conj z) ^ 2 - 2 * (luneAlpha c : ℂ) * (conj z) + 1) =
      -(s : ℂ) := by
    have h1 := congrArg conj hfac
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, map_neg,
      Complex.conj_ofReal, conj_luneB] at h1
    exact h1
  have hsub : (z - conj z) * (z + conj z - 2 * (luneAlpha c : ℂ)) = 0 := by
    have h3 : (z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1) -
        ((conj z) ^ 2 - 2 * (luneAlpha c : ℂ) * (conj z) + 1) =
        (z - conj z) * (z + conj z - 2 * (luneAlpha c : ℂ)) := by ring
    have h2 : luneB c ^ 2 * ((z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1) -
        ((conj z) ^ 2 - 2 * (luneAlpha c : ℂ) * (conj z) + 1)) = 0 := by
      rw [mul_sub, hfac, hconj, sub_self]
    rw [h3] at h2
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 (luneB_ne_zero c))
  have hA2 : (0 : ℝ) < 1 - luneAlpha c ^ 2 := one_sub_luneAlpha_sq_pos hc
  rcases mul_eq_zero.mp hsub with hA | hB
  · -- `z` would have to be real: but then `R z > 0`
    have hzA : z = conj z := sub_eq_zero.mp hA
    have hzim : z.im = 0 := by
      have h1 : z.im = -z.im := by simpa using congrArg Complex.im hzA
      linarith
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hzim])
    rw [hzre] at hfac
    have hreal : luneBr c ^ 2 * (z.re ^ 2 - 2 * luneAlpha c * z.re + 1) = -s := by
      have hh := hfac
      simp only [luneB, luneBr] at hh
      exact_mod_cast hh
    have hpos : 0 < luneBr c ^ 2 * (z.re ^ 2 - 2 * luneAlpha c * z.re + 1) := by
      have h1 : 0 < z.re ^ 2 - 2 * luneAlpha c * z.re + 1 := by
        nlinarith [sq_nonneg (z.re - luneAlpha c)]
      exact mul_pos (pow_pos (luneBr_pos c) 2) h1
    linarith
  · -- `z + z̄ = 2α`: the product of the two conjugate roots is `1 + s/B²`
    have hzB : 2 * (luneAlpha c : ℂ) = z + conj z := (sub_eq_zero.mp hB).symm
    have hzsq : z ^ 2 - 2 * (luneAlpha c : ℂ) * z + 1 = 1 - z * conj z := by
      rw [hzB]; ring
    rw [hzsq, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hfac
    have hreal : luneBr c ^ 2 * (1 - ‖z‖ ^ 2) = -s := by
      have hh := hfac
      simp only [luneB] at hh
      push_cast at hh
      exact_mod_cast hh
    have hb : (0 : ℝ) < luneBr c ^ 2 := pow_pos (luneBr_pos c) 2
    have h1 : luneBr c ^ 2 * ‖z‖ ^ 2 = luneBr c ^ 2 + s := by linear_combination -hreal
    rw [show (1 : ℝ) + s / luneBr c ^ 2 = (luneBr c ^ 2 + s) / luneBr c ^ 2 by
      rw [add_div, div_self (ne_of_gt hb)]]
    exact (eq_div_iff (ne_of_gt hb)).mpr (by linarith)

/-- `luneR c` does not vanish in the open unit disc. -/
theorem luneR_ne_zero_of_norm_lt_one {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    luneR c z ≠ 0 := by
  intro h
  have h0 : luneR c z = -((0 : ℝ) : ℂ) := by rw [h]; norm_num
  have h1 := luneR_neg_real hc h0 le_rfl
  simp only [zero_div, add_zero] at h1
  have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  linarith

/-- `luneR c` avoids the branch cut `(-∞,0]` on the open unit disc. -/
theorem luneR_slitPlane_of_lt {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    luneR c z ∈ slitPlane := by
  rw [Complex.slitPlane]
  change 0 < (luneR c z).re ∨ (luneR c z).im ≠ 0
  by_contra hmem
  rw [not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (luneR c z).re ≤ 0 := le_of_not_gt hre
  have him' : (luneR c z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((luneR c z).re) := by linarith
  have hval : luneR c z = -(((-(luneR c z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := luneR_neg_real hc hval hs
  have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  rw [h1] at h2
  have h3 : 0 ≤ (-(luneR c z).re) / luneBr c ^ 2 :=
    div_nonneg hs (le_of_lt (pow_pos (luneBr_pos c) 2))
  linarith

/-- On the closed unit disc `luneR c` avoids the branch cut `(-∞,0]`, except that it may vanish
(at the two points of the unit circle which are the critical values of the inverse map). -/
theorem luneR_slitPlane_of_le_of_ne {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hne : luneR c z ≠ 0) : luneR c z ∈ slitPlane := by
  by_contra hmem
  rw [Complex.slitPlane, Set.mem_ofPred_eq, not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (luneR c z).re ≤ 0 := le_of_not_gt hre
  have him' : (luneR c z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((luneR c z).re) := by linarith
  have hval : luneR c z = -(((-(luneR c z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := luneR_neg_real hc hval hs
  have hb : (0 : ℝ) < luneBr c ^ 2 := pow_pos (luneBr_pos c) 2
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hs0 : -((luneR c z).re) = 0 := by
    have hle : (-(luneR c z).re) / luneBr c ^ 2 ≤ 0 := by linarith
    rcases (div_nonpos_iff.mp hle) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · linarith
    · linarith
  exact hne (by rw [hval, hs0, Complex.ofReal_zero, neg_zero])

end

end Work.APsi
