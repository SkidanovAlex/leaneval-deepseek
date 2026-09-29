import Mathlib
import Submission.CDTPlan.Interfaces

/-!
# Base algebra for the lune map `lune (23/10)` and `ψ_C`

This module develops the elementary algebra of the "lune" conformal map

`lune c z = (z(1+c²) - 1 - c² + √R(z)) / (2(c²-1))`,  `R(z) = (1+c²)²(1+z)² - 16c²z`,

at `c = 23/10` (the contour map `ψ_C = -(3/4)·lune (23/10) ·` of Calegari--Dimitrov--Tang,
arXiv:2408.15403 §"A contour for the logarithm problem"), together with the branch/baseline
analysis of `R`.

Write `B = 1 + c² = 629/100`, `C = c² - 1 = 429/100`, `c² = 529/100`, and `R z = B²(1+z)² - 16c²z`.
The lune is the inverse of the degree-two rational map

`f w = w (B + C w)/(C + B w)`

which is a conformal isomorphism from the lune `L(c) = 𝔻 \ 𝔻 ∩ D(-B/C, 2c/C)` onto the disc.
The algebraic heart (all identities below are *polynomial* identities, valid for every `z`):

* `R z = B²(z² - 2αz + 1)` with `α = 1 - 2C²/B²` and `1 - α² = 4C²(B²-C²)/B⁴ > 0`, i.e. `R` has two
  complex conjugate roots of modulus `1` (and no root in the open disc);
* `C w² + B(1-z) w - C z = 0` for `w = (Bz - B + √R(z))/(2C)` (only `(√R)² = R` is used);
* consequently `f (lune c z) = z` for **every** `z`, and the denominator never vanishes;
* `‖f w‖ = 1` whenever `‖w‖ = 1`.

The baseline/negativity analysis: if `R z = -s` with `s ≥ 0` then `‖z‖² = 1 + s/B² ≥ 1`; hence `R`
takes no value in `(-∞,0]` on the closed unit disc.
-/

namespace Work.CPsi

open Submission.CDTPlan Complex
open scoped ComplexConjugate

noncomputable section

/-- `1 + (23/10)²`, i.e. `B`. -/
noncomputable def gBr : ℝ := 629 / 100
/-- `(23/10)² - 1`, i.e. `C`. -/
noncomputable def gCr : ℝ := 429 / 100
/-- `1 + (23/10)²` as a complex number. -/
noncomputable def gB : ℂ := (gBr : ℂ)
/-- `(23/10)² - 1` as a complex number. -/
noncomputable def gC : ℂ := (gCr : ℂ)
/-- `(23/10)²` as a complex number. -/
noncomputable def gC2 : ℂ := ((529 / 100 : ℝ) : ℂ)
/-- `α = 1 - 2C²/B²`, the common real part of the two roots of `R`. -/
noncomputable def gAlpha : ℝ := 1 - 2 * gCr ^ 2 / gBr ^ 2

/-- `R(z) = B²(1+z)² - 16c²z` (the radicand of the lune map). -/
noncomputable def gobR (z : ℂ) : ℂ := gB ^ 2 * (1 + z) ^ 2 - 16 * gC2 * z

/-- The lune map with the numerical constants made explicit: `lune (23/10) = gobL`. -/
noncomputable def gobL (z : ℂ) : ℂ := (gB * z - gB + (gobR z) ^ (1 / 2 : ℂ)) / (2 * gC)

/-- The rational map `f w = w (B + C w)/(C + B w)` whose inverse is the lune map. -/
noncomputable def gobF (w : ℂ) : ℂ := w * (gB + gC * w) / (gC + gB * w)

theorem conj_gB : conj gB = gB := by simpa only [gB] using Complex.conj_ofReal gBr

theorem conj_gC : conj gC = gC := by simpa only [gC] using Complex.conj_ofReal gCr

theorem conj_gAlpha : conj (gAlpha : ℂ) = (gAlpha : ℂ) := by simp

theorem gB_ne_zero : gB ≠ 0 := by simp only [gB, gBr]; push_cast; norm_num

theorem gC_ne_zero : gC ≠ 0 := by simp only [gC, gCr]; push_cast; norm_num

theorem gBr_pos : 0 < gBr := by simp only [gBr]; norm_num

/-- `lune (23/10) z = gobL z`, definitionally after unfolding the numerical constants. -/
theorem lune_eq (z : ℂ) : lune (23 / 10) z = gobL z := by
  unfold lune gobL
  push_cast
  have e1 : (1 + (23 / 10 : ℂ) ^ 2 : ℂ) = (629 / 100 : ℂ) := by norm_num
  have e2 : ((23 / 10 : ℂ) ^ 2 : ℂ) = (529 / 100 : ℂ) := by norm_num
  rw [e1, e2]
  simp only [gB, gC, gC2, gBr, gCr, gobR]
  push_cast
  congr 1
  · ring
  · norm_num

theorem gobR_zero : gobR 0 = gB ^ 2 := by simp only [gobR]; ring

/-- `(w^{1/2})² = w` for the principal square root. -/
theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [one_div]
  exact Complex.cpow_nat_inv_pow _ (by norm_num)

/-- `(B²)^{1/2} = B` (principal square root of a positive real square). -/
theorem cpow_half_gB_sq : (gB ^ 2) ^ (1 / 2 : ℂ) = gB := by
  have h : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [h]
  exact Complex.sq_cpow_two_inv (by simp only [gB, gBr, Complex.ofReal_re]; norm_num)

/-- Alternative description of `R` (used to expand the square-root identity). -/
theorem gobR_eq_complete (z : ℂ) : gobR z = gB ^ 2 * (1 - z) ^ 2 + 4 * gC ^ 2 * z := by
  simp only [gobR, gB, gC, gC2, gBr, gCr]; push_cast; ring_nf

/-- Factorization of `R` through its two complex conjugate roots of modulus `1`. -/
theorem gobR_eq_factor (z : ℂ) : gobR z = gB ^ 2 * (z ^ 2 - 2 * (gAlpha : ℂ) * z + 1) := by
  simp only [gobR, gB, gC2, gAlpha, gBr, gCr]; push_cast; ring_nf

/-- The auxiliary identity behind `gobL_quad`: after multiplying by `4C²` the quadratic
relations become a polynomial identity in `σ` with `σ² = R(z)`. -/
theorem quad_mul (z σ : ℂ) :
    gC * (σ - gB * (1 - z)) ^ 2 + 2 * gC * gB * (1 - z) * (σ - gB * (1 - z)) - 4 * gC ^ 3 * z =
      gC * (σ ^ 2 - gobR z) := by
  rw [gobR_eq_complete]; ring

/-- `2C·gobL z = √R(z) - B(1-z)`. -/
theorem two_gC_gobL (z : ℂ) :
    2 * gC * gobL z = (gobR z) ^ (1 / 2 : ℂ) - gB * (1 - z) := by
  have hgC : gC ≠ 0 := gC_ne_zero
  simp only [gobL]; field_simp; ring

/-- **The quadratic relation**: `w = lune c z` satisfies `C w² + B(1-z) w - C z = 0`.
Only `(√R)² = R` is used, so this holds for **every** `z : ℂ`. -/
theorem gobL_quad (z : ℂ) : gC * (gobL z) ^ 2 + gB * (1 - z) * gobL z - gC * z = 0 := by
  have h2 : ((gobR z) ^ (1 / 2 : ℂ)) ^ 2 = gobR z := cpow_half_sq _
  have hu := two_gC_gobL z
  have key := quad_mul z ((gobR z) ^ (1 / 2 : ℂ))
  rw [h2, sub_self, mul_zero] at key
  rw [← hu] at key
  have key2 : (4 : ℂ) * gC ^ 2 * (gC * (gobL z) ^ 2 + gB * (1 - z) * gobL z - gC * z) = 0 := by
    rw [← key]; ring
  exact (mul_eq_zero.mp key2).resolve_left (by simp only [gC, gCr]; push_cast; norm_num)

/-- The denominator of `f` does not vanish at `w = lune c z`. -/
theorem gobL_pole_ne (z : ℂ) : gC + gB * gobL z ≠ 0 := by
  intro h
  have hgB : gB ≠ 0 := gB_ne_zero
  have hw : gobL z = -gC / gB := by
    field_simp
    linear_combination h
  have hq := gobL_quad z
  rw [hw] at hq
  field_simp at hq
  have h0 : gC ^ 3 - gC * gB ^ 2 ≠ 0 := by
    simp only [gC, gB, gBr, gCr]; push_cast; norm_num
  exact h0 (by linear_combination hq)

/-- `f (lune c z) = z` for every `z : ℂ`: the lune map is a right inverse of `f`. -/
theorem gobF_gobL (z : ℂ) : gobF (gobL z) = z := by
  have hq' : gobL z * (gC * gobL z + gB) = z * (gC + gB * gobL z) := by
    have hq := gobL_quad z
    linear_combination hq
  rw [gobF, div_eq_iff (gobL_pole_ne z)]
  linear_combination hq'

theorem gobF_zero : gobF 0 = 0 := by simp [gobF]

/-- `f` maps the unit circle into itself. -/
theorem norm_gobF_eq_one {w : ℂ} (hw : ‖w‖ = 1) : ‖gobF w‖ = 1 := by
  have hmul : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  have hden : gC + gB * w = w * conj (gB + gC * w) := by
    have h1 : gC + gB * w = w * (gB + gC * conj w) := by
      calc gC + gB * w = gC * (w * conj w) + gB * w := by rw [hmul]; ring
        _ = w * (gB + gC * conj w) := by ring
    rw [h1]
    congr 1
    simp only [map_add, map_mul, conj_gB, conj_gC]
  have hnorm : ‖gC + gB * w‖ = ‖gB + gC * w‖ := by
    rw [hden, norm_mul, hw, one_mul, Complex.norm_conj]
  have hne : gC + gB * w ≠ 0 := by
    intro h
    have h1 : gC = -(gB * w) := by linear_combination h
    have hw2 : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    have h2 : Complex.normSq gC = Complex.normSq gB := by
      rw [h1, Complex.normSq_neg, Complex.normSq_mul, hw2, mul_one]
    simp only [gC, gB, gBr, gCr, Complex.normSq_ofReal] at h2
    norm_num at h2
  have hne2 : ‖gB + gC * w‖ ≠ 0 := by
    rw [← hnorm]; exact norm_ne_zero_iff.mpr hne
  rw [gobF, norm_div, norm_mul, hnorm, hw, one_mul, div_self hne2]

/-- `lune c 0 = 0` (the lune map fixes the origin: `√R(0) = B`). -/
theorem gobL_zero : gobL 0 = 0 := by
  have h0 : gobR 0 = gB ^ 2 := gobR_zero
  simp only [gobL, h0, cpow_half_gB_sq, mul_zero, zero_sub]
  ring

/-- **Baseline analysis of `R`.**  If `R z` is a nonpositive real, `R z = -s` with `s ≥ 0`, then
`‖z‖² = 1 + s/B² ≥ 1`: `z` is (at least) on the unit circle.  This is the "discriminant
`(2B²-16c²)² - 4B⁴ = 16C²(C²-B²) < 0`" computation, in the form needed for the branch cut. -/
theorem gobR_neg_real {z : ℂ} {s : ℝ} (h : gobR z = -(s : ℂ)) (hs : 0 ≤ s) :
    ‖z‖ ^ 2 = 1 + s / gBr ^ 2 := by
  have hfac : gB ^ 2 * (z ^ 2 - 2 * (gAlpha : ℂ) * z + 1) = -(s : ℂ) := by
    rw [gobR_eq_factor] at h; exact h
  have hconj : gB ^ 2 * ((conj z) ^ 2 - 2 * (gAlpha : ℂ) * (conj z) + 1) = -(s : ℂ) := by
    have h1 := congrArg conj hfac
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, map_neg] at h1
    rw [conj_gB, conj_gAlpha, Complex.conj_ofReal] at h1
    exact h1
  have hsub : (z - conj z) * (z + conj z - 2 * (gAlpha : ℂ)) = 0 := by
    have h3 : (z ^ 2 - 2 * (gAlpha : ℂ) * z + 1) - ((conj z) ^ 2 - 2 * (gAlpha : ℂ) * (conj z) + 1) =
        (z - conj z) * (z + conj z - 2 * (gAlpha : ℂ)) := by ring
    have h2 : gB ^ 2 * ((z ^ 2 - 2 * (gAlpha : ℂ) * z + 1) -
        ((conj z) ^ 2 - 2 * (gAlpha : ℂ) * (conj z) + 1)) = 0 := by
      rw [mul_sub, hfac, hconj, sub_self]
    rw [h3] at h2
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 gB_ne_zero)
  have hA2 : (0 : ℝ) < 1 - gAlpha ^ 2 := by simp only [gAlpha, gBr, gCr]; norm_num
  have hBr2 : (0 : ℝ) < gBr ^ 2 := pow_pos gBr_pos 2
  rcases mul_eq_zero.mp hsub with hA | hB
  · -- `z` is real: then `R z > 0`, contradiction
    have hzA : z = conj z := sub_eq_zero.mp hA
    have hzim : z.im = 0 := by
      have h1 : z.im = -z.im := by simpa using congrArg Complex.im hzA
      linarith
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hzim])
    rw [hzre] at hfac
    have hreal : gBr ^ 2 * (z.re ^ 2 - 2 * gAlpha * z.re + 1) = -s := by
      have hh := hfac
      simp only [gB] at hh
      exact_mod_cast hh
    have hpos : 0 < gBr ^ 2 * (z.re ^ 2 - 2 * gAlpha * z.re + 1) := by
      nlinarith [sq_nonneg (z.re - gAlpha)]
    linarith
  · -- `z + z̄ = 2α`: the two conjugate roots, giving `z z̄ = 1 + s/B²`
    have hzB : 2 * (gAlpha : ℂ) = z + conj z := (sub_eq_zero.mp hB).symm
    have hzsq : z ^ 2 - 2 * (gAlpha : ℂ) * z + 1 = 1 - z * conj z := by
      rw [hzB]; ring
    rw [hzsq, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hfac
    have hreal : gBr ^ 2 * (1 - ‖z‖ ^ 2) = -s := by
      have hh := hfac
      simp only [gB] at hh
      push_cast at hh
      exact_mod_cast hh
    have hgBr : gBr ≠ 0 := ne_of_gt gBr_pos
    field_simp
    linarith

/-- `R` does not vanish in the open unit disc. -/
theorem gobR_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : gobR z ≠ 0 := by
  intro h
  have h0 : gobR z = -((0 : ℝ) : ℂ) := by rw [h]; norm_num
  have h1 := gobR_neg_real h0 le_rfl
  have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  simp only [zero_div, add_zero] at h1
  nlinarith [h1, h2]

/-- `R` avoids the branch cut `(-∞,0]` on the open unit disc, so `√R` is holomorphic there. -/
theorem gobR_slitPlane_of_lt {z : ℂ} (hz : ‖z‖ < 1) : gobR z ∈ slitPlane := by
  rw [Complex.slitPlane]
  change 0 < (gobR z).re ∨ (gobR z).im ≠ 0
  by_contra hmem
  rw [not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (gobR z).re ≤ 0 := le_of_not_gt hre
  have him' : (gobR z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((gobR z).re) := by linarith
  have hval : gobR z = -(((-(gobR z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := gobR_neg_real hval hs
  have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  rw [h1] at h2
  have : 0 ≤ (-(gobR z).re) / gBr ^ 2 := div_nonneg hs (le_of_lt (pow_pos gBr_pos 2))
  linarith

/-- On the closed unit disc `R` avoids the branch cut `(-∞,0]`, except that it may vanish
(at the two points of the unit circle which are the critical values of `f`). -/
theorem gobR_slitPlane_of_le_of_ne {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : gobR z ≠ 0) :
    gobR z ∈ slitPlane := by
  by_contra hmem
  rw [Complex.slitPlane, Set.mem_ofPred_eq, not_or] at hmem
  obtain ⟨hre, him⟩ := hmem
  have hre' : (gobR z).re ≤ 0 := le_of_not_gt hre
  have him' : (gobR z).im = 0 := not_not.mp him
  have hs : 0 ≤ -((gobR z).re) := by linarith
  have hval : gobR z = -(((-(gobR z).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him']
  have h1 := gobR_neg_real hval hs
  have h4 : (0 : ℝ) < gBr ^ 2 := pow_pos gBr_pos 2
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hs0 : -((gobR z).re) = 0 := by
    have hle : (-(gobR z).re) / gBr ^ 2 ≤ 0 := by linarith [h1, hz2]
    rcases (div_nonpos_iff.mp hle) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · linarith
    · linarith
  exact hne (by rw [hval, hs0, Complex.ofReal_zero, neg_zero])

end

end Work.CPsi
