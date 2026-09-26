/-
# `Gam2` maps the left bottom arc region of `U₀` into the CKMRV domain `𝒟`

`Work.CKFinal.Gam2 = !![1,0;1,1]` acts on `ℍ` by `τ ↦ τ / (1 + τ)`.  The disc
`‖τ + 1/2‖ < 1/2` (whose boundary meets `U₀` exactly along the bottom-left arc
`‖τ + 1/2‖ = 1/2`, the geodesic `0 ↔ -1`) is mapped by `Gam2` onto the half plane
`Re w < 0`; the three remaining conditions cutting out the CKMRV fundamental domain
`𝒟 = {-1 < Re < 1, |· - 1/2| > 1/2, |· + 1/2| > 1/2}` (CKMRV (3.12)) are exactly the
conditions `‖τ + 1/4‖ > 1/4` and `‖τ + 3/4‖ > 1/4` which, together with the strip
`-1 < Re τ < 1`, define `U₀` away from its bottom arcs.

Concretely, with `z = (τ : ℂ)`, `a = Re z`, `b = Im z`, `r² = a² + b²` and `w = z/(1+z)`:

* `‖w + 1/2‖ = ‖3z+1‖ / (2‖1+z‖)` and `‖3z+1‖² - ‖1+z‖² = 4(2r²+a)`, so
  `‖w + 1/2‖ > 1/2 ⟺ 2r² + a > 0`, i.e. exactly `‖τ + 1/4‖ > 1/4`;
* `‖w - 1/2‖ = ‖z-1‖ / (2‖1+z‖)` and `‖z-1‖² - ‖1+z‖² = -4a`, so
  `‖w - 1/2‖ > 1/2 ⟺ a < 0`, which follows from `2r² + a > 0` together with
  `r² + a < 0`, the latter being `‖τ + 1/2‖ < 1/2`;
* `Re w = (a + r²)/((1+a)² + b²)`, so `Re w < 0` follows from `r² + a < 0` and
  `Re w > -1` is equivalent to `2r² + 3a + 1 > 0`, i.e. exactly `‖τ + 3/4‖ > 1/4`.

The first two families of elementary facts are the delegated lemmas
`Work.CKFinal.gam2_arith` (the real-arithmetic content of the three disc conditions) and
`Work.CKFinal.gam2_quotient_identities` (the Möbius identities for `z ↦ z/(1+z)`); the
present file contains the assembly, i.e. the comparison of the three squared norms
`‖1+z‖²`, `‖z-1‖²`, `‖3z+1‖²` and the transfer to `UpperHalfPlane`.
-/
import Mathlib
import Submission.Work.CKFinal.U0ArcSetup
import Submission.Work.CKFinal.U0Defs
import Submission.Work.CKFinal.gam2_arith
import Submission.Work.CKFinal.gam2_quotient_identities
import Submission.Work.Asymptotics.DomainD

set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.CKFinal

/-- The square of the norm of `z - 1`, in coordinates. -/
lemma gam2smul_norm_sq_sub_one (z : ℂ) : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- The square of the norm of `3z + 1`, in coordinates. -/
lemma gam2smul_norm_sq_three_mul_add_one (z : ℂ) :
    ‖(3 : ℂ) * z + 1‖ ^ 2 = 9 * (z.re ^ 2 + z.im ^ 2) + 6 * z.re + 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  norm_num
  ring

/-- **The left bottom arc of `U₀` is carried by `Gam2` into the CKMRV fundamental domain.**

For `τ` in the open set `U₀` (the strip `-1 < Re τ < 1` minus the four closed Farey discs of
radius `1/4` about `±1/4`, `±3/4`) lying inside the disc `‖τ + 1/2‖ < 1/2`, the Möbius image
`Gam2 • τ = τ/(1+τ)` lies in `𝒟 = {-1 < Re < 1, |· - 1/2| > 1/2, |· + 1/2| > 1/2}`. -/
theorem gam2_smul_mem_DomainD (τ : UpperHalfPlane) (hτ : τ ∈ Work.CKFinal.U0)
    (h : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2) :
    Work.CKFinal.Gam2 • τ ∈ Work.Asymptotics.DomainD := by
  -- The two `U₀` conditions used below: `‖τ + 1/4‖ > 1/4` and `‖τ + 3/4‖ > 1/4`.
  obtain ⟨_, _, _, hB, _, hD3⟩ := hτ
  have him : 0 < τ.im := τ.im_pos
  -- `1 + τ ≠ 0`, since `Im (1 + τ) = Im τ > 0`.
  have h1z : (1 : ℂ) + (τ : ℂ) ≠ 0 := by
    intro hc
    have h1 : ((1 : ℂ) + (τ : ℂ)).im = 0 := by rw [hc]; simp
    simp [Complex.add_im] at h1
    linarith [him, h1]
  have hpos : 0 < ‖1 + (τ : ℂ)‖ := norm_pos_iff.mpr h1z
  -- The real-arithmetic content of the three disc conditions (delegated lemma).
  obtain ⟨A1, A2, A3, A4, hD⟩ := gam2_arith (τ : ℂ) him hB hD3 h
  -- The Möbius identities for `z ↦ z/(1+z)` (delegated lemma).
  obtain ⟨hre, hn1, hn2⟩ := gam2_quotient_identities (τ : ℂ) h1z
  have hnum : (τ : ℂ).re + ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) < 0 := by nlinarith [A3]
  -- `‖1 + z‖²` in coordinates.
  have h3 : ‖1 + (τ : ℂ)‖ ^ 2 = (1 + (τ : ℂ).re) ^ 2 + (τ : ℂ).im ^ 2 := by
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, add_comm, norm_sq_add_real]
    ring
  -- `‖1 + z‖ < ‖z - 1‖`, i.e. `Re z < 0`.
  have hs1 : ‖1 + (τ : ℂ)‖ < ‖(τ : ℂ) - 1‖ := by
    have hlt : ‖1 + (τ : ℂ)‖ ^ 2 < ‖(τ : ℂ) - 1‖ ^ 2 := by
      rw [gam2smul_norm_sq_sub_one, h3]; nlinarith [A4]
    have hh := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hh
  -- `‖1 + z‖ < ‖3z + 1‖`, i.e. `2r² + a > 0`.
  have hs2 : ‖1 + (τ : ℂ)‖ < ‖(3 : ℂ) * (τ : ℂ) + 1‖ := by
    have hlt : ‖1 + (τ : ℂ)‖ ^ 2 < ‖(3 : ℂ) * (τ : ℂ) + 1‖ ^ 2 := by
      rw [gam2smul_norm_sq_three_mul_add_one, h3]; nlinarith [A1]
    have hh := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hh
  rw [Work.Asymptotics.mem_DomainD, ← UpperHalfPlane.coe_re, Work.CKFinal.coe_Gam2_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `-1 < Re w`, equivalent to `2r² + 3a + 1 > 0`
    rw [hre, lt_div_iff₀ hD]; nlinarith [A2]
  · -- `Re w < 1`, indeed `Re w < 0` because `r² + a < 0`
    rw [hre]
    have hneg := div_neg_of_neg_of_pos hnum hD
    linarith
  · -- `‖w - 1/2‖ > 1/2`
    rw [hn1, lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * ‖1 + (τ : ℂ)‖)]
    linarith
  · -- `‖w + 1/2‖ > 1/2`
    rw [hn2, lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * ‖1 + (τ : ℂ)‖)]
    linarith

end Work.CKFinal
