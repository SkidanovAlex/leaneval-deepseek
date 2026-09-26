/-
# `Gam1` maps the bottom-right Farey triangle of `U₀` into the CKMRV domain `𝒟`

`Work.CKFinal.U0` is the strip `-1 < Re τ < 1` with the four closed discs of radius `1/4`
centred at `±1/4`, `±3/4` removed; `Gam1 = !![1,0;-1,1]` acts by `τ ↦ τ/(1-τ)` and sends the
open Farey triangle `(0, 1/2, 1)` onto the triangle `(0, 1, ∞)`, which lies in the CKMRV
fundamental domain

  `𝒟 = {z ∈ ℍ : -1 < Re z < 1, |z - 1/2| > 1/2, |z + 1/2| > 1/2}`   (`Work.Asymptotics.DomainD`).

The triangle `(0, 1/2, 1)` is exactly the set of points of `U₀` with `|τ - 1/2| < 1/2`, so the
statement proved here is

  `τ ∈ U₀ → |τ - 1/2| < 1/2 → Gam1 • τ ∈ 𝒟`,

which is the "region" half of `Work.CKFinal.re_Gam1_smul_eq_zero_iff` (its converse direction is
the boundary case `|τ - 1/2| = 1/2`).

Everything is a computation in `x = τ.re`, `y = τ.im`, `A = |τ|² = x² + y²`.  Writing
`w = τ/(1-τ)` one has `|1-τ|² = 1 - 2x + A` and

* `Re w = (x - A)/(1 - 2x + A)`,   `|w|² = A/(1 - 2x + A)`,
* `|w - 1/2|² = |w|² - Re w + 1/4`,   `|w + 1/2|² = |w|² + Re w + 1/4`,

so the four conditions of `𝒟` are respectively equivalent to

* `-1 < Re w  ↔  x < 1`,
* `Re w < 1   ↔  2A > 3x - 1`,
* `|w - 1/2| > 1/2  ↔  2A > x`,
* `|w + 1/2| > 1/2  ↔  x > 0`.

The hypotheses produce exactly these: `|τ - 1/2| < 1/2` gives `A < x` (hence `0 < x < 1`), while
`|τ - 1/4| > 1/4` and `|τ - 3/4| > 1/4` (both from `τ ∈ U₀`) give `2A > x` and `2A > 3x - 1`.
-/
import Mathlib
import Submission.Work.CKFinal.U0ArcSetup
import Submission.Work.CKFinal.U0Defs
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal

/-! ## The coordinate identities for `|·|²` -/

private lemma ns_half (z : ℂ) :
    Complex.normSq (z - (1 / 2 : ℂ)) = Complex.normSq z + 1 / 4 - z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

private lemma ns_quarter (z : ℂ) :
    Complex.normSq (z - (1 / 4 : ℂ)) = Complex.normSq z + 1 / 16 - z.re / 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

private lemma ns_three_quarters (z : ℂ) :
    Complex.normSq (z - (3 / 4 : ℂ)) = Complex.normSq z + 9 / 16 - (3 / 2) * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

private lemma ns_one_sub (z : ℂ) :
    Complex.normSq (1 - z) = Complex.normSq z + 1 - 2 * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

private lemma ns_three_mul_sub_one (z : ℂ) :
    Complex.normSq (3 * z - 1) = 9 * Complex.normSq z + 1 - 6 * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

private lemma ns_add_one (z : ℂ) :
    Complex.normSq (z + 1) = Complex.normSq z + 1 + 2 * z.re := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  norm_num
  ring

private lemma normSq_coe (τ : UpperHalfPlane) :
    Complex.normSq (τ : ℂ) = τ.re ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- `1/2 < ‖w‖` is the same as `1/4 < |w|²`. -/
private lemma half_lt_norm_iff (w : ℂ) : (1 / 2 : ℝ) < ‖w‖ ↔ 1 / 4 < Complex.normSq w := by
  rw [Complex.normSq_eq_norm_sq]
  constructor <;> intro h
  · nlinarith
  · nlinarith [norm_nonneg w]

/-- The real part of `z/(1-z)` in coordinates. -/
private lemma re_div_aux (z : ℂ) :
    (z / (1 - z)).re = (z.re - Complex.normSq z) / Complex.normSq (1 - z) := by
  rw [Complex.div_re, Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  simp
  ring

private lemma sub_half_eq (z : ℂ) (hz : z ≠ 1) :
    z / (1 - z) - 1 / 2 = (3 * z - 1) / (2 * (1 - z)) := by
  have h1 : (1 - z : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  field_simp
  ring

private lemma add_half_eq (z : ℂ) (hz : z ≠ 1) :
    z / (1 - z) + 1 / 2 = (z + 1) / (2 * (1 - z)) := by
  have h1 : (1 - z : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  field_simp
  ring

private lemma nsq_sub_half (z : ℂ) (hz : z ≠ 1) :
    Complex.normSq (z / (1 - z) - 1 / 2) =
      Complex.normSq (3 * z - 1) / (4 * Complex.normSq (1 - z)) := by
  rw [sub_half_eq z hz, Complex.normSq_div, Complex.normSq_mul]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]

private lemma nsq_add_half (z : ℂ) (hz : z ≠ 1) :
    Complex.normSq (z / (1 - z) + 1 / 2) =
      Complex.normSq (z + 1) / (4 * Complex.normSq (1 - z)) := by
  rw [add_half_eq z hz, Complex.normSq_div, Complex.normSq_mul]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]

/-! ## The two halves of the computation -/

/-- **Real part.**  If `z = x + iy ≠ 1` has `|z|² < x` and `3x - 1 < 2|z|²`, then
`w = z/(1-z)` satisfies `-1 < Re w < 1`. -/
private lemma re_div_one_sub_bounds_aux (z : ℂ) (h1 : Complex.normSq z < z.re)
    (h2 : 3 * z.re - 1 < 2 * Complex.normSq z) :
    -1 < (z / (1 - z)).re ∧ (z / (1 - z)).re < 1 := by
  have hzne : z ≠ 1 := by
    intro hz
    rw [hz] at h1
    norm_num [Complex.normSq_apply] at h1
  have hDne : (1 - z : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hzne)
  have hDpos : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hDne
  have hDval : Complex.normSq (1 - z) = Complex.normSq z + 1 - 2 * z.re := ns_one_sub z
  rw [re_div_aux]
  constructor
  · rw [lt_div_iff₀ hDpos]
    linarith
  · rw [div_lt_iff₀ hDpos]
    linarith

/-- **Norm bounds.**  If `z = x + iy ≠ 1` has `x < 2|z|²` and `x > 0`, then
`w = z/(1-z)` satisfies `|w - 1/2| > 1/2` and `|w + 1/2| > 1/2`. -/
private lemma norm_div_one_sub_half_bounds_aux (z : ℂ) (hz : z ≠ 1)
    (h1 : z.re < 2 * Complex.normSq z) (h2 : 0 < z.re) :
    (1 / 2 : ℝ) < ‖z / (1 - z) - 1 / 2‖ ∧ (1 / 2 : ℝ) < ‖z / (1 - z) + 1 / 2‖ := by
  have hDne : (1 - z : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hDpos : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hDne
  have hDval : Complex.normSq (1 - z) = Complex.normSq z + 1 - 2 * z.re := ns_one_sub z
  have hEpos : (0 : ℝ) < Complex.normSq z + 1 - 2 * z.re := by
    rw [← hDval]
    exact hDpos
  have h4pos : (0 : ℝ) < 4 * (Complex.normSq z + 1 - 2 * z.re) := by linarith
  have hkey1 : 1 / 4 < Complex.normSq (z / (1 - z) - 1 / 2) := by
    rw [nsq_sub_half z hz, ns_three_mul_sub_one, hDval, lt_div_iff₀ h4pos]
    linarith
  have hkey2 : 1 / 4 < Complex.normSq (z / (1 - z) + 1 / 2) := by
    rw [nsq_add_half z hz, ns_add_one, hDval, lt_div_iff₀ h4pos]
    linarith
  exact ⟨(half_lt_norm_iff _).mpr hkey1, (half_lt_norm_iff _).mpr hkey2⟩

/-! ## The main theorem -/

theorem gam1_smul_mem_DomainD (τ : UpperHalfPlane) (hτ : τ ∈ Work.CKFinal.U0)
    (h : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2) :
    Work.CKFinal.Gam1 • τ ∈ Work.Asymptotics.DomainD := by
  obtain ⟨-, -, h14, -, h34, -⟩ := mem_U0_iff.mp hτ
  -- `A = |τ|²`
  have hA : Complex.normSq (τ : ℂ) < τ.re := by
    have h1 : Complex.normSq ((τ : ℂ) - (1 / 2 : ℂ)) < 1 / 4 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
    rw [ns_half, UpperHalfPlane.coe_re] at h1
    linarith
  have hB : τ.re < 2 * Complex.normSq (τ : ℂ) := by
    have h1 : 1 / 16 < Complex.normSq ((τ : ℂ) - (1 / 4 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((τ : ℂ) - (1 / 4 : ℂ))]
    rw [ns_quarter, UpperHalfPlane.coe_re] at h1
    linarith
  have hC : 3 * τ.re - 1 < 2 * Complex.normSq (τ : ℂ) := by
    have h1 : 1 / 16 < Complex.normSq ((τ : ℂ) - (3 / 4 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((τ : ℂ) - (3 / 4 : ℂ))]
    rw [ns_three_quarters, UpperHalfPlane.coe_re] at h1
    linarith
  have hx0 : 0 < τ.re := by
    have hy : (0 : ℝ) ≤ τ.im ^ 2 := sq_nonneg τ.im
    have hA' : Complex.normSq (τ : ℂ) = τ.re ^ 2 + τ.im ^ 2 := normSq_coe τ
    nlinarith [Complex.normSq_nonneg (τ : ℂ)]
  have hx1 : τ.re < 1 := by
    have hy : (0 : ℝ) ≤ τ.im ^ 2 := sq_nonneg τ.im
    have hA' : Complex.normSq (τ : ℂ) = τ.re ^ 2 + τ.im ^ 2 := normSq_coe τ
    nlinarith [Complex.normSq_nonneg (τ : ℂ)]
  have hz : (τ : ℂ) ≠ 1 := by
    intro hzz
    have hre : (τ : ℂ).re = 1 := by rw [hzz]; simp
    rw [UpperHalfPlane.coe_re] at hre
    linarith
  obtain ⟨hr1, hr2⟩ := re_div_one_sub_bounds_aux (τ : ℂ) hA hC
  obtain ⟨hn1, hn2⟩ := norm_div_one_sub_half_bounds_aux (τ : ℂ) hz hB hx0
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← UpperHalfPlane.coe_re, coe_Gam1_smul]
    exact hr1
  · rw [← UpperHalfPlane.coe_re, coe_Gam1_smul]
    exact hr2
  · rw [coe_Gam1_smul]
    exact hn1
  · rw [coe_Gam1_smul]
    exact hn2

end Work.CKFinal
