/-
# The line `Re τ = ±1/2` above height `1` and its `S`-image lie in `𝒟`

For `τ ∈ ℍ` with `Re τ = 1/2` or `Re τ = -1/2` and `Im τ ≥ 1`, both `τ` and its image under
`S = !![0, -1; 1, 0]` (the Möbius transformation `τ ↦ -1/τ`) lie in the CKMRV domain

  `𝒟 = {z : -1 < Re z < 1, |z - 1/2| > 1/2, |z + 1/2| > 1/2}`

(`Work.Asymptotics.DomainD`).  This is the geometric input recording that the two vertical
lines bounding the two ideal triangles of `U₀` (at height at least `1`) are mapped by `S`
back into the domain of convergence of the CKMRV contour integral.

The proof is a direct coordinate computation.  With `τ = x + iy`, `x = ±1/2`, `y ≥ 1`:

* `‖τ ∓ 1/2‖² = (x ∓ 1/2)² + y² ≥ 1`, so `‖τ ∓ 1/2‖ > 1/2`;
* for `w = S • τ = -1/τ` one has `w = -x/‖τ‖² + i y/‖τ‖²` with `‖τ‖² ≥ 5/4`, so
  `|Re w| ≤ (1/2)/(5/4) < 1`, and
  `‖w - 1/2‖ = ‖2 + τ‖/(2‖τ‖)`, `‖w + 1/2‖ = ‖2 - τ‖/(2‖τ‖)`,
  both `> 1/2` because `‖2 ± τ‖² - ‖τ‖² = 4(1 ± x) > 0`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.CKFinal

/-- Coordinate form of the squared modulus of `τ`. -/
lemma normSq_coe (τ : ℍ) : Complex.normSq (τ : ℂ) = τ.re ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply]; simp; ring

/-- Coordinate form of the squared distance from `τ` to `1/2`. -/
lemma normSq_sub_half (τ : ℍ) :
    Complex.normSq ((τ : ℂ) - (1 / 2 : ℂ)) = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im]; ring

/-- Coordinate form of the squared distance from `τ` to `-1/2`. -/
lemma normSq_add_half (τ : ℍ) :
    Complex.normSq ((τ : ℂ) + (1 / 2 : ℂ)) = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.add_re, Complex.add_im]; ring

/-- Coordinate form of the squared modulus of `2 + τ`. -/
lemma normSq_two_add (τ : ℍ) :
    Complex.normSq ((2 : ℂ) + (τ : ℂ)) = (τ.re + 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.add_re, Complex.add_im]; ring

/-- Coordinate form of the squared modulus of `2 - τ`. -/
lemma normSq_two_sub (τ : ℍ) :
    Complex.normSq ((2 : ℂ) - (τ : ℂ)) = (τ.re - 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im]; ring

/-- The Möbius action of `S = !![0, -1; 1, 0]` is `τ ↦ -1/τ`. -/
lemma S_coe (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
  rw [modular_S_smul, coe_mk, neg_inv]

/-- `1/2 < ‖z‖` follows from `1/4 < ‖z‖²` (`= Complex.normSq z`). -/
lemma norm_gt_half_of (z : ℂ) (h : (1 : ℝ) / 4 < Complex.normSq z) : (1 / 2 : ℝ) < ‖z‖ := by
  have h2 : (1 / 2 : ℝ) ^ 2 < ‖z‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith
  nlinarith [norm_nonneg z]

end Work.CKFinal

namespace Work.CKFinal

/-- **CKMRV**: on the two vertical lines `Re τ = ±1/2` above height `1`, both `τ` and its image
`S • τ = -1/τ` lie in the fundamental domain `𝒟` of `Γ(2)`. -/
theorem S_smul_line_mem_DomainD (τ : UpperHalfPlane)
    (hτ : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (h1 : 1 ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD ∧ ModularGroup.S • τ ∈ Work.Asymptotics.DomainD := by
  have hc0 : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hcpos : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hc0
  have hcgt1 : 1 < ‖(τ : ℂ)‖ := by
    have h : (1 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, normSq_coe]
      rcases hτ with h | h <;> rw [h] <;> nlinarith
    nlinarith [norm_nonneg (τ : ℂ)]
  constructor
  · rw [Work.Asymptotics.mem_DomainD]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hτ with h | h <;> linarith
    · rcases hτ with h | h <;> linarith
    · apply norm_gt_half_of
      rw [normSq_sub_half]
      rcases hτ with h | h <;> rw [h] <;> nlinarith
    · apply norm_gt_half_of
      rw [normSq_add_half]
      rcases hτ with h | h <;> rw [h] <;> nlinarith
  · set w : ℍ := ModularGroup.S • τ with hwdef
    have hw : (w : ℂ) = -((τ : ℂ))⁻¹ := by rw [hwdef]; exact S_coe τ
    rw [Work.Asymptotics.mem_DomainD]
    have hwnorm : ‖(w : ℂ)‖ = 1 / ‖(τ : ℂ)‖ := by
      rw [hw, norm_neg, norm_inv]; ring
    have hwlt1 : ‖(w : ℂ)‖ < 1 := by
      rw [hwnorm, div_lt_one hcpos]; exact hcgt1
    have hre : |w.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm (w : ℂ)) hwlt1
    have hwsub : (w : ℂ) - 1 / 2 = -((2 + (τ : ℂ)) / (2 * (τ : ℂ))) := by
      rw [hw]; field_simp; ring
    have hnorm_sub : ‖(w : ℂ) - 1 / 2‖ = ‖2 + (τ : ℂ)‖ / (2 * ‖(τ : ℂ)‖) := by
      rw [hwsub, norm_neg, norm_div, norm_mul]; norm_num
    have hlt2 : ‖(τ : ℂ)‖ < ‖(2 : ℂ) + (τ : ℂ)‖ := by
      have hsq : ‖(τ : ℂ)‖ ^ 2 < ‖(2 : ℂ) + (τ : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_two_add, normSq_coe]
        rcases hτ with h | h <;> rw [h] <;> nlinarith
      nlinarith [norm_nonneg (τ : ℂ), norm_nonneg ((2 : ℂ) + (τ : ℂ))]
    have hhalf1 : 1 / 2 < ‖(w : ℂ) - 1 / 2‖ := by
      rw [hnorm_sub, lt_div_iff₀ (by positivity)]
      nlinarith
    have hwadd : (w : ℂ) + 1 / 2 = -((2 - (τ : ℂ)) / (2 * (τ : ℂ))) := by
      rw [hw]; field_simp; ring
    have hnorm_add : ‖(w : ℂ) + 1 / 2‖ = ‖2 - (τ : ℂ)‖ / (2 * ‖(τ : ℂ)‖) := by
      rw [hwadd, norm_neg, norm_div, norm_mul]; norm_num
    have hlt3 : ‖(τ : ℂ)‖ < ‖(2 : ℂ) - (τ : ℂ)‖ := by
      have hsq : ‖(τ : ℂ)‖ ^ 2 < ‖(2 : ℂ) - (τ : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_two_sub, normSq_coe]
        rcases hτ with h | h <;> rw [h] <;> nlinarith
      nlinarith [norm_nonneg (τ : ℂ), norm_nonneg ((2 : ℂ) - (τ : ℂ))]
    have hhalf2 : 1 / 2 < ‖(w : ℂ) + 1 / 2‖ := by
      rw [hnorm_add, lt_div_iff₀ (by positivity)]
      nlinarith
    exact ⟨(abs_lt.mp hre).1, (abs_lt.mp hre).2, hhalf1, hhalf2⟩

end Work.CKFinal
