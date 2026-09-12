import Mathlib
import Submission.Conjugates
import Submission.Minpoly
import Submission.GOnCutPlane
import Submission.XTransfer
import Submission.BranchX

/-!
# Pointwise growth bound for the X-plane branch off the star

`Submission.BranchX.exists_laurent_branch` gives, for a nonzero algebraic
integer `α`, a function `g` holomorphic on `ℂ ∖ star S`
(`S := conjugateValues α`) with

    g X ^ 2 = (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹)   (X ∉ star S)

The right hand side is the product `∏_{z∈S}(1 - z²/X)(1 - z⁴/X)`
(`GOnCutPlane.eval₂_Gpoly_eq_prod`).  This module records the resulting
explicit pointwise bound, valid on the whole complement of the star:

    ‖g X‖ ≤ (1 + (house α)^4 / ‖X‖) ^ |S|        (X ∉ star S)

It is obtained purely from the algebraic identity (`|z| = |z²|^{1/2}` and
`|z| ≤ house α` for every conjugate `z`); no complex analysis is needed.

## Why this bound matters

In the Pólya–Hadamard part of the engine one bounds the Hankel determinants
by `det ∮ g(X)·p_i(X)·p_j(X)·X⁻¹ dX` over a large circle, deformed to a
contour at distance ≥ ε from the star.  On such a contour `‖X‖ ≥ ε`
(`0 ∈ star S`), so `‖g X‖ ≤ (1 + H⁴/ε)^d` is an explicit, polynomial-in-`1/ε`
control of the integrand's first factor.

## Ingredients

* `z ∈ conjugateValues α` ⟹ `‖z‖ ≤ house α`  (`norm_conj_le_house` after
  unrolling the image), and `house α ≥ 1` (`one_le_house_of_isIntegral_ne_zero`);
* `‖1 - u‖ ≤ 1 + ‖u‖` (triangle inequality) applied to `u = z²·X⁻¹`, `z⁴·X⁻¹`;
* `‖g X‖² = ‖g X ^ 2‖` for complex `g X`, and the square identity.
-/

noncomputable section

open scoped Polynomial Real

namespace Submission.Gnorm

open Polynomial
open Submission.Conjugates
open Submission.Minpoly
open Submission.GOnCutPlane
open Submission.XTransfer

variable {K : Type*} [Field K] [NumberField K]

/-- Every conjugate has modulus at most the house. -/
lemma norm_le_house_of_mem_conj {α : K} {z : ℂ} (hz : z ∈ conjugateValues α) :
    ‖z‖ ≤ NumberField.house α := by
  classical
  rcases Finset.mem_image.mp hz with ⟨σ, hσ, hzσ⟩
  simpa [hzσ] using norm_conj_le_house α σ

/-- Pointwise form of `GOnCutPlane.eval₂_Gpoly_eq_prod` in terms of `X⁻¹`,
for `X ≠ 0`. -/
lemma sq_eq_prod_inv {α : K} (hα : IsIntegral ℤ α) {X : ℂ} (hX : X ≠ 0) :
    (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹) =
      ((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * X⁻¹)) *
        ((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * X⁻¹)) := by
  have hinv : X⁻¹ ≠ 0 := by exact inv_ne_zero hX
  simpa using eval₂_Gpoly_eq_prod (α := α) hα (w := X⁻¹) hinv

/-- For `X ∉ star S` (in particular `X ≠ 0`): `‖g X‖²` equals the product of
the moduli-squared of the `G`-factors at `X⁻¹`. -/
lemma norm_sq_g {α : K} (hα : IsIntegral ℤ α) (g : ℂ → ℂ) {X : ℂ}
    (hX : X ∈ (star (conjugateValues α))ᶜ)
    (hgsq : g X ^ 2 = (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹)) :
    ‖g X‖ ^ 2 =
      ((conjugateValues α).prod (fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖)) *
        ((conjugateValues α).prod (fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖)) := by
  have hXne : X ≠ 0 := by
    intro hX0
    have hSne : (conjugateValues α).Nonempty := by
      dsimp [conjugateValues]
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
    exact hX (by simpa [hX0] using (zero_mem_star (S := conjugateValues α) hSne))
  calc
    ‖g X‖ ^ 2 = ‖g X ^ 2‖ := by
        rw [← norm_pow]
    _ = ‖(Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹)‖ := by rw [hgsq]
    _ = ‖(((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * X⁻¹)) *
          ((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * X⁻¹)))‖ := by
        rw [sq_eq_prod_inv (α := α) hα hXne]
    _ = ((conjugateValues α).prod (fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖)) *
          ((conjugateValues α).prod (fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖)) := by
        rw [norm_mul]
        rw [Complex.norm_prod]
        rw [Complex.norm_prod]

/-- Factor bound: `‖1 - zᵐ·w‖ ≤ 1 + (house α)^4·‖w‖` for `m ∈ {2,4}` and
conjugates `z`. -/
lemma factor_le {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) {z : ℂ}
    (hz : z ∈ conjugateValues α) {m : ℕ} (hm : m = 2 ∨ m = 4) (w : ℂ) :
    ‖1 - z ^ m * w‖ ≤ 1 + (NumberField.house α) ^ 4 * ‖w‖ := by
  have hzle : ‖z‖ ≤ NumberField.house α := norm_le_house_of_mem_conj hz
  have h1 : 1 ≤ NumberField.house α := one_le_house_of_isIntegral_ne_zero hα hα0
  have hHn : 0 ≤ NumberField.house α := by positivity
  have hHsq1 : 1 ≤ (NumberField.house α) ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ NumberField.house α * 1 := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ NumberField.house α * NumberField.house α :=
          mul_le_mul_of_nonneg_left h1 (le_trans (by norm_num) h1)
      _ = (NumberField.house α) ^ 2 := by ring
  have hHz2 : (NumberField.house α) ^ 2 ≤ (NumberField.house α) ^ 4 := by
    calc
      (NumberField.house α) ^ 2 = (NumberField.house α) ^ 2 * 1 := by ring
      _ ≤ (NumberField.house α) ^ 2 * (NumberField.house α) ^ 2 :=
          mul_le_mul_of_nonneg_left hHsq1 (by positivity)
      _ = (NumberField.house α) ^ 4 := by ring
  have hzm : ‖z‖ ^ m ≤ (NumberField.house α) ^ 4 := by
    rcases hm with rfl | rfl
    · -- m = 2
      exact le_trans (pow_le_pow_left₀ (norm_nonneg z) hzle 2) hHz2
    · -- m = 4
      exact pow_le_pow_left₀ (norm_nonneg z) hzle 4
  calc
    ‖1 - z ^ m * w‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ m * w‖ := norm_sub_le _ _
    _ = 1 + ‖z ^ m‖ * ‖w‖ := by simp
    _ = 1 + ‖z‖ ^ m * ‖w‖ := by rw [norm_pow]
    _ ≤ 1 + (NumberField.house α) ^ 4 * ‖w‖ := by
        nlinarith [hzm, norm_nonneg w, norm_nonneg z]

/-- **Pointwise growth of the branch off the star.**  For a nonzero algebraic
integer `α`, any `g` satisfying the BranchX square identity off the star
`satisfies `‖g X‖ ≤ (1 + house⁴/‖X‖)^|S|` there. -/
theorem norm_g_le {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) (g : ℂ → ℂ)
    (hgsq : ∀ X ∈ (star (conjugateValues α))ᶜ,
      g X ^ 2 = (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹))
    {X : ℂ} (hX : X ∈ (star (conjugateValues α))ᶜ) :
    ‖g X‖ ≤ (1 + (NumberField.house α) ^ 4 / ‖X‖) ^ (conjugateValues α).card := by
  classical
  let S : Finset ℂ := conjugateValues α
  have hXne : X ≠ 0 := by
    intro hX0
    have hSne : S.Nonempty := by
      dsimp [S, conjugateValues]
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
    exact hX (by simpa [hX0] using (zero_mem_star (S := S) hSne))
  have hw : X⁻¹ ≠ 0 := inv_ne_zero hXne
  -- the squared norm equals the product of the moduli of the factors
  have hsq := norm_sq_g (α := α) hα g (X := X) hX (hgsq X hX)
  -- bound each factor by `1 + H⁴·‖X⁻¹‖`
  have hfac2 : ∀ z ∈ S, ‖1 - z ^ 2 * X⁻¹‖ ≤ 1 + (NumberField.house α) ^ 4 * ‖X⁻¹‖ := by
    intro z hz
    exact factor_le (α := α) hα hα0 (z := z) hz (Or.inl rfl) (X⁻¹)
  have hfac4 : ∀ z ∈ S, ‖1 - z ^ 4 * X⁻¹‖ ≤ 1 + (NumberField.house α) ^ 4 * ‖X⁻¹‖ := by
    intro z hz
    exact factor_le (α := α) hα hα0 (z := z) hz (Or.inr rfl) (X⁻¹)
  let c : ℝ := 1 + (NumberField.house α) ^ 4 * ‖X⁻¹‖
  have hfac2c : ∀ z ∈ S, ‖1 - z ^ 2 * X⁻¹‖ ≤ c := by
    intro z hz
    simpa [c] using hfac2 z hz
  have hfac4c : ∀ z ∈ S, ‖1 - z ^ 4 * X⁻¹‖ ≤ c := by
    intro z hz
    simpa [c] using hfac4 z hz
  have hle : (S.prod (fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖)) *
        (S.prod (fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖)) ≤ c ^ (2 * S.card) := by
    have hp2 : (S.prod fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖) ≤ c ^ S.card := by
      calc
        (S.prod fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖) ≤ S.prod fun z : ℂ => c :=
            Finset.prod_le_prod (fun z hz => norm_nonneg _) hfac2c
        _ = c ^ S.card := by simp
    have hp4 : (S.prod fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖) ≤ c ^ S.card := by
      calc
        (S.prod fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖) ≤ S.prod fun z : ℂ => c :=
            Finset.prod_le_prod (fun z hz => norm_nonneg _) hfac4c
        _ = c ^ S.card := by simp
    calc
      (S.prod fun z : ℂ => ‖1 - z ^ 2 * X⁻¹‖) * (S.prod fun z : ℂ => ‖1 - z ^ 4 * X⁻¹‖)
          ≤ (c ^ S.card) * (c ^ S.card) :=
              mul_le_mul hp2 hp4 (Finset.prod_nonneg (by intro z hz; positivity))
                (by positivity)
      _ = c ^ (2 * S.card) := by
          rw [← pow_add]
          congr 1
          ring
  have hg2le : ‖g X‖ ^ 2 ≤ c ^ (2 * S.card) := by
    rw [hsq]
    exact hle
  -- now take square roots
  have hsqr : ‖g X‖ ≤ c ^ S.card := by
    have hA0 : 0 ≤ ‖g X‖ := norm_nonneg _
    have hB0 : 0 ≤ c ^ S.card := by positivity
    have hg2sq : ‖g X‖ ^ 2 ≤ (c ^ S.card) ^ 2 := by
      calc
        ‖g X‖ ^ 2 ≤ c ^ (2 * S.card) := hg2le
        _ = (c ^ S.card) ^ 2 := by ring_nf
    exact (sq_le_sq₀ hA0 hB0).mp hg2sq
  -- rewrite ‖X⁻¹‖ = ‖X‖⁻¹
  have hnorm_inv : ‖X⁻¹‖ = ‖X‖⁻¹ := by exact norm_inv X
  calc
    ‖g X‖ ≤ c ^ S.card := hsqr
    _ = (1 + (NumberField.house α) ^ 4 / ‖X‖) ^ S.card := by
        dsimp [c]
        rw [hnorm_inv]
        rfl

