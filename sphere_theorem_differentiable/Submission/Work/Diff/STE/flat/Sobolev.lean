import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dyadic (Littlewood–Paley) toolkit for the sharp `L^{2p}` Sobolev bound

This module fixes the vocabulary for `Work.Diff.STE.flat.norm_seriesFun_rpow_le`: the
sharp Sobolev embedding `H^j(𝕋^ι) ⊆ L^{2p}(𝕋^ι)` for `j > card ι * (1/2 - 1/(2p))`.

The proof splits the frequency lattice `ℤ^ι` into the dyadic annuli
`annulus m = {k | 2^{2m} ≤ ⟨k⟩² < 2^{2m+2}}`, estimates each block `seriesFun (blockCoeff m γ)`
separately (a sup bound and an `L²` bound, combined by Hölder), and sums the resulting geometric
series.

Objects:

* `annulus m`      : the `m`-th dyadic annulus of the lattice `ℤ^ι`;
* `blockCoeff m γ` : the `m`-th dyadic block of the coefficient family `γ`;
* `blockMass j m γ`: the `(wt ·)^j`-weighted `ℓ²` mass `Σ_k (wt k)^j ‖blockCoeff m γ k‖²`;
* `totalMass j γ`  : the same weight for the whole family;
* `rnorm q g`      : the `L^q` norm `(∫_{unitCube} ‖g‖^q)^{1/q}` of a function on the cube.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dyadic annulus `2^{2m} ≤ ⟨k⟩² < 2^{2m+2}` of the frequency lattice `ℤ^ι`.  Here
`⟨k⟩² = wt k`, so this is the shell `2^m ≤ ⟨k⟩ < 2^{m+1}`.  Since `wt k ≥ 1` these sets
partition the lattice. -/
def annulus (m : ℕ) : Set (ι → ℤ) :=
  {k | (2 : ℝ) ^ (2 * m) ≤ Work.Diff.STE.wt k ∧ Work.Diff.STE.wt k < (2 : ℝ) ^ (2 * (m + 1))}

/-- The `m`-th dyadic block of a coefficient family with values in an additive monoid with zero:
`g` restricted to `annulus m`.  (The decidability of the annulus membership is discharged
classically, so that statements using this definition need no `Decidable` instance.) -/
def blockFun {E : Type*} [Zero E] (m : ℕ) (g : (ι → ℤ) → E) : (ι → ℤ) → E := by
  classical
  exact fun k => if k ∈ annulus m then g k else 0

/-- The `m`-th dyadic block of a complex coefficient family: `γ` restricted to `annulus m`. -/
def blockCoeff (m : ℕ) (γ : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ := blockFun m γ

/-- The `(wt ·)^j`-weighted `ℓ²` mass of the `m`-th dyadic block of `γ`. -/
def blockMass (j : ℝ) (m : ℕ) (γ : (ι → ℤ) → ℂ) : ℝ :=
  ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖blockCoeff m γ k‖ ^ 2

/-- The `(wt ·)^j`-weighted `ℓ²` mass `Σ_k (wt k)^j ‖γ k‖²` of a coefficient family. -/
def totalMass (j : ℝ) (γ : (ι → ℤ) → ℂ) : ℝ :=
  ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2

/-- The `L^q`-norm `(∫_{unitCube} ‖g x‖^q dx)^{1/q}` of a function on the unit cube. -/
def rnorm (q : ℝ) (g : (ι → ℝ) → ℂ) : ℝ :=
  (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ q) ^ (1 / q)

@[simp] lemma blockCoeff_apply_mem (m : ℕ) (γ : (ι → ℤ) → ℂ) {k : ι → ℤ}
    (hk : k ∈ annulus (ι := ι) m) : blockCoeff m γ k = γ k := by
  classical
  simp only [blockCoeff, blockFun]
  exact if_pos hk

@[simp] lemma blockCoeff_apply_not_mem (m : ℕ) (γ : (ι → ℤ) → ℂ) {k : ι → ℤ}
    (hk : k ∉ annulus (ι := ι) m) : blockCoeff m γ k = 0 := by
  classical
  simp only [blockCoeff, blockFun]
  exact if_neg hk

lemma blockMass_nonneg (j : ℝ) (m : ℕ) (γ : (ι → ℤ) → ℂ) : 0 ≤ blockMass j m γ :=
  tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)

lemma totalMass_nonneg (j : ℝ) (γ : (ι → ℤ) → ℂ) : 0 ≤ totalMass j γ :=
  tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)

lemma rnorm_nonneg (q : ℝ) (g : (ι → ℝ) → ℂ) : 0 ≤ rnorm q g :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) q) _

/-- In the `ℓ¹` case the Fourier series is a continuous function: the series converges uniformly
by the Weierstrass M-test and every character is continuous. -/
theorem continuous_seriesFun (γ : (ι → ℤ) → ℂ) (hγ : Summable fun k : ι → ℤ => ‖γ k‖) :
    Continuous (Work.Diff.STE.seriesFun γ) := by
  have hf : ∀ k : ι → ℤ, Continuous (fun x : ι → ℝ => γ k * Work.Diff.STE.fourierExp k x) :=
    fun k => continuous_const.mul
      (Work.Diff.STE.BesselCont.continuous_fourierExp_char (ι := ι) k)
  have hb : ∀ (k : ι → ℤ) (x : ι → ℝ),
      ‖γ k * Work.Diff.STE.fourierExp k x‖ ≤ (fun k : ι → ℤ => ‖γ k‖) k := by
    intro k x
    rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]
  exact continuous_tsum hf hγ hb

/-- If the coefficient family is not `ℓ¹`, the pointwise Fourier series is identically zero
(this is the junk value of `tsum` for a non-summable family). -/
theorem seriesFun_eq_zero_of_not_summable (γ : (ι → ℤ) → ℂ)
    (hγ : ¬ Summable fun k : ι → ℤ => ‖γ k‖) : Work.Diff.STE.seriesFun γ = 0 := by
  funext x
  rw [Work.Diff.STE.seriesFun, Pi.zero_apply]
  refine tsum_eq_zero_of_not_summable fun hsum => hγ ?_
  refine hsum.norm.congr fun k => ?_
  rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]

end Work.Diff.STE.flat
