/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Shared setup for the Bochner–Martinelli divergence computation

This file collects the definitions and elementary lemmas shared by the proof that the
Bochner–Martinelli potential solves the flat `∂̄`-equation on a polydisc
(`Submission/Work/CR/Flat/Cauchy/bmPotential_solves_dbar.lean`).

* `nrmSq x = Σ_j ‖x_j‖²` is the *squared* Euclidean norm on `ℂⁿ = Fin n → ℂ`; it is the
  natural polynomial parametrisation of `eucNorm`, so that the Bochner–Martinelli kernel
  reads `bmKernel k x = \bar x_k / nrmSq x ^ n` (see `bmKernel_eq`).
* `bmKerEps k ε x = \bar x_k / (nrmSq x + ε²)^n` is the regularised kernel: smooth for
  `ε > 0`, with `bmKerEps k ε x → bmKernel k x` as `ε → 0⁺`.
* `bmPot f z = Σ_k ∫ x, bmKernel k x * f k (z + x)` is the potential with the singular
  point translated to the origin; `bmPotential_eq_bmPot` shows it is `bmPotential`.
* `bmGamma n = -∫ x, n / (nrmSq x + 1)^{n+1}` is the normalising constant of the
  Bochner–Martinelli formula.  It is non-zero (`bmGamma_ne_zero_of`), the relevant
  positivity of the integral `∫ x, n / (nrmSq x + 1)^{n+1}` being `integrable_bmWeight`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_coord
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- The squared Euclidean norm on `ℂⁿ = Fin n → ℂ`, `nrmSq x = Σ_j ‖x_j‖²`. -/
def nrmSq {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

lemma nrmSq_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ nrmSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nrmSq_eq_eucNorm_sq {n : ℕ} (x : Fin n → ℂ) : nrmSq x = eucNorm x ^ 2 := by
  rw [nrmSq, ← eucNorm_sq]

lemma nrmSq_eq_zero {n : ℕ} {x : Fin n → ℂ} : nrmSq x = 0 ↔ x = 0 := by
  rw [nrmSq_eq_eucNorm_sq, sq_eq_zero_iff, eucNorm_eq_zero]

lemma nrmSq_pos {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < nrmSq x := by
  rw [nrmSq_eq_eucNorm_sq]
  exact pow_pos (eucNorm_pos hx) 2

/-- The Bochner–Martinelli kernel in terms of the squared Euclidean norm. -/
lemma bmKernel_eq {n : ℕ} (k : Fin n) (x : Fin n → ℂ) :
    bmKernel k x = starRingEnd ℂ (x k) / ((nrmSq x : ℝ) : ℂ) ^ n := by
  have h : ((eucNorm x : ℂ)) ^ (2 * n) = (((eucNorm x ^ 2 : ℝ)) : ℂ) ^ n := by
    rw [pow_mul, Complex.ofReal_pow]
  rw [bmKernel, nrmSq, h, eucNorm_sq]

/-- The Euclidean norm dominates the sup norm on `ℂⁿ`. -/
lemma norm_le_eucNorm {n : ℕ} (x : Fin n → ℂ) : ‖x‖ ≤ eucNorm x := by
  refine (pi_norm_le_iff_of_nonneg (eucNorm_nonneg x)).mpr fun j => ?_
  rw [eucNorm, ← Real.sqrt_sq (norm_nonneg (x j))]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))

/-- `nrmSq` is bounded by `n` times the sup norm squared. -/
lemma nrmSq_le_card_mul {n : ℕ} (x : Fin n → ℂ) : nrmSq x ≤ n * ‖x‖ ^ 2 := by
  calc nrmSq x = ∑ j, ‖x j‖ ^ 2 := rfl
    _ ≤ ∑ _j : Fin n, ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x j) 2
    _ = n * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `nrmSq` is a quadratic form. -/
lemma nrmSq_smul {n : ℕ} (ε : ℝ) (y : Fin n → ℂ) : nrmSq (ε • y) = ε ^ 2 * nrmSq y := by
  have h : ∀ j : Fin n, ‖(ε • y) j‖ ^ 2 = ε ^ 2 * ‖y j‖ ^ 2 := by
    intro j
    rw [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
  rw [nrmSq, nrmSq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => h j

lemma nrmSq_smul' {n : ℕ} (ε : ℝ) (y : Fin n → ℂ) : nrmSq (ε • y) + ε ^ 2 = ε ^ 2 * (nrmSq y + 1) := by
  rw [nrmSq_smul]; ring

/-- The regularised Bochner–Martinelli kernel `\bar x_k / (nrmSq x + ε²)^n`. -/
def bmKerEps {n : ℕ} (k : Fin n) (ε : ℝ) (x : Fin n → ℂ) : ℂ :=
  starRingEnd ℂ (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n

@[simp] lemma bmKerEps_apply {n : ℕ} (k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    bmKerEps k ε x = starRingEnd ℂ (x k) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n := rfl

/-- The normalising constant of the Bochner–Martinelli formula:
`bmGamma n = -∫_ℂⁿ n / (1 + ‖x‖²)^{n+1} dx`. -/
def bmGamma (n : ℕ) : ℂ :=
  -(((∫ x : Fin n → ℂ, (n : ℝ) / (nrmSq x + 1) ^ (n + 1)) : ℝ) : ℂ)

/-- The Bochner–Martinelli potential written with the singularity at the origin,
`bmPot f z = Σ_k ∫ x, bmKernel k x * f k (z + x)`. -/
def bmPot {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ k, ∫ x, bmKernel k x * f k (z + x)

/-- `bmPot` is `bmPotential`: translating the singularity to the origin. -/
lemma bmPotential_eq_bmPot {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    bmPotential f z = bmPot f z := by
  rw [bmPotential, bmPot]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun y : Fin n → ℂ => bmKernel k y * f k (z + y)) z
  have h' : ∀ x : Fin n → ℂ, z + (x - z) = x := fun x => by abel
  simp only [h'] at h
  rw [← h]

/-- If the weight `n / (1+‖x‖²)^{n+1}` has a positive integral then the
Bochner–Martinelli constant is non-zero. -/
lemma bmGamma_ne_zero_of {n : ℕ}
    (h : 0 < ∫ y : Fin n → ℂ, (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) : bmGamma n ≠ 0 := by
  rw [bmGamma, neg_ne_zero, Complex.ofReal_ne_zero]
  exact ne_of_gt h

end Work.CR.Flat.Cauchy
