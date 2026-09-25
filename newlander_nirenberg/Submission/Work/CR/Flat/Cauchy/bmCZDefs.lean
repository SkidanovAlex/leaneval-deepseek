/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Definitions for the Calderón–Zygmund estimate for the Bochner–Martinelli potential

This file collects the vocabulary used in
`Submission/Work/CR/Flat/Cauchy/bmPotential_holderNorm_le.lean`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ### Euclidean balls and annuli -/

/-- The open ball of radius `R` for the Euclidean norm on `ℂⁿ`. -/
def eucBall {n : ℕ} (R : ℝ) : Set (Fin n → ℂ) := {x | eucNorm x < R}

/-- The closed ball of radius `R` for the Euclidean norm on `ℂⁿ`. -/
def eucClosedBall {n : ℕ} (R : ℝ) : Set (Fin n → ℂ) := {x | eucNorm x ≤ R}

/-- The annulus `a ≤ ‖x‖ < b` for the Euclidean norm on `ℂⁿ`. -/
def eucShell {n : ℕ} (a b : ℝ) : Set (Fin n → ℂ) := {x | a ≤ eucNorm x ∧ eucNorm x < b}

@[simp] lemma mem_eucBall {n : ℕ} {R : ℝ} {x : Fin n → ℂ} :
    x ∈ eucBall R ↔ eucNorm x < R := Iff.rfl

@[simp] lemma mem_eucClosedBall {n : ℕ} {R : ℝ} {x : Fin n → ℂ} :
    x ∈ eucClosedBall R ↔ eucNorm x ≤ R := Iff.rfl

@[simp] lemma mem_eucShell {n : ℕ} {a b : ℝ} {x : Fin n → ℂ} :
    x ∈ eucShell a b ↔ a ≤ eucNorm x ∧ eucNorm x < b := Iff.rfl

lemma measurableSet_eucBall {n : ℕ} (R : ℝ) : MeasurableSet (eucBall (n := n) R) :=
  (isOpen_lt continuous_eucNorm continuous_const).measurableSet

lemma measurableSet_eucShell {n : ℕ} (a b : ℝ) : MeasurableSet (eucShell (n := n) a b) :=
  (isClosed_le continuous_const continuous_eucNorm).measurableSet.inter
    (isOpen_lt continuous_eucNorm continuous_const).measurableSet

/-- The ambient (sup) norm is bounded by the Euclidean norm. -/
lemma pi_norm_le_eucNorm {n : ℕ} (x : Fin n → ℂ) : ‖x‖ ≤ eucNorm x := by
  rw [pi_norm_le_iff_of_nonneg (eucNorm_nonneg x)]
  intro i
  have h : ‖x i‖ ^ 2 ≤ eucNorm x ^ 2 := by
    rw [eucNorm_sq]
    exact Finset.single_le_sum (f := fun l : Fin n => ‖x l‖ ^ 2) (fun l _ => sq_nonneg (‖x l‖))
      (Finset.mem_univ i)
  have h3 : |‖x i‖| ≤ |eucNorm x| := sq_le_sq.mp h
  rw [abs_of_nonneg (norm_nonneg (x i)), abs_of_nonneg (eucNorm_nonneg x)] at h3
  exact h3

/-- The Euclidean ball is contained in the ball of the same radius for the ambient norm. -/
lemma eucBall_subset_ball {n : ℕ} {R : ℝ} :
    eucBall (n := n) R ⊆ Metric.ball (0 : Fin n → ℂ) R := fun x hx => by
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (pi_norm_le_eucNorm x) hx

lemma eucBall_subset_eucClosedBall {n : ℕ} {R : ℝ} :
    eucBall (n := n) R ⊆ eucClosedBall (n := n) R := fun x hx => by
  simpa using le_of_lt hx

/-! ### The smooth radial cutoff -/

/-- A smooth profile: `1` on `(-∞,1/2]` and `0` on `[1,∞)`. -/
def cutProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t)

lemma cutProfile_of_two_mul_le_one {t : ℝ} (ht : 2 * t ≤ 1) : cutProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith [ht])

lemma cutProfile_of_one_le {t : ℝ} (ht : 1 ≤ t) : cutProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith [ht])

lemma cutProfile_nonneg (t : ℝ) : 0 ≤ cutProfile t := by
  rcases le_or_gt (2 * t) 1 with h | h
  · simpa [cutProfile_of_two_mul_le_one h]
  · rcases le_or_gt 1 t with h2 | h2
    · simpa [cutProfile_of_one_le h2]
    · exact Real.smoothTransition.nonneg _

lemma cutProfile_le_one (t : ℝ) : cutProfile t ≤ 1 := by
  rcases le_or_gt (2 * t) 1 with h | h
  · simpa [cutProfile_of_two_mul_le_one h]
  · rcases le_or_gt 1 t with h2 | h2
    · simpa [cutProfile_of_one_le h2]
    · exact Real.smoothTransition.le_one _

lemma contDiff_cutProfile : ContDiff ℝ 1 cutProfile :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The smooth radial cutoff `ρ`: equal to `1` on `eucBall (R/2)` and to `0` off `eucBall R`. -/
def eucCutoff {n : ℕ} (R : ℝ) (x : Fin n → ℂ) : ℝ := cutProfile (eucNorm x / R)

/-- The `ℂ`-valued smooth radial cutoff. -/
def eucCutoffC {n : ℕ} (R : ℝ) (x : Fin n → ℂ) : ℂ := (eucCutoff R x : ℂ)

lemma eucCutoff_nonneg {n : ℕ} (R : ℝ) (x : Fin n → ℂ) : 0 ≤ eucCutoff R x :=
  cutProfile_nonneg _

lemma eucCutoff_le_one {n : ℕ} (R : ℝ) (x : Fin n → ℂ) : eucCutoff R x ≤ 1 :=
  cutProfile_le_one _

lemma eucCutoff_eq_one {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin n → ℂ}
    (hx : 2 * eucNorm x ≤ R) : eucCutoff R x = 1 := by
  refine cutProfile_of_two_mul_le_one ?_
  rw [show 2 * (eucNorm x / R) = (2 * eucNorm x) / R from by ring, div_le_one hR]
  exact hx

lemma eucCutoff_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin n → ℂ}
    (hx : R ≤ eucNorm x) : eucCutoff R x = 0 :=
  cutProfile_of_one_le (by rw [one_le_div hR]; exact hx)

lemma eucCutoffC_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin n → ℂ}
    (hx : R ≤ eucNorm x) : eucCutoffC R x = 0 := by
  simp [eucCutoffC, eucCutoff_eq_zero hR hx]

/-! ### Wirtinger derivatives of the Bochner–Martinelli kernel -/

/-- `∂_{z_k}` of the Bochner–Martinelli kernel `bmKernel j`: `-n \bar x_j \bar x_k ‖x‖^{-2n-2}`. -/
def bmDzKernel {n : ℕ} (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k) / ((eucNorm x : ℂ) ^ (2 * n + 2))

/-- `∂_{\bar z_k}` of the Bochner–Martinelli kernel `bmKernel j`:
`δ_{jk}‖x‖^{-2n} - n \bar x_j x_k ‖x‖^{-2n-2}`. -/
def bmDbarKernel {n : ℕ} (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  (if k = j then 1 else 0) / ((eucNorm x : ℂ) ^ (2 * n))
    - (n : ℂ) * starRingEnd ℂ (x j) * x k / ((eucNorm x : ℂ) ^ (2 * n + 2))

/-- The singular part of `∂_{z_k}(bmKernel j · ρ)`: `ρ · ∂_{z_k}(bmKernel j)`. -/
def bmPhiRho {n : ℕ} (R : ℝ) (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  eucCutoffC R x * bmDzKernel k j x

/-- The smooth compactly supported part of `∂_{z_k}(bmKernel j · ρ)`:
`bmKernel j · ∂_{z_k} ρ`. -/
def bmPhiCut {n : ℕ} (R : ℝ) (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  bmKernel j x * dCoord k (eucCutoffC R) x

/-- The part of the kernel `∂_{z_k}(bmKernel j) (1 - ρ)` supported off the origin:
`(1 - ρ) ∂_{z_k}(bmKernel j)`. -/
def bmPsiRho {n : ℕ} (R : ℝ) (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  (1 - eucCutoffC R x) * bmDzKernel k j x

/-- The smooth compactly supported part of `∂_{z_k}(bmKernel j (1 - ρ))`:
`- bmKernel j · ∂_{z_k} ρ`. -/
def bmPsiCut {n : ℕ} (R : ℝ) (k j : Fin n) (x : Fin n → ℂ) : ℂ :=
  -(bmKernel j x * dCoord k (eucCutoffC R) x)

/-! ### The Fréchet derivative of the Euclidean norm -/

/-- A candidate Fréchet derivative of `eucNorm` at `x` (valid for `x ≠ 0`):
`v ↦ ‖x‖⁻¹ ∑ k, Re (conj (x k) * v k)`. -/
def eucNormDeriv {n : ℕ} (x : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ k, (eucNorm x)⁻¹ •
    (Complex.reCLM.comp
      (((ContinuousLinearMap.mul ℝ ℂ (starRingEnd ℂ (x k))).comp (ContinuousLinearMap.proj k))))

end Work.CR.Flat.Cauchy
