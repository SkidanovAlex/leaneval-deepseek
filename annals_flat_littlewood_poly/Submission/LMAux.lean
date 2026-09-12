import Mathlib
import Submission.DiscrepancyDefs

/-!
Auxiliary bridge between `Fin n → ℝ` (as used in `Submission.Discrepancy`) and
`EuclideanSpace ℝ (Fin n)` (as used in the Gaussian-walk proof of the partial colouring lemma).
-/
open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission

namespace Discrepancy

/-- The Euclidean space over the coordinate type `Fin n`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Inner product of two Euclidean vectors. -/
def vin {n : ℕ} (a b : Vec n) : ℝ := ⟪a, b⟫

/-- Euclidean norm. -/
def vnorm {n : ℕ} (a : Vec n) : ℝ := ‖a‖

/-- A vector with 1 in coordinate `i`, 0 elsewhere. -/
def basis (n : ℕ) (i : Fin n) : Vec n := EuclideanSpace.single i 1

/-- Conversion function → Vec (bundled linear isometry, rfl-friendly). -/
def toV {n : ℕ} (f : Fin n → ℝ) : Vec n := WithLp.toLp 2 f

/-- Conversion Vec → function. -/
def ofV {n : ℕ} (x : Vec n) : Fin n → ℝ := WithLp.ofLp (p := 2) x

@[simp] lemma ofV_toV {n : ℕ} (f : Fin n → ℝ) : ofV (toV f) = f := by
  simp [ofV, toV]

@[simp] lemma toV_ofV {n : ℕ} (x : Vec n) : toV (ofV x) = x := by
  simp [ofV, toV]

@[simp] lemma ofV_apply {n : ℕ} (x : Vec n) (i : Fin n) : ofV x i = x i := rfl

@[simp] lemma toV_apply {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : (toV f) i = f i := by
  simp [toV]

lemma vin_toV {n : ℕ} (f g : Fin n → ℝ) : vin (toV f) (toV g) = dot f g := by
  simp [vin, dot, PiLp.inner_apply, mul_comm]

lemma vin_sum {n : ℕ} (a b : Vec n) : vin a b = ∑ i : Fin n, a i * b i := by
  simp [vin, PiLp.inner_apply, mul_comm]

lemma norm_sq_sum (n : ℕ) (x : Vec n) : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
  simpa [ofV] using (EuclideanSpace.real_norm_sq_eq x)

lemma sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith [sq_nonneg (a - b)]

lemma vnorm_toV {n : ℕ} (f : Fin n → ℝ) : vnorm (toV f) = eucl f := by
  rw [vnorm, eucl]
  apply sq_eq_of_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt]
  · rw [norm_sq_sum]
    simp [toV]
  · positivity

lemma basis_apply (n : ℕ) (i : Fin n) (j : Fin n) : ofV (basis n i) j = if j = i then 1 else 0 := by
  simp [basis, ofV, EuclideanSpace.single]

lemma vin_basis (n : ℕ) (i : Fin n) (x : Vec n) : vin (basis n i) x = x i := by
  simp [vin, basis, EuclideanSpace.inner_single_left]

lemma vin_sq_norm (n : ℕ) (x : Vec n) : vin x x = ‖x‖ ^ 2 := by
  simpa [vin] using (inner_self_eq_norm_sq x : (inner ℝ x x).re = ‖x‖ ^ 2)


/-- The coefficient function is measurable. -/
lemma measurable_coord (n : ℕ) (i : Fin n) : Measurable (fun x : Vec n => x i) := by
  let e : (Fin n → ℝ) ≃ᵐ (Vec n) := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have h : (fun x : Vec n => x i) = (fun f : Fin n → ℝ => f i) ∘ e.symm := by
    ext x
    simp [e, Vec]
  rw [h]
  exact (measurable_pi_apply i).comp e.symm.measurable

/-- Measurability of the absolute value of a coefficient. -/
lemma measurable_abs_coord (n : ℕ) (i : Fin n) : Measurable (fun x : Vec n => |x i|) := by
  simpa using (measurable_coord n i).abs

/-- Measurability of an inner product with a fixed vector. -/
lemma measurable_vin (n : ℕ) (a : Vec n) : Measurable (fun x : Vec n => vin x a) := by
  have hc : Continuous (fun x : Vec n => ⟪x, a⟫) :=
    continuous_inner.comp (by fun_prop : Continuous (fun x : Vec n => (x, a)))
  simpa [vin] using hc.measurable

/-- Measurability of a norm. -/
lemma measurable_norm (n : ℕ) : Measurable (fun x : Vec n => ‖x‖) := by
  fun_prop

/-- The finite family of subsets of `Fin n`. -/
lemma finrank_euclidean (n : ℕ) : Module.finrank ℝ (Vec n) = n := by
  simp [Vec]

end Discrepancy

end Submission
