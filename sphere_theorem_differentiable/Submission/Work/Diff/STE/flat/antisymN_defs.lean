import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for `Work.Diff.STE.flat.antisymN_bound`

Definitions used by the antisymmetrisation estimate `antisymN_bound`: the symmetrisation of a
value / first-jet pair, the real quadratic form of the real part of a complex matrix, the region
of "admissible" pairs (bounded entries, positive definite quadratic form) and the antisymmetric
size functional appearing on the right-hand side of the estimate.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-- The symmetric part `(A + Aᵀ) / 2` of a complex matrix. -/
def symMat (A : MatC n) : MatC n := fun i j => (A i j + A j i) / 2

/-- Symmetrisation of a value / first-jet pair. -/
def symPair (w : MatC n × (Fin n → MatC n)) : MatC n × (Fin n → MatC n) :=
  (symMat w.1, fun c => symMat (w.2 c))

/-- The real quadratic form `∑ᵢⱼ (reMat A)ᵢⱼ ξᵢ ξⱼ` of the real part of a complex matrix. -/
def quadForm (A : MatC n) (ξ : Fin n → ℝ) : ℝ := ∑ i, ∑ j, reMat A i j * ξ i * ξ j

/-- The set of value / first-jet pairs with entries bounded by `M` and real quadratic form
dominating `lam * ‖ξ‖²`. -/
def posSet (M lam : ℝ) : Set (MatC n × (Fin n → MatC n)) :=
  {w | (∀ i j, ‖w.1 i j‖ ≤ M) ∧ (∀ c i j, ‖(w.2 c) i j‖ ≤ M) ∧
    ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ}

/-- The domain of the nonlinearity: the real part of the value matrix is non-singular. -/
def detNeZeroSet : Set (MatC n × (Fin n → MatC n)) := {w | (reMat w.1).det ≠ 0}

/-- The domain of `N`, as an abbreviation (the same set as the one appearing in the hypotheses of
`antisymN_bound`). -/
def domN : Set ((Fin n → ℝ) × (MatC n × (Fin n → MatC n))) :=
  Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}

/-- The closed unit cube on which the `x`-variable of `N` is estimated. -/
def cubeN : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)

/-- The total size of the antisymmetric part of a complex matrix. -/
def asymSum (A : MatC n) : ℝ := ∑ i, ∑ j, ‖A i j - A j i‖

/-- The total size of the antisymmetric part of a value / first-jet pair. -/
def asymPairSum (w : MatC n × (Fin n → MatC n)) : ℝ := asymSum w.1 + ∑ c, asymSum (w.2 c)

@[simp] lemma symMat_apply (A : MatC n) (i j : Fin n) : symMat A i j = (A i j + A j i) / 2 := rfl

@[simp] lemma symPair_apply (w : MatC n × (Fin n → MatC n)) :
    symPair w = (symMat w.1, fun c => symMat (w.2 c)) := rfl

@[simp] lemma quadForm_apply (A : MatC n) (ξ : Fin n → ℝ) :
    quadForm A ξ = ∑ i, ∑ j, reMat A i j * ξ i * ξ j := rfl

lemma mem_posSet {M lam : ℝ} {w : MatC n × (Fin n → MatC n)} :
    w ∈ posSet M lam ↔ (∀ i j, ‖w.1 i j‖ ≤ M) ∧ (∀ c i j, ‖(w.2 c) i j‖ ≤ M) ∧
      ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ := Iff.rfl

lemma mem_detNeZeroSet {w : MatC n × (Fin n → MatC n)} :
    w ∈ detNeZeroSet ↔ (reMat w.1).det ≠ 0 := Iff.rfl

/-- The quadratic form `∑ᵢ ∑ⱼ Aᵢⱼ ξᵢ ξⱼ` is the dot product of `ξ` with `A *ᵥ ξ`. -/
lemma sum_sum_mul_eq_dotProduct' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, A i j * v i * v j = dotProduct v (A.mulVec v) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A nonzero vector has positive sum of squares. -/
lemma sum_sq_pos_of_ne_zero' {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, (v i) ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : v k ≠ 0 := by simpa using hk
  have hpos := Finset.sum_pos' (s := Finset.univ) (fun i _ => sq_nonneg (v i))
    ⟨k, Finset.mem_univ k, sq_pos_of_ne_zero hk'⟩
  simpa using hpos

/-- A square real matrix whose associated quadratic form dominates `lam * ‖·‖²` with `lam > 0`
is nonsingular.  (Local copy of `Work.Diff.STE.flat.det_ne_zero_of_quadForm_le`, under a
different name so that no module has to import two files declaring the same constants.) -/
theorem det_ne_zero_of_quadForm_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h0 : ∑ i, ∑ j, A i j * v i * v j = 0 := by
    rw [sum_sum_mul_eq_dotProduct', hv, dotProduct_zero]
  have hvpos : 0 < ∑ i, (v i) ^ 2 := sum_sq_pos_of_ne_zero' hvne
  have hle := h v
  rw [h0] at hle
  have hpos := mul_pos hlam hvpos
  linarith

end

end Work.Diff.STE.flat
