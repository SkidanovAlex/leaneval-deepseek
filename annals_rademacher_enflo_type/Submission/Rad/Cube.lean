import ChallengeDeps
set_option autoImplicit false
open Function MeasureTheory
open scoped ENNReal

namespace RadType
open RademacherEnfloType

/-- The two-point set `{-1,1}` as a subset of `ℤ`. -/
abbrev C := ({-1, 1} : Set ℤ)
/-- The discrete cube of dimension `n`. -/
abbrev Ω (n : ℕ) := Fin n → C

lemma val_eq (z : C) : (z : ℤ) = 1 ∨ (z : ℤ) = -1 := by
  rcases z with ⟨v, hv⟩
  change v ∈ ({-1, 1} : Set ℤ) at hv
  rw [Set.mem_insert_iff] at hv
  rcases hv with hv | hv
  · right; simpa using hv
  · rw [Set.mem_singleton_iff] at hv
    left; simpa using hv

lemma coe_real_eq (z : C) : ((z : C) : ℝ) = 1 ∨ ((z : C) : ℝ) = -1 := by
  rcases val_eq z with h | h <;> simp [h]

lemma neg_coe_int (z : C) : ((-z : C) : ℤ) = -(z : ℤ) := rfl

lemma neg_coe_real (z : C) : ((-z : C) : ℝ) = -((z : C) : ℝ) := by
  rw [neg_coe_int]; norm_num

@[simp] lemma neg_neg (z : C) : -(-z : C) = z := by
  apply Subtype.ext
  simp [neg_coe_int]

@[simp] lemma neg_mem_one : -(⟨1, by decide⟩ : C) = (⟨-1, by decide⟩ : C) := by
  apply Subtype.ext; rfl

@[simp] lemma neg_mem_neg_one : -(⟨-1, by decide⟩ : C) = (⟨1, by decide⟩ : C) := by
  apply Subtype.ext; rfl

lemma ennorm_scalar (z : C) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X) :
    ‖((z : C) : ℝ) • x‖ₑ = ‖x‖ₑ := by
  rcases coe_real_eq z with h | h <;> simp [h]

/-- Pointwise negation on the cube. -/
def negΩ {n : ℕ} (ε : Ω n) : Ω n := fun j => -ε j

@[simp] lemma negΩ_apply {n : ℕ} (ε : Ω n) (j : Fin n) : (negΩ ε) j = - ε j := rfl

@[simp] lemma negΩ_negΩ {n : ℕ} (ε : Ω n) : negΩ (negΩ ε) = ε := by
  ext j; simp

/-- The function that flips coordinate `j` only. -/
def flip {n : ℕ} (j : Fin n) (ε : Ω n) : Ω n := update ε j (- ε j)

@[simp] lemma flip_apply_self {n : ℕ} (j : Fin n) (ε : Ω n) : flip j ε j = - ε j := by
  simp [flip]

lemma flip_apply_of_ne {n : ℕ} {j : Fin n} {ε : Ω n} {i : Fin n} (hij : i ≠ j) :
    flip j ε i = ε i := by
  simp [flip, hij]

@[simp] lemma flip_flip {n : ℕ} (j : Fin n) (ε : Ω n) : flip j (flip j ε) = ε := by
  ext i
  by_cases h : i = j
  · subst i; simp [flip]
  · simp [flip, h]

end RadType
