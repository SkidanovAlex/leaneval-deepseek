import Submission.Rad.Cube
set_option autoImplicit false
open Function MeasureTheory
open scoped ENNReal

namespace RadType
open RademacherEnfloType

/-- The linear test function `ε ↦ Σ_j (ε j : ℝ) • x j`. -/
noncomputable def lin {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (x : Fin n → X) (ε : Ω n) : X :=
  ∑ j : Fin n, (((ε j : C) : ℝ) • x j)

lemma lin_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (x : Fin n → X) (ε : Ω n) : lin x (negΩ ε) = - lin x ε := by
  unfold lin negΩ
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp [neg_coe_real]

lemma lin_sub_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (x : Fin n → X) (ε : Ω n) :
    (1 / 2 : ℝ) • (lin x ε - lin x (negΩ ε)) = lin x ε := by
  rw [lin_neg]
  simp
  module

/-- Changing coordinate `j` changes a linear function by twice the `j`-th summand. -/
lemma lin_flip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (x : Fin n → X) (ε : Ω n) (j : Fin n) :
    lin x ε - lin x (update ε j (- ε j)) = 2 • (((ε j : C) : ℝ) • x j) := by
  classical
  unfold lin
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · -- j-th summand difference
    rw [update_self, neg_coe_real, neg_smul]
    module
  · intro b hb hbj
    -- all other terms cancel
    rw [Function.update_of_ne hbj]
    exact sub_self _
  · intro hjm
    exact (hjm (Finset.mem_univ j)).elim

/-- The `j`-th discrete derivative of a linear function is the `j`-th summand. -/
lemma D_lin {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (x : Fin n → X) (ε : Ω n) (j : Fin n) :
    D j (lin x) ε = (((ε j : C) : ℝ) • x j) := by
  rw [D, lin_flip]
  module

end RadType
