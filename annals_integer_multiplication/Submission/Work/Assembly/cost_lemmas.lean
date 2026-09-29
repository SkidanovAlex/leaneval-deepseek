import Mathlib
import Submission.Work.Assembly.Defs
import Submission.Work.Assembly.Base

namespace Work.Assembly

/-- `Nat.size m ≤ m` for every `m : ℕ` (the binary length never exceeds the number).
Local (private) copy: `assembly.lean` publishes the same fact under the name `size_le_self`. -/
private theorem cost_size_le_self (m : ℕ) : m.size ≤ m :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := m))

/-- `(m + 2)^2 ≤ 4 * (m + 1)^2`: the slack needed to absorb the `Kms` term. -/
private theorem cost_sq_succ_succ_le (m : ℕ) :
    (m + 2) * (m + 2) ≤ 4 * ((m + 1) * (m + 1)) := by nlinarith

/-- Arithmetic of the dispatcher cost function: the recursion's two clauses bound `dispCost`.
Uses `Nat.size_le_self`-style facts: `n₀ ≤ n → n₀.size ≤ n`, `(m+2)^2 ≤ 4*(m+1)^2`. -/
theorem cost_lemmas :
    (∀ C : ℕ, Monotone (HvdH.CmOf C)) ∧
    (∀ {S Kiz Kms Km C n₀ x y Kb : ℕ}, 2 * S + 3 * Kiz + 3 ≤ Kb → n₀ ≤ max x.size y.size →
      HvdH.mainCost Km (HvdH.CmOf C) (max x.size y.size) + Kb * (max x.size y.size + 1)
        ≤ HvdH.CmOf C (max x.size y.size) →
      Work.Assembly.dispCost S Kiz Kms Km C n₀ x y + 3 ≤ HvdH.CmOf C (max x.size y.size)) ∧
    (∀ {S Kiz Kms Km C n₀ x y Kb : ℕ}, 2 * S + 4 * Kiz + 4 * Kms + 3 ≤ Kb → max x.size y.size < n₀ →
      Kb * ((max x.size y.size + 1) ^ 2 + n₀.size) ≤ HvdH.CmOf C (max x.size y.size) →
      Work.Assembly.dispCost S Kiz Kms Km C n₀ x y + 3 ≤ HvdH.CmOf C (max x.size y.size)) ∧
    (∀ {C Kp Ke L M : ℕ}, M ≤ C * (L * L.size + 1) →
      2 + Kp * (L + 1) + M + Ke * (2 * L + 1) ≤ (C + Kp + 2 * Ke + 2) * (L * L.size + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `CmOf C` is monotone: `m ↦ m * m.size` is monotone because both factors are.
    intro C a b hab
    simp only [HvdH.CmOf]
    exact Nat.mul_le_mul_left C
      (Nat.add_le_add_right (Nat.mul_le_mul hab (Nat.size_le_size hab)) 1)
  · -- large-operand branch: `n₀ ≤ n`, the recursion hypothesis for the recursive step applies.
    intro S Kiz Kms Km C n₀ x y Kb hKb hn₀ hrec
    have hif : ¬ (max x.size y.size < n₀) := by omega
    have hsz : n₀.size ≤ max x.size y.size := le_trans (cost_size_le_self n₀) hn₀
    have key : S * (max x.size y.size + 1) + S * (n₀.size + 1)
        + (3 * Kiz + HvdH.mainCost Km (HvdH.CmOf C) (max x.size y.size)) + 3
        ≤ HvdH.CmOf C (max x.size y.size) := by
      have hpos : 1 ≤ max x.size y.size + 1 := by omega
      have hA : S * (n₀.size + 1) ≤ S * (max x.size y.size + 1) :=
        Nat.mul_le_mul_left S (by omega)
      nlinarith [hKb, hpos, hA, hrec]
    simp only [Work.Assembly.dispCost, Work.Assembly.overCost]
    rw [ite_eq_right hif]
    exact key
  · -- small-operand branch: `n < n₀`, the quadratic base-case hypothesis applies.
    intro S Kiz Kms Km C n₀ x y Kb hKb hlt hrec
    have key : S * (max x.size y.size + 1) + S * (n₀.size + 1)
        + (4 * Kiz + Kms * (max x.size y.size + 2) * (max x.size y.size + 2)) + 3
        ≤ HvdH.CmOf C (max x.size y.size) := by
      set M := max x.size y.size with hMdef
      set A := (M + 1) * (M + 1) + n₀.size with hAdef
      have hrec' : Kb * A ≤ HvdH.CmOf C M := by
        rw [hAdef, hMdef]
        simpa [pow_two] using hrec
      have hsq : M + 1 ≤ (M + 1) * (M + 1) := Nat.le_mul_self (M + 1)
      have hA1 : 1 ≤ A := by rw [hAdef]; nlinarith [hsq]
      have h1 : M + 1 ≤ A := by rw [hAdef]; omega
      have h2 : n₀.size + 1 ≤ A := by rw [hAdef]; nlinarith [hsq]
      have h3 : (M + 2) * (M + 2) ≤ 4 * A := by
        rw [hAdef]; nlinarith [cost_sq_succ_succ_le M]
      have h6 : S * (M + 1) ≤ S * A := Nat.mul_le_mul_left S h1
      have h7 : S * (n₀.size + 1) ≤ S * A := Nat.mul_le_mul_left S h2
      have h8 : Kms * ((M + 2) * (M + 2)) ≤ (4 * Kms) * A := by nlinarith [h3]
      have h9 : 4 * Kiz ≤ (4 * Kiz) * A := Nat.le_mul_of_pos_right (m := A) (4 * Kiz) (by omega)
      have h10 : (3 : ℕ) ≤ 3 * A := Nat.le_mul_of_pos_right (m := A) 3 (by omega)
      nlinarith [hKb, hrec', h6, h7, h8, h9, h10]
    simp only [Work.Assembly.dispCost, Work.Assembly.overCost]
    rw [ite_eq_left hlt]
    exact key
  · -- top-level numerical bound `M ≤ C (L log L + 1)`.
    intro C Kp Ke L M hM
    have hA : 1 ≤ L * L.size + 1 := by omega
    have hL : L ≤ L * L.size := by
      rcases Nat.eq_zero_or_pos L with h | h
      · simp [h]
      · have hsz : 0 < L.size := Nat.size_pos.mpr h
        exact Nat.le_mul_of_pos_right (m := L.size) L hsz
    have h1 : L + 1 ≤ L * L.size + 1 := by omega
    have h2 : 2 * L + 1 ≤ 2 * (L * L.size + 1) := by omega
    nlinarith [hM, hA, h1, h2]

end Work.Assembly
