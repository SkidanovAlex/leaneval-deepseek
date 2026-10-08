import Mathlib
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmG

private lemma add_eq_zero_of_zero_one {x y : ℂ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (h : x + y = 0) : x = 0 ∧ y = 0 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all

theorem arith_case {A1 A2 B1 B2 P Q ε ε₀ : ℂ} {a : ℕ}
    (hP : P = 0 ∨ P = 1) (hQ : Q = 0 ∨ Q = 1)
    (hPsum : P = A1 + A2) (hQsum : Q = B1 + B2)
    (hA1 : A1 = 0 ∨ A1 = 1) (hA2 : A2 = 0 ∨ A2 = 1)
    (hB1 : B1 = 0 ∨ B1 = 1) (hB2 : B2 = 0 ∨ B2 = 1)
    (hε : ε = 1 ∨ ε = -1) (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (ha : 1 ≤ a)
    (h : ε * P = (a : ℂ) * ε₀ * Q) :
    (A1 = 0 ∧ A2 = 0 ∧ B1 = 0 ∧ B2 = 0) ∨ (a = 1 ∧ P = 1 ∧ Q = 1 ∧ ε = ε₀) := by
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hε₀ne : ε₀ ≠ 0 := by rcases hε₀ with h | h <;> simp [h]
  have hε₀sq : ε₀ * ε₀ = 1 := by rcases hε₀ with h | h <;> simp [h]
  rcases hQ with hQ | hQ
  · rw [hQ] at h
    have hP0 : P = 0 := by
      have hzero : ε * P = 0 := by simpa using h
      exact (mul_eq_zero.mp hzero).resolve_left hεne
    have hA : A1 = 0 ∧ A2 = 0 := add_eq_zero_of_zero_one hA1 hA2 (by rw [← hPsum, hP0])
    have hB : B1 = 0 ∧ B2 = 0 := add_eq_zero_of_zero_one hB1 hB2 (by rw [← hQsum, hQ])
    exact Or.inl ⟨hA.1, hA.2, hB.1, hB.2⟩
  · rw [hQ] at h
    rcases hP with hP | hP
    · exfalso
      rw [hP] at h
      have hzero : (a : ℂ) * ε₀ = 0 := by simpa using h.symm
      have hcast : (a : ℂ) = 0 := (mul_eq_zero.mp hzero).resolve_right hε₀ne
      have : a = 0 := Nat.cast_eq_zero.mp hcast
      omega
    · rw [hP] at h
      have heq : ε = (a : ℂ) * ε₀ := by simpa using h
      have hcast : (a : ℂ) = ε * ε₀ := by
        have h1 : ε * ε₀ = (a : ℂ) * (ε₀ * ε₀) := by rw [heq]; ring
        rw [h1, hε₀sq, mul_one]
      rcases hε with hε | hε <;> rcases hε₀ with hε₀ | hε₀
      · exact Or.inr ⟨Nat.cast_eq_one.mp (by rw [hcast, hε, hε₀]; norm_num), hP, hQ,
          by rw [hε, hε₀]⟩
      · exfalso
        have hneg : (a : ℂ) = -1 := by rw [hcast, hε, hε₀]; norm_num
        have hre := congrArg Complex.re hneg
        simp [Complex.natCast_re] at hre
        have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        linarith
      · exfalso
        have hneg : (a : ℂ) = -1 := by rw [hcast, hε, hε₀]; norm_num
        have hre := congrArg Complex.re hneg
        simp [Complex.natCast_re] at hre
        have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        linarith
      · exact Or.inr ⟨Nat.cast_eq_one.mp (by rw [hcast, hε, hε₀]; norm_num), hP, hQ,
          by rw [hε, hε₀]⟩

end Work.ThmG
