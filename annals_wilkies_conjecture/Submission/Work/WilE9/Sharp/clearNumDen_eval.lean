import Mathlib
import Submission.Work.WilE9.Sharp.Clear

namespace Work.WilE9.Sharp

/-- Arithmetic core: for `b ≠ 0` and `p ≤ K`, multiplying `(a/b)^p` by `b^K` and reading the
denominator back into the numerator. -/
private lemma pow_div_pow_sub {a b : ℝ} {K p : ℕ} (hb : b ≠ 0) (hp : p ≤ K) :
    b ^ K * (a / b) ^ p = a ^ p * b ^ (K - p) := by
  rw [div_pow, mul_div_assoc', mul_comm (b ^ K) (a ^ p), mul_div_assoc, div_eq_mul_inv,
    ← pow_sub₀ b hb hp]

/-- Evaluation of a single term of `clearNumDen` (the `C c * ∏_b X^{…} * ∏_c X^{…}` summand). -/
private lemma eval_prodX {β γ α : Type*} [Fintype β] [Fintype γ] (num den : β → α) (ρ : γ → α)
    (K : ℕ) (m : β ⊕ γ →₀ ℕ) (v : α → ℝ) (c : ℝ) :
    MvPolynomial.eval v (MvPolynomial.C c *
        (∏ b : β, MvPolynomial.X (num b) ^ (m (Sum.inl b)) * MvPolynomial.X (den b) ^ (K - m (Sum.inl b))) *
        (∏ c' : γ, MvPolynomial.X (ρ c') ^ (m (Sum.inr c')))) =
      c * (∏ b : β, v (num b) ^ (m (Sum.inl b)) * v (den b) ^ (K - m (Sum.inl b))) *
        (∏ c' : γ, v (ρ c') ^ (m (Sum.inr c'))) := by
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod,
    MvPolynomial.eval_pow, MvPolynomial.eval_X]

/-- The monomial-wise identity: the factor `(∏_b v (den b))^K` clears the denominators produced
by the substitution `X (inl b) ↦ v (num b) / v (den b)`, using `m (inl b) ≤ K`. -/
private lemma prod_key {β γ α : Type*} [Fintype β] [Fintype γ] (num den : β → α) (ρ : γ → α)
    (K : ℕ) (v : α → ℝ) (w : β ⊕ γ → ℝ) (m : β ⊕ γ →₀ ℕ)
    (hw_inl : ∀ b, w (Sum.inl b) = v (num b) / v (den b))
    (hw_inr : ∀ c', w (Sum.inr c') = v (ρ c'))
    (hle : ∀ b, m (Sum.inl b) ≤ K) (hd : ∀ b, v (den b) ≠ 0) :
    (∏ b : β, v (den b)) ^ K * (∏ i : β ⊕ γ, w i ^ m i) =
      (∏ b : β, v (num b) ^ (m (Sum.inl b)) * v (den b) ^ (K - m (Sum.inl b))) *
        (∏ c' : γ, v (ρ c') ^ (m (Sum.inr c'))) := by
  rw [← Finset.prod_pow, Fintype.prod_sum_type]
  simp only [hw_inl, hw_inr]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  exact pow_div_pow_sub (hd b) (hle b)

theorem clearNumDen_eval {β γ α : Type*} [Fintype β] [Fintype γ] (num den : β → α) (ρ : γ → α)
    (K : ℕ) (P : MvPolynomial (β ⊕ γ) ℝ) (v : α → ℝ)
    (hK : P.totalDegree ≤ K) (hd : ∀ b, v (den b) ≠ 0) :
    (∏ b : β, v (den b)) ^ K *
      MvPolynomial.eval (Sum.elim (fun b => v (num b) / v (den b)) (fun c => v (ρ c))) P =
      MvPolynomial.eval v (Work.WilE9.Sharp.clearNumDen num den ρ K P) := by
  classical
  set w : β ⊕ γ → ℝ := Sum.elim (fun b => v (num b) / v (den b)) (fun c => v (ρ c)) with hw
  have hw_inl : ∀ b, w (Sum.inl b) = v (num b) / v (den b) := fun b => by rw [hw]; rfl
  have hw_inr : ∀ c', w (Sum.inr c') = v (ρ c') := fun c' => by rw [hw]; rfl
  rw [clearNumDen, MvPolynomial.eval_sum, MvPolynomial.eval_eq' w P, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : ∀ b, m (Sum.inl b) ≤ K := by
    intro b
    have h1 : m.sum (fun _ e => e) ≤ K := le_trans (MvPolynomial.le_totalDegree hm) hK
    rw [Finsupp.sum_fintype m (fun _ e => e) (by intro i; rfl)] at h1
    exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ (Sum.inl b))) h1
  calc (∏ b : β, v (den b)) ^ K * (P.coeff m * ∏ i : β ⊕ γ, w i ^ m i)
      = P.coeff m * ((∏ b : β, v (den b)) ^ K * ∏ i : β ⊕ γ, w i ^ m i) := by ring
    _ = P.coeff m * ((∏ b : β, v (num b) ^ (m (Sum.inl b)) * v (den b) ^ (K - m (Sum.inl b))) *
          (∏ c' : γ, v (ρ c') ^ (m (Sum.inr c')))) := by
          rw [prod_key num den ρ K v w m hw_inl hw_inr hle hd]
    _ = P.coeff m * (∏ b : β, v (num b) ^ (m (Sum.inl b)) * v (den b) ^ (K - m (Sum.inl b))) *
          (∏ c' : γ, v (ρ c') ^ (m (Sum.inr c'))) := by ring
    _ = MvPolynomial.eval v (MvPolynomial.C (P.coeff m) *
          (∏ b : β, MvPolynomial.X (num b) ^ (m (Sum.inl b)) * MvPolynomial.X (den b) ^ (K - m (Sum.inl b))) *
          (∏ c' : γ, MvPolynomial.X (ρ c') ^ (m (Sum.inr c')))) :=
          (eval_prodX num den ρ K m v (P.coeff m)).symm

end Work.WilE9.Sharp
