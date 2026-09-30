import Mathlib
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.IntegralOn_gcd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial

/-- Evaluating the dilation `dil a P` at `x` gives `P.eval (a * x)`. -/
private theorem eval_dil' (a x : ℝ) (P : Polynomial ℝ) :
    (Work.BMF.dil a P).eval x = P.eval (a * x) := by
  simp only [Work.BMF.dil, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

/-- If `q` is the minimal natural modulus with `IntegralOn q γ` and `IntegralOn R γ`, then
`q ∣ R`.  The point is that the valid moduli are closed under `gcd`
(`IntegralOn_gcd`), while minimality of `q` makes `gcd q R = q`. -/
private theorem dvd_of_IntegralOn {k : ℕ} {γ : Polynomial ℝ} {q : ℕ} (hq1 : 1 ≤ q)
    (hdeg : γ.natDegree ≤ k) (hintq : Work.BMF.IntegralOn (q : ℝ) γ)
    (hmin : ∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) γ → q ≤ r)
    {R : ℕ} (hR : 1 ≤ R) (hintR : Work.BMF.IntegralOn (R : ℝ) γ) : q ∣ R := by
  have hg : Work.BMF.IntegralOn ((q.gcd R : ℕ) : ℝ) γ :=
    IntegralOn_gcd (a := q) (b := R) (by omega) (by omega) hdeg hintq hintR
  have h1 : 1 ≤ q.gcd R := Nat.gcd_pos_of_pos_left R (by omega)
  have hle : q ≤ q.gcd R := hmin (q.gcd R) h1 hg
  have hge : q.gcd R ≤ q := Nat.gcd_le_left R (by omega)
  have heq : q.gcd R = q := le_antisymm hge hle
  have hdvd : q.gcd R ∣ R := Nat.gcd_dvd_right q R
  rwa [heq] at hdvd

theorem goodQuad_q_eq {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ} {ℓ : ℕ}
    (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ) {δ : ℝ}
    {x₁ T₁ : ℝ} {q₁ qf₁ : ℕ} {γ₁ : Polynomial ℝ} {Ps₁ : Finset ℕ}
    {x₂ T₂ : ℝ} {q₂ qf₂ : ℕ} {γ₂ : Polynomial ℝ} {Ps₂ : Finset ℕ} {p₁ p₂ : ℕ}
    (h₁ : Work.BMF.GoodQuad A δ x₁ T₁ q₁ qf₁ γ₁ Ps₁)
    (h₂ : Work.BMF.GoodQuad A δ x₂ T₂ q₂ qf₂ γ₂ Ps₂)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hint : Work.BMF.IntegralOn 1 (Work.BMF.dil (p₂ : ℝ) γ₁ - Work.BMF.dil (p₁ : ℝ) γ₂))
    (hd₁ : ¬ p₁ ∣ q₂) (hd₂ : ¬ p₂ ∣ q₁) : q₁ = q₂ := by
  have hdeg1 : γ₁.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact Polynomial.mem_degreeLE.mp h₁.deg
  have hdeg2 : γ₂.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact Polynomial.mem_degreeLE.mp h₂.deg
  -- Step A: `IntegralOn (p₂ * q₂) γ₁`.
  have hA : Work.BMF.IntegralOn (((p₂ * q₂ : ℕ) : ℝ)) γ₁ := by
    intro n
    obtain ⟨m₁, hm₁⟩ := hint ((q₂ : ℤ) * n)
    obtain ⟨m₂, hm₂⟩ := h₂.int_coarse ((p₁ : ℤ) * n)
    refine ⟨m₁ + m₂, ?_⟩
    have hcast1 : (↑((q₂ : ℤ) * n) : ℝ) = (q₂ : ℝ) * (n : ℝ) := by push_cast; ring
    have hcast2 : (↑((p₁ : ℤ) * n) : ℝ) = (p₁ : ℝ) * (n : ℝ) := by push_cast; ring
    rw [Polynomial.eval_sub, eval_dil', eval_dil', one_mul, hcast1] at hm₁
    rw [hcast2] at hm₂
    rw [show (p₁ : ℝ) * ((q₂ : ℝ) * (n : ℝ)) = (q₂ : ℝ) * ((p₁ : ℝ) * (n : ℝ)) by ring]
      at hm₁
    rw [hm₂] at hm₁
    rw [show ((p₂ * q₂ : ℕ) : ℝ) * (n : ℝ) = (p₂ : ℝ) * ((q₂ : ℝ) * (n : ℝ)) by
      push_cast; ring]
    push_cast
    linarith
  -- Step B: `IntegralOn (p₁ * q₁) γ₂`.
  have hB : Work.BMF.IntegralOn (((p₁ * q₁ : ℕ) : ℝ)) γ₂ := by
    intro n
    obtain ⟨m₁, hm₁⟩ := h₁.int_coarse ((p₂ : ℤ) * n)
    obtain ⟨m₂, hm₂⟩ := hint ((q₁ : ℤ) * n)
    refine ⟨m₁ - m₂, ?_⟩
    have hcastp : (↑((p₂ : ℤ) * n) : ℝ) = (p₂ : ℝ) * (n : ℝ) := by push_cast; ring
    have hcastq : (↑((q₁ : ℤ) * n) : ℝ) = (q₁ : ℝ) * (n : ℝ) := by push_cast; ring
    rw [hcastp] at hm₁
    rw [show (q₁ : ℝ) * ((p₂ : ℝ) * (n : ℝ)) = (p₂ : ℝ) * ((q₁ : ℝ) * (n : ℝ)) by ring]
      at hm₁
    rw [Polynomial.eval_sub, eval_dil', eval_dil', one_mul, hcastq] at hm₂
    rw [hm₁] at hm₂
    rw [show ((p₁ * q₁ : ℕ) : ℝ) * (n : ℝ) = (p₁ : ℝ) * ((q₁ : ℝ) * (n : ℝ)) by
      push_cast; ring]
    push_cast
    linarith
  have hR1 : 1 ≤ p₂ * q₂ := one_le_mul hp₂.one_le h₂.q_bound
  have hR2 : 1 ≤ p₁ * q₁ := one_le_mul hp₁.one_le h₁.q_bound
  have hdiv1 : q₁ ∣ p₂ * q₂ :=
    dvd_of_IntegralOn h₁.q_bound hdeg1 h₁.int_coarse h₁.minimal hR1 hA
  have hdiv2 : q₂ ∣ p₁ * q₁ :=
    dvd_of_IntegralOn h₂.q_bound hdeg2 h₂.int_coarse h₂.minimal hR2 hB
  have hc1 : q₁ ∣ q₂ :=
    ((hp₂.coprime_iff_not_dvd.mpr hd₂).symm).dvd_of_dvd_mul_left hdiv1
  have hc2 : q₂ ∣ q₁ :=
    ((hp₁.coprime_iff_not_dvd.mpr hd₁).symm).dvd_of_dvd_mul_left hdiv2
  exact Nat.dvd_antisymm hc1 hc2

end Work.N8
