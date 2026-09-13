import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem max_ineq_algebra {n : ℕ} (lam uii xc u D1b D2b : Fin n → ℝ)
    (uki ukiik : Fin n → Fin n → ℝ) (S rho b α β : ℝ)
    (hS3 : (∑ i : Fin n, (S - lam i)) = 3 * S)
    (hlam : ∀ i : Fin n, uii i = lam i)
    (huki2 : ∀ i : Fin n, (∑ k : Fin n, (uki k i) ^ 2) = (lam i) ^ 2)
    (h2 : (∑ i : Fin n, (S - lam i) * lam i) = 2)
    (hzero : ∀ k : Fin n, (∑ i : Fin n, (S - lam i) * ukiik k i) = 0) :
    (∑ i : Fin n, (S - lam i) *
        ((-4 / rho - 8 * (xc i) ^ 2 / rho ^ 2)
          + α * (uii i + ∑ k : Fin n, xc k * ukiik k i)
          + (β / 2) * (2 * (∑ k : Fin n, (uki k i) ^ 2)
              + 2 * ∑ k : Fin n, u k * ukiik k i)
          + (D2b i / b - (D1b i) ^ 2 / b ^ 2)))
      = -12 * S / rho - 8 * (∑ i : Fin n, (S - lam i) * (xc i) ^ 2) / rho ^ 2 + 2 * α
        + β * (∑ i : Fin n, (S - lam i) * (lam i) ^ 2)
        + (1 / b) * (∑ i : Fin n, (S - lam i) * D2b i)
        - (1 / b ^ 2) * (∑ i : Fin n, (S - lam i) * (D1b i) ^ 2) := by
  -- Evaluate the first ("linear") sum using the trace hypothesis.
  have e1 : (∑ i : Fin n, (S - lam i) * (-4 / rho)) = -12 * S / rho := by
    rw [← Finset.sum_mul, hS3]; ring
  -- Evaluate the second sum (quadratic in xc).
  have e2 : (∑ i : Fin n, (S - lam i) * (-8 * (xc i) ^ 2 / rho ^ 2))
      = -8 * (∑ i : Fin n, (S - lam i) * (xc i) ^ 2) / rho ^ 2 := by
    have h : ∀ i : Fin n, (S - lam i) * (-8 * (xc i) ^ 2 / rho ^ 2)
        = (-8 / rho ^ 2) * ((S - lam i) * (xc i) ^ 2) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]
    ring
  -- The α * uii sum equals 2 (uses uii = lam and the "2" hypothesis).
  have e3 : (∑ i : Fin n, (S - lam i) * uii i) = 2 := by
    have h : ∀ i : Fin n, (S - lam i) * uii i = (S - lam i) * lam i :=
      fun i => by rw [hlam i]
    rw [Finset.sum_congr rfl (fun i _ => h i), h2]
  -- The α * (cross term with xc) sum vanishes.
  have e4 : (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, xc k * ukiik k i)) = 0 := by
    have hpush : ∀ i : Fin n, (S - lam i) * (∑ k : Fin n, xc k * ukiik k i)
        = ∑ k : Fin n, (S - lam i) * (xc k * ukiik k i) :=
      fun i => by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => hpush i), Finset.sum_comm]
    have hinner : ∀ k : Fin n, (∑ i : Fin n, (S - lam i) * (xc k * ukiik k i)) = 0 := by
      intro k
      have h : ∀ i : Fin n, (S - lam i) * (xc k * ukiik k i)
          = xc k * ((S - lam i) * ukiik k i) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, hzero k, mul_zero]
    simp only [hinner, Finset.sum_const_zero]
  -- The β * uki sum reduces to the squared-lam sum.
  have e5 : (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, (uki k i) ^ 2))
      = (∑ i : Fin n, (S - lam i) * (lam i) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [huki2 i]
  -- The β * (cross term with u) sum vanishes.
  have e6 : (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, u k * ukiik k i)) = 0 := by
    have hpush : ∀ i : Fin n, (S - lam i) * (∑ k : Fin n, u k * ukiik k i)
        = ∑ k : Fin n, (S - lam i) * (u k * ukiik k i) :=
      fun i => by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => hpush i), Finset.sum_comm]
    have hinner : ∀ k : Fin n, (∑ i : Fin n, (S - lam i) * (u k * ukiik k i)) = 0 := by
      intro k
      have h : ∀ i : Fin n, (S - lam i) * (u k * ukiik k i)
          = u k * ((S - lam i) * ukiik k i) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, hzero k, mul_zero]
    simp only [hinner, Finset.sum_const_zero]
  -- Split the whole summand pointwise and distribute the outer sum.
  have hpt : ∀ i : Fin n, (S - lam i) *
        ((-4 / rho - 8 * (xc i) ^ 2 / rho ^ 2)
          + α * (uii i + ∑ k : Fin n, xc k * ukiik k i)
          + (β / 2) * (2 * (∑ k : Fin n, (uki k i) ^ 2)
              + 2 * ∑ k : Fin n, u k * ukiik k i)
          + (D2b i / b - (D1b i) ^ 2 / b ^ 2))
      = (S - lam i) * (-4 / rho) + (S - lam i) * (-8 * (xc i) ^ 2 / rho ^ 2)
        + α * ((S - lam i) * uii i) + α * ((S - lam i) * (∑ k : Fin n, xc k * ukiik k i))
        + β * ((S - lam i) * (∑ k : Fin n, (uki k i) ^ 2))
        + β * ((S - lam i) * (∑ k : Fin n, u k * ukiik k i))
        + (1 / b) * ((S - lam i) * D2b i) - (1 / b ^ 2) * ((S - lam i) * (D1b i) ^ 2) :=
    fun i => by ring
  have hmain : (∑ i : Fin n, (S - lam i) *
        ((-4 / rho - 8 * (xc i) ^ 2 / rho ^ 2)
          + α * (uii i + ∑ k : Fin n, xc k * ukiik k i)
          + (β / 2) * (2 * (∑ k : Fin n, (uki k i) ^ 2)
              + 2 * ∑ k : Fin n, u k * ukiik k i)
          + (D2b i / b - (D1b i) ^ 2 / b ^ 2)))
      = (∑ i : Fin n, (S - lam i) * (-4 / rho))
        + (∑ i : Fin n, (S - lam i) * (-8 * (xc i) ^ 2 / rho ^ 2))
        + α * (∑ i : Fin n, (S - lam i) * uii i)
        + α * (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, xc k * ukiik k i))
        + β * (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, (uki k i) ^ 2))
        + β * (∑ i : Fin n, (S - lam i) * (∑ k : Fin n, u k * ukiik k i))
        + (1 / b) * (∑ i : Fin n, (S - lam i) * D2b i)
        - (1 / b ^ 2) * (∑ i : Fin n, (S - lam i) * (D1b i) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hmain, e1, e2, e3, e4, e5, e6]
  ring

end Commons.Analysis.Sigma2