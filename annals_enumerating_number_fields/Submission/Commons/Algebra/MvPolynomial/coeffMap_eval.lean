import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

private lemma prod_cast {K : Type*} [Field K] [CharZero K] {σ : Type*}
    (W : σ →₀ ℕ) (u : σ → ℚ) :
    W.prod (fun n e => ((u n : K)) ^ e) = ((W.prod (fun n e => (u n) ^ e) : ℚ) : K) := by
  rw [Finsupp.prod, Finsupp.prod]
  rw [show ((∏ a ∈ W.support, u a ^ W a : ℚ) : K) =
      algebraMap ℚ K (∏ a ∈ W.support, u a ^ W a) by simp]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n hn
  rw [map_pow]
  simp

private lemma term {K : Type*} [Field K] [CharZero K] {σ : Type*}
    (g : K →ₗ[ℚ] ℚ) (a : K) (m : σ →₀ ℕ) (u : σ → ℚ) :
    g (a * m.prod (fun n e => ((u n : K)) ^ e)) = g a * m.prod (fun n e => (u n) ^ e) := by
  rw [prod_cast m u]
  have h : a * ((m.prod fun n e => u n ^ e : ℚ) : K) =
      (m.prod fun n e => u n ^ e) • a := by
    rw [Algebra.smul_def]
    rw [show ((m.prod fun n e => u n ^ e : ℚ) : K) =
        algebraMap ℚ K (m.prod fun n e => u n ^ e) by simp]
    rw [mul_comm]
  rw [h, map_smul, smul_eq_mul, mul_comm]

/-- The coefficient-wise extension of a `ℚ`-linear functional `g : K →ₗ[ℚ] ℚ` to multivariable
polynomials, with its evaluation property. -/
theorem coeffMap_eval {K : Type*} [Field K] [CharZero K] {σ : Type*} (g : K →ₗ[ℚ] ℚ) :
    ∃ Φ : MvPolynomial σ K →ₗ[ℚ] MvPolynomial σ ℚ,
      ∀ (p : MvPolynomial σ K) (u : σ → ℚ),
        MvPolynomial.eval u (Φ p) = g (MvPolynomial.eval (fun s => (u s : K)) p) := by
  classical
  let Φ : MvPolynomial σ K →ₗ[ℚ] MvPolynomial σ ℚ :=
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := σ →₀ ℕ)).symm.toLinearMap ∘ₗ
      (Finsupp.mapRange.linearMap (α := σ →₀ ℕ) g) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := K) (M := σ →₀ ℕ)).toLinearMap
  refine ⟨Φ, ?_⟩
  intro p u
  have h1 : MvPolynomial.eval u (Φ p)
      = (Finsupp.mapRange g g.map_zero (AddMonoidAlgebra.coeff p)).sum
          (fun m a => a * m.prod (fun n e => u n ^ e)) := rfl
  have h2 : (Finsupp.mapRange g g.map_zero (AddMonoidAlgebra.coeff p)).sum
        (fun m a => a * m.prod (fun n e => u n ^ e))
      = (AddMonoidAlgebra.coeff p).sum (fun m a => g a * m.prod (fun n e => u n ^ e)) := by
    rw [Finsupp.sum_mapRange_index]
    intro a; simp
  have h3 : MvPolynomial.eval (fun s => (u s : K)) p
      = (AddMonoidAlgebra.coeff p).sum
          (fun m a => a * m.prod (fun n e => (u n : K) ^ e)) := rfl
  have h4 : g ((AddMonoidAlgebra.coeff p).sum
        (fun m a => a * m.prod (fun n e => (u n : K) ^ e)))
      = (AddMonoidAlgebra.coeff p).sum
          (fun m a => g (a * m.prod (fun n e => (u n : K) ^ e))) := by
    rw [map_finsuppSum]
  have h5 : (AddMonoidAlgebra.coeff p).sum
        (fun m a => g (a * m.prod (fun n e => (u n : K) ^ e)))
      = (AddMonoidAlgebra.coeff p).sum (fun m a => g a * m.prod (fun n e => u n ^ e)) := by
    apply Finsupp.sum_congr
    intro m hm
    exact term g ((AddMonoidAlgebra.coeff p) m) m u
  rw [h1, h2, h3, h4, h5]

end Commons.Algebra.MvPolynomial