import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

noncomputable section

/-- The coefficient-wise extension of a `ℚ`-linear functional `g : K →ₗ[ℚ] ℚ` to multivariable
polynomials, with its evaluation property and degree bound. -/
theorem coeffMap_totalDegree_eval {K : Type*} [Field K] [CharZero K] {σ : Type*} (g : K →ₗ[ℚ] ℚ) :
    ∃ Φ : MvPolynomial σ K →ₗ[ℚ] MvPolynomial σ ℚ,
      (∀ p, (Φ p).totalDegree ≤ p.totalDegree) ∧
      ∀ (p : MvPolynomial σ K) (u : σ → ℚ),
        MvPolynomial.eval u (Φ p) = g (MvPolynomial.eval (fun s => (u s : K)) p) := by
  let Φ : MvPolynomial σ K →ₗ[ℚ] MvPolynomial σ ℚ :=
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := σ →₀ ℕ)).symm.toLinearMap ∘ₗ
      Finsupp.mapRange.linearMap (α := σ →₀ ℕ) g ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := K) (M := σ →₀ ℕ)).toLinearMap
  have hcoeff : ∀ p : MvPolynomial σ K,
      AddMonoidAlgebra.coeff (Φ p)
        = Finsupp.mapRange g g.map_zero (AddMonoidAlgebra.coeff p) := fun _ => rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro p
    have hsub : (Φ p).support ⊆ p.support := by
      show (AddMonoidAlgebra.coeff (Φ p)).support ⊆ (AddMonoidAlgebra.coeff p).support
      rw [hcoeff p]
      exact Finsupp.support_mapRange
    rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree]
    exact Finset.sup_mono hsub
  · intro p u
    have hL : MvPolynomial.eval u (Φ p)
        = (AddMonoidAlgebra.coeff p).sum (fun s a => g a * s.prod fun n e => u n ^ e) := by
      rw [show MvPolynomial.eval u (Φ p)
          = (Finsupp.mapRange g g.map_zero (AddMonoidAlgebra.coeff p)).sum
              (fun s a => a * s.prod fun n e => u n ^ e) from by
        show MvPolynomial.eval₂ (RingHom.id ℚ) u (Φ p) = _
        show (AddMonoidAlgebra.coeff (Φ p)).sum
            (fun s a => (RingHom.id ℚ) a * s.prod fun n e => u n ^ e) = _
        rw [hcoeff p]
        simp]
      rw [Finsupp.sum_mapRange_index]
      · intro a
        simp
    have hR : g (MvPolynomial.eval (fun s => (u s : K)) p)
        = (AddMonoidAlgebra.coeff p).sum (fun s a => g a * s.prod fun n e => u n ^ e) := by
      show g ((AddMonoidAlgebra.coeff p).sum
            (fun s a => a * s.prod fun n e => ((u n : ℚ) : K) ^ e)) = _
      rw [Finsupp.sum, map_sum]
      rw [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro s _
      have hprod : (s.prod fun n e => ((u n : ℚ) : K) ^ e)
          = algebraMap ℚ K (s.prod fun n e => (u n) ^ e) := by
        rw [Finsupp.prod, Finsupp.prod, map_prod]
        apply Finset.prod_congr rfl
        intro n _
        rw [map_pow]
        rfl
      rw [hprod]
      have hsmul : (AddMonoidAlgebra.coeff p) s
            * algebraMap ℚ K (s.prod fun n e => (u n) ^ e)
          = (s.prod fun n e => (u n) ^ e) • ((AddMonoidAlgebra.coeff p) s) := by
        rw [Algebra.smul_def]
        ring
      rw [hsmul, map_smul]
      simp [mul_comm]
    rw [hL, hR]

end

end Commons.Algebra.MvPolynomial