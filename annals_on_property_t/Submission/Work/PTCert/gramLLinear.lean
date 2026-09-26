import Mathlib
import Submission.Work.PTCert.Interfaces

namespace Work.PTCert

/-- The index set of the letter pairs `(a, b)` over which `gramL` sums. -/
private def ptSet (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Submission.PTCert.NB1 r)).product (Finset.range (Submission.PTCert.NB1 r))

/-- The monomial `of ((b1 r a)⁻¹ * b1 r b)` attached to a letter pair. -/
private noncomputable def ptMon (r : ℕ) (p : ℕ × ℕ) :
    MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))) :=
  MonoidAlgebra.of ℝ _ ((Submission.PTCert.b1 r p.1)⁻¹ * Submission.PTCert.b1 r p.2)

/-- `gramL` as a single sum over the product index set of letter pairs. -/
private lemma gramL_prod (r : ℕ) (Q : ℕ → ℕ → ℚ) :
    Submission.PTCert.gramL r Q = ∑ p ∈ ptSet r, ((Q p.1 p.2 : ℚ) : ℝ) • ptMon r p := by
  rw [Submission.PTCert.gramL]
  exact (Finset.sum_product (s := Finset.range (Submission.PTCert.NB1 r))
    (t := Finset.range (Submission.PTCert.NB1 r))
    (f := fun p : ℕ × ℕ => ((Q p.1 p.2 : ℚ) : ℝ) •
      MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r)))
        ((Submission.PTCert.b1 r p.1)⁻¹ * Submission.PTCert.b1 r p.2))).symm

theorem gramLLinear (r : ℕ) (Q Q1 Q2 : ℕ → ℕ → ℚ) :
    (Submission.PTCert.gramL r (fun a b => Q1 a b + Q2 a b) = Submission.PTCert.gramL r Q1 + Submission.PTCert.gramL r Q2) ∧
    (Submission.PTCert.gramL r (fun a b => Q1 a b - Q2 a b) = Submission.PTCert.gramL r Q1 - Submission.PTCert.gramL r Q2) ∧
    (∀ c : ℚ, Submission.PTCert.gramL r (fun a b => c * Q a b) = (c : ℝ) • Submission.PTCert.gramL r Q) ∧
    (∀ {ι : Type} (s : Finset ι) (Qf : ι → ℕ → ℕ → ℚ),
      Submission.PTCert.gramL r (fun a b => ∑ t ∈ s, Qf t a b) = ∑ t ∈ s, Submission.PTCert.gramL r (Qf t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gramL_prod]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Rat.cast_add, add_smul]
  · simp only [gramL_prod]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Rat.cast_sub, sub_smul]
  · intro c
    simp only [gramL_prod]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Rat.cast_mul, mul_smul]
  · intro ι s Qf
    simp only [gramL_prod]
    simp only [Rat.cast_sum, Finset.sum_smul]
    rw [Finset.sum_comm]

end Work.PTCert
