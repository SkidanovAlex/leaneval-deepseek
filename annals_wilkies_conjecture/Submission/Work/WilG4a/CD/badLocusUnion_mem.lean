import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells

namespace Work.WilG4a.CD

/-- Monotonicity of `MvPolynomial.eval` for polynomials with *natural* coefficients: if the
evaluation points are compared pointwise, so are the values.  (Here all coefficients, hence all
monomial evaluations, are nonnegative.) -/
theorem eval_le_eval_of_le {σ : Type*} {f g : σ → ℕ} (h : ∀ s, f s ≤ g s)
    (b : MvPolynomial σ ℕ) :
    MvPolynomial.eval f b ≤ MvPolynomial.eval g b := by
  induction b using MvPolynomial.induction_on' with
  | monomial u a =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Finset.prod_le_prod (fun s _ => Nat.pow_le_pow_left (h s) _))
  | add p q hp hq =>
      rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
      exact add_le_add hp hq

/-- The union of the first `j + 1` bad loci is `Ω`-definable, with format and degree depending
only on the input format `F0`, the ambient dimension `p`, the degree `D` and the order `j`.

The point is that the degree of the union is the *sum* of the degrees of the `j + 1` bad loci;
each of these is bounded by the degree of the `j`-th one (monotonicity of the degree polynomial
in its second argument, since its coefficients are natural numbers), so `b * (X 1 + 1)` bounds
the sum. -/
theorem badLocusUnion_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        (⋃ m ∈ Finset.range (j + 1), Work.WilG4a.badLocus f m) ∈
          S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := Work.WilG4a.badLocus_mem S hder p F0
  refine ⟨a, b * (MvPolynomial.X 1 + 1), ?_⟩
  intro D j f hf
  -- Re-index the union over `Finset.range (j+1)` as a union over `Fin (j+1)`.
  have hset : (⋃ m ∈ Finset.range (j + 1), Work.WilG4a.badLocus f m) =
      ⋃ i : Fin (j + 1), Work.WilG4a.badLocus f (i : ℕ) := by
    ext z
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, hz⟩
      exact ⟨⟨m, hm⟩, hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨i, i.isLt, hz⟩
  rw [hset]
  -- Each bad locus has degree `eval ![D, i] b`; the degree of the `j`-th one dominates them all.
  have hsum : (∑ i : Fin (j + 1), MvPolynomial.eval ![D, (i : ℕ)] b) ≤
      MvPolynomial.eval ![D, j] b * (j + 1) := by
    have h1 : ∀ i : Fin (j + 1),
        MvPolynomial.eval ![D, (i : ℕ)] b ≤ MvPolynomial.eval ![D, j] b := by
      intro i
      apply eval_le_eval_of_le
      intro s
      fin_cases s
      · simp
      · simpa using (Nat.lt_succ_iff.mp i.isLt : ((i : ℕ) ≤ j))
    calc (∑ i : Fin (j + 1), MvPolynomial.eval ![D, (i : ℕ)] b)
        ≤ ∑ _i : Fin (j + 1), MvPolynomial.eval ![D, j] b :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = (j + 1) * MvPolynomial.eval ![D, j] b := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = MvPolynomial.eval ![D, j] b * (j + 1) := by rw [Nat.mul_comm]
  have hkey : MvPolynomial.eval ![D, j] (b * (MvPolynomial.X 1 + 1)) =
      MvPolynomial.eval ![D, j] b * (j + 1) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_X]
    simp
  rw [hkey]
  exact Work.WilG4a.mono_D_le S
    (S.union (fun i : Fin (j + 1) => MvPolynomial.eval ![D, (i : ℕ)] b)
      (fun i : Fin (j + 1) => Work.WilG4a.badLocus f (i : ℕ))
      (fun i => hb D (i : ℕ) hf)) hsum

end Work.WilG4a.CD
