import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.DiscRadial

/-- If the Hölder norm `holderNorm k α h Ω` of `h` is finite, then the operator norms
of the iterated (within) derivatives of `h` up to order `k` are uniformly bounded on
`Ω`.  Indeed each `iterDerivNorm i h Ω` is a summand of the (finite) Hölder norm hence
finite, and `∑_{i ≤ k} (iterDerivNorm i h Ω).toReal` is the required bound. -/
lemma iterDerivBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} {k : ℕ} {α : ℝ} {h : X → ℂ}
    (hfin : Work.CR.Flat.holderNorm k α h Ω ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ k → ∀ x : X, x ∈ Ω →
      ‖iteratedFDerivWithin ℝ j h Ω x‖ ≤ C := by
  refine ⟨∑ i ∈ Finset.range (k+1), (Work.CR.Flat.iterDerivNorm i h Ω).toReal, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  · intro j hj x hx
    have hmem : j ∈ Finset.range (k+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hterm : Work.CR.Flat.iterDerivNorm j h Ω ≠ ⊤ := by
      intro htop
      have hle : Work.CR.Flat.iterDerivNorm j h Ω ≤ Work.CR.Flat.holderNorm k α h Ω :=
        Work.CR.Flat.iterDerivNorm_le_holderNorm k α h Ω hj
      rw [htop] at hle
      exact hfin (top_le_iff.mp hle)
    have h2 : (ENNReal.ofReal ‖iteratedFDerivWithin ℝ j h Ω x‖).toReal
        ≤ (Work.CR.Flat.iterDerivNorm j h Ω).toReal :=
      ENNReal.toReal_mono hterm (Work.CR.Flat.le_iterDerivNorm j h Ω hx)
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    exact le_trans h2 (Finset.single_le_sum
      (f := fun i => (Work.CR.Flat.iterDerivNorm i h Ω).toReal)
      (fun i _ => ENNReal.toReal_nonneg) hmem)

end Work.NN.DiscRadial
