import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A sectional curvature at most the average `scalAlg / (n(n-1))`

`Work.Diff.L.exists_isONPair_secK_le_scalAlg_div` is the "min" half of the elementary fact that the
mean value of the sectional curvatures of an algebraic curvature tensor over an orthonormal frame is
`scalAlg R / (n (n-1))`.  The proof runs through the standard basis:

* `scalAlg_eq_sum_offDiag`: the diagonal components `R i i i i` vanish (antisymmetry), so the scalar
  curvature is the sum of the `n (n-1)` off-diagonal components `R i j i j`;
* `card_offDiag_fin`/`cast_card_offDiag_fin`: the off-diagonal index set `univ.offDiag` of
  `Fin n × Fin n` has `n (n-1)` elements;
* hence the minimum of `R i j i j` over the off-diagonal pairs is at most the average, and that
  minimum is attained at a pair of distinct standard basis vectors, which are orthonormal
  (`Work.Diff.Alg.PA.isONPair_stdB`) with `secK R (stdB n i) (stdB n j) = R i j i j`
  (`Work.Diff.Alg.PA.secK_stdB`).
-/

namespace Work.Diff.L

open Finset Submission.Diff.Alg Work.Diff.Alg.PA

/-- The scalar curvature of an algebraic curvature tensor is the sum of its off-diagonal components
`R i j i j` (the diagonal ones vanish by antisymmetry). -/
theorem scalAlg_eq_sum_offDiag {n : ℕ} {R : Curv4 n} (hR : IsAlgCurv R) :
    ∑ p ∈ (Finset.univ.offDiag : Finset (Fin n × Fin n)), R p.1 p.2 p.1 p.2 = scalAlg R := by
  have hdiag : ∀ i : Fin n, R i i i i = 0 := by
    intro i
    have h := hR.1 i i i i
    linarith
  have h1 : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), R p.1 p.2 p.1 p.2 = scalAlg R := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [← h1]
  refine Finset.sum_subset (fun p _ => Finset.mem_univ p) ?_
  intro p _ hp
  have hp12 : p.1 = p.2 := by
    by_contra h
    exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, h⟩)
  rw [hp12, hdiag]

/-- The off-diagonal of `Fin n × Fin n` has `n (n-1)` elements. -/
theorem card_offDiag_fin (n : ℕ) :
    (Finset.univ.offDiag : Finset (Fin n × Fin n)).card = n * (n - 1) := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  exact (Nat.mul_sub_one n n).symm

/-- The cardinality of the off-diagonal of `Fin n × Fin n`, as a real number:
`n (n-1)`. -/
theorem cast_card_offDiag_fin {n : ℕ} (hn : 2 ≤ n) :
    ((Finset.univ.offDiag : Finset (Fin n × Fin n)).card : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
  rw [card_offDiag_fin, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]

/-- **A pair of orthonormal vectors whose sectional curvature is at most the mean sectional
curvature `scalAlg R / (n (n-1))`.**  The pair is a pair of distinct standard basis vectors in some
orthonormal frame. -/
theorem exists_isONPair_secK_le_scalAlg_div {n : ℕ} (hn : 2 ≤ n)
    {R : Submission.Diff.Alg.Curv4 n} (hR : Submission.Diff.Alg.IsAlgCurv R) :
    ∃ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v ∧
      Submission.Diff.Alg.secK R u v ≤ Submission.Diff.Alg.scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)) := by
  classical
  have hoff : (Finset.univ.offDiag : Finset (Fin n × Fin n)).Nonempty := by
    rw [← Finset.card_pos, card_offDiag_fin]
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (Finset.univ.offDiag : Finset (Fin n × Fin n)) (fun p => R p.1 p.2 p.1 p.2) hoff
  have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- the minimum is at most the mean over the `n (n-1)` off-diagonal pairs
  have hmean : R p.1 p.2 p.1 p.2 * ((n : ℝ) * ((n : ℝ) - 1)) ≤ scalAlg R := by
    have hle : ∑ q ∈ (Finset.univ.offDiag : Finset (Fin n × Fin n)), R p.1 p.2 p.1 p.2
        ≤ ∑ q ∈ (Finset.univ.offDiag : Finset (Fin n × Fin n)), R q.1 q.2 q.1 q.2 :=
      Finset.sum_le_sum (fun q hq => hmin q hq)
    rw [Finset.sum_const, nsmul_eq_mul, scalAlg_eq_sum_offDiag hR, cast_card_offDiag_fin hn]
      at hle
    linarith
  have hfin : R p.1 p.2 p.1 p.2 ≤ scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [le_div_iff₀ hpos]
    linarith
  obtain ⟨_, _, hpne⟩ := Finset.mem_offDiag.mp hp
  exact ⟨stdB n p.1, stdB n p.2, isONPair_stdB hpne, by rw [secK_stdB]; exact hfin⟩

end Work.Diff.L
