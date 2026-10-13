/-
  WilCrux/SphereChoicePos — the basic `Ω`-atom `{z : ℝ^m | z ≠ 0}`.

  The set of *nonzero* vectors in `ℝᵐ` is the complement of the zero set of the degree-`2`
  polynomial `Σᵢ Xᵢ²`, hence an `Ω`-set with format `m + 1` (one complement, `SOMin.compl`)
  and degree `2`.  As stated the lemma is exactly the membership

      `{z | 0 < ‖z‖} ∈ S.Ω (m+1) 2 m`.

  The only substantive point beyond `SOMin.hyp`/`SOMin.compl` is that the polynomial
  `Σᵢ Xᵢ²` has total degree at most `2` (for `m = 0` it is the zero polynomial, of degree `0`),
  combined with `SOMin.mono_D` to raise the forced degree `P.totalDegree` of `SOMin.hyp` up to
  the budget `2`.  Note the norm of `Fin m → ℝ` is the sup norm, so the identification
  `‖z‖ = 0 ↔ Σᵢ zᵢ² = 0 ↔ z = 0` goes through the vanishing of a sum of squares rather than
  through the Euclidean norm.
-/
import Mathlib
import Submission.Work.WilCrux.SphereChoiceDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-- The set of nonzero vectors of `ℝᵐ` is `Ω`-definable with format `m + 1` and degree `2`. -/
theorem SphereChoicePos (S : WilkiesDesign.SOMin) (m : ℕ) :
    {z : Fin m → ℝ | 0 < ‖z‖} ∈ S.Ω (m + 1) 2 m := by
  -- The polynomial whose zero set is `{0}`.
  set P : MvPolynomial (Fin m) ℝ := ∑ i : Fin m, (MvPolynomial.X i) ^ 2 with hP
  -- Its value is the sum of squares of the coordinates.
  have hsum : ∀ z : Fin m → ℝ, MvPolynomial.eval z P = ∑ i : Fin m, (z i) ^ 2 := by
    intro z; rw [hP]; simp
  -- … so it has total degree at most `2`.
  have htd : P.totalDegree ≤ 2 := by
    rw [hP]
    refine le_trans (MvPolynomial.totalDegree_finsetSum Finset.univ
      (fun i => (MvPolynomial.X i) ^ 2)) ?_
    refine Finset.sup_le ?_
    intro i _
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]
  -- The zero set of `P` is `Ω`-definable, at degree `2`.
  have hzero : {z : Fin m → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω m P.totalDegree m :=
    S.hyp m P
  have hzero2 : {z : Fin m → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω m 2 m :=
    Nat.le_induction hzero (fun _ _ ih => S.mono_D ih) 2 htd
  -- Its complement is the set of nonzero vectors.
  have hcompl := S.compl hzero2
  have hset : ({z : Fin m → ℝ | MvPolynomial.eval z P = 0})ᶜ = {z : Fin m → ℝ | 0 < ‖z‖} := by
    ext z
    show ¬ (MvPolynomial.eval z P = 0) ↔ 0 < ‖z‖
    have hz : (MvPolynomial.eval z P = 0) ↔ z = 0 := by
      rw [hsum z, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))]
      constructor
      · intro h; funext i; simpa using h i (Finset.mem_univ i)
      · intro h; subst h; simp
    rw [hz, norm_pos_iff]
  rwa [hset] at hcompl

end Work.WilCrux
