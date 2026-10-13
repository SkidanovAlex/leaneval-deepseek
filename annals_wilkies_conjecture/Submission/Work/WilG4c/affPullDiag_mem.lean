import Mathlib
import Submission.Work.WilG4c.AffPullDefs
import Submission.Work.WilG0.diagSet_mem
import Submission.Work.WilG5.Basic

/-!
# The graph of an affine substitution is an `Ω`-set of degree `2`

The affine pull-back diagonal `Work.WilkG4c.affPullDiag N c M ⊆ ℝ^{N+N}` (the last `N`
coordinates equal `c + M·x` applied to the first `N`) is the zero set of the sum of squares
`Work.WilkG4c.affPullPoly N c M = Σ_i (W_i − c_i − Σ_j M_{ij} X_j)²`, which has total degree at
most two.  Hence it lies in `S.Ω (N+N) 2 (N+N)`, exactly as `Work.WilG0.diagSet_mem` does for
the linear substitution case.
-/

namespace Work.WilG4c

open WilkiesDesign

/-- Evaluation of the polynomial `affPullPoly`: it is the sum of squares
`Σ_i (z (natAdd N i) − c i − Σ_j M i j · z (castAdd N j))²`. -/
theorem eval_affPullPoly (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ)
    (z : Fin (N + N) → ℝ) :
    MvPolynomial.eval z (Work.WilkG4c.affPullPoly N c M)
      = ∑ i : Fin N,
          (z (Fin.natAdd N i) - c i - ∑ j : Fin N, M i j * z (Fin.castAdd N j)) ^ 2 := by
  rw [Work.WilkG4c.affPullPoly, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_sum]

/-- `affPullDiag N c M` is the zero set of the sum of squares `affPullPoly N c M`. -/
theorem affPullDiag_eq_zero (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) :
    Work.WilkG4c.affPullDiag N c M
      = {z : Fin (N + N) → ℝ | MvPolynomial.eval z (Work.WilkG4c.affPullPoly N c M) = 0} := by
  ext z
  rw [Work.WilkG4c.mem_affPullDiag, Set.mem_ofPred_eq, eval_affPullPoly]
  constructor
  · intro h
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [h i]; ring
  · intro h
    have hterm : ∀ i : Fin N,
        (z (Fin.natAdd N i) - c i - ∑ j : Fin N, M i j * z (Fin.castAdd N j)) ^ 2 = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : Fin N =>
          (z (Fin.natAdd N i) - c i - ∑ j : Fin N, M i j * z (Fin.castAdd N j)) ^ 2)
        (fun i _ => sq_nonneg _)).mp h i (Finset.mem_univ i)
    intro i
    have := hterm i
    nlinarith [sq_nonneg (z (Fin.natAdd N i) - c i - ∑ j : Fin N, M i j * z (Fin.castAdd N j))]

/-- `affPullPoly N c M` has total degree at most `2`, independently of `N`. -/
theorem affPullPoly_totalDegree_le (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) :
    (Work.WilkG4c.affPullPoly N c M).totalDegree ≤ 2 := by
  rw [Work.WilkG4c.affPullPoly]
  refine MvPolynomial.totalDegree_finsetSum_le (fun i _ => ?_)
  rw [pow_two]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hlin : (MvPolynomial.X (Fin.natAdd N i) - MvPolynomial.C (c i)
      - ∑ j : Fin N, MvPolynomial.C (M i j) * MvPolynomial.X (Fin.castAdd N j)
      : MvPolynomial (Fin (N + N)) ℝ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    refine max_le ?_ ?_
    · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
      refine max_le ?_ ?_
      · rw [MvPolynomial.totalDegree_X]
      · rw [MvPolynomial.totalDegree_C]; simp
    · refine MvPolynomial.totalDegree_finsetSum_le (fun j _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  omega

theorem affPullDiag_mem (S : WilkiesDesign.SOMin) (N : ℕ) (c : Fin N → ℝ)
    (M : Fin N → Fin N → ℝ) :
    Work.WilkG4c.affPullDiag N c M ∈ S.Ω (N + N) 2 (N + N) := by
  rw [affPullDiag_eq_zero N c M]
  exact Work.WilkG4c.Omega_mono_D_le S (affPullPoly_totalDegree_le N c M)
    (S.hyp (N + N) (Work.WilkG4c.affPullPoly N c M))

end Work.WilG4c
