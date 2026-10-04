import Mathlib
import Submission.Work.Diff.EXT.covK_frameInv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The multilinear map `krVLin g x k hM` (arguments indexed by `Fin (k + 4)`: the first `k`
differentiation slots, then the four curvature slots) evaluated on a packed tuple `q` is the
corresponding `covKRm` component. -/
lemma krVLin_eq_covKRm (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti (I := I) (M := M) g x k) (q : Fin (k + 4) → TangentSpace I x) :
    krVLin g x k hM q
      = covKRm g x k (fun i : Fin k => q (Fin.castAdd 4 i)) (q (Fin.natAdd k 0))
          (q (Fin.natAdd k 1)) (q (Fin.natAdd k 2)) (q (Fin.natAdd k 3)) := by
  change krVCur g x k (fun i : Fin k ⊕ Fin 4 => q (finSumFinEquiv i)) = _
  simp only [krVCur, krV, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- **Multilinear expansion of a component of `∇^k Rm` on a frame (packed form).**

`covKRm g x k` is the `(0,k+4)`-tensor `∇^k Rm` evaluated on `k` derivative slots and four curvature
slots.  Its value-level multilinearity `KrMulti g x k` implies that, when each of the `k+4` slots is
a linear combination `∑ r, cp j r • a r` of a family `a`, the value is the corresponding sum over
index tuples of the products of coefficients times the values on `a`.  Here the `k+4` slots are
packed as the index type `Fin (k+4)` (first `k` derivative slots, last four curvature slots). -/
theorem covKRm_expand_packed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (hM : KrMulti (I := I) (M := M) g x k)
    {n : ℕ} (a : Fin n → TangentSpace I x) (p : Fin (k + 4) → TangentSpace I x)
    (cp : Fin (k + 4) → Fin n → ℝ)
    (hp : ∀ j : Fin (k + 4), ∑ r, cp j r • a r = p j) :
    covKRm g x k (fun i : Fin k => p (Fin.castAdd 4 i)) (p (Fin.natAdd k 0))
        (p (Fin.natAdd k 1)) (p (Fin.natAdd k 2)) (p (Fin.natAdd k 3))
      = ∑ r : Fin (k + 4) → Fin n, (∏ j : Fin (k + 4), cp j (r j)) *
          covKRm g x k (fun i : Fin k => a (r (Fin.castAdd 4 i))) (a (r (Fin.natAdd k 0)))
            (a (r (Fin.natAdd k 1))) (a (r (Fin.natAdd k 2))) (a (r (Fin.natAdd k 3))) := by
  classical
  rw [← krVLin_eq_covKRm g x k hM p]
  have hp' : (fun j : Fin (k + 4) => ∑ r, cp j r • a r) = p := funext hp
  rw [← hp', MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [MultilinearMap.map_smul_univ, krVLin_eq_covKRm]
  simp only [smul_eq_mul]

end Work.Diff.EXT
