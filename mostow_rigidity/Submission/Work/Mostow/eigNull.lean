import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper

/-!
# Eigenvectors of a Lorentz transformation with eigenvalue `≠ ±1` are null

`A : O1 n = O(n,1)` preserves the Minkowski form `mink x y = Σ xᵢyᵢ − x₀y₀` on
`ℝ^{Fin n ⊕ Fin 1}`, so for an eigenvector `v` of the underlying matrix with eigenvalue `lam`,

  `mink v v = mink (A v) (A v) = lam ^ 2 * mink v v`,

whence `(lam ^ 2 - 1) * mink v v = 0`.  If `lam ^ 2 ≠ 1` then `mink v v = 0`: `v` is a null
(lightlike) vector.

The concrete definition of `mink` used by the statement (from `QIDefs`) agrees
with `Submission.Mostow.Hyper.mink`, where the `J`-orthogonality of `O(n,1)` is already available.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

/-- `Work.Mostow.mink` is the Minkowski form of the `Hyper` toolkit. -/
lemma eigNull_mink_eq_hyper {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x y = Submission.Mostow.Hyper.mink x y := by
  rw [Submission.Mostow.Hyper.mink_apply]; rfl

/-- Bilinearity of `mink` on scalar multiples. -/
lemma eigNull_mink_smul {n : ℕ} (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) (s • y) = r * s * mink x y := by
  rw [eigNull_mink_eq_hyper, eigNull_mink_eq_hyper]
  exact Submission.Mostow.Hyper.mink_smul r s x y

/-- The underlying matrix of `A : O1 n` preserves the Minkowski form. -/
lemma eigNull_mat_mink {n : ℕ} (A : O1 n) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink ((mat A).mulVec x) ((mat A).mulVec y) = mink x y := by
  rw [eigNull_mink_eq_hyper, eigNull_mink_eq_hyper]
  exact Submission.Mostow.Hyper.mink_mulVec (mat A) (Submission.Mostow.Hyper.mat_conj A) x y

theorem eigNull (n : ℕ) (A : O1 n) (lam : ℝ) (v : Fin n ⊕ Fin 1 → ℝ) (hv : v ≠ 0)
    (heig : Matrix.mulVec (mat A) v = lam • v) (hlam : lam ^ 2 ≠ 1) : mink v v = 0 := by
  -- `A` preserves the Minkowski form, and `A v = lam • v` is an eigenvector equation
  have hpres : mink ((mat A).mulVec v) ((mat A).mulVec v) = mink v v :=
    eigNull_mat_mink A v v
  have hpair : mink v v = lam * lam * mink v v :=
    calc mink v v = mink ((mat A).mulVec v) ((mat A).mulVec v) := hpres.symm
      _ = mink (lam • v) (lam • v) := by rw [heig]
      _ = lam * lam * mink v v := eigNull_mink_smul lam lam v v
  -- hence `(lam ^ 2 - 1) * mink v v = 0`, and `lam ^ 2 ≠ 1` kills the factor
  have hzero : (lam * lam - 1) * mink v v = 0 := by nlinarith [hpair]
  have hne : lam * lam - 1 ≠ 0 := by
    intro hc
    exact hlam (by nlinarith [hc])
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hne
  · exact h

end Work.Mostow
