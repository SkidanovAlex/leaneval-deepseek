import Mathlib
import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree no-common-root combinations of integer polynomials (Phase D1: statements)

Smith, prelim.tex, `lem:squarefree_nocommon` (reduced form): if integer polynomials
`S i` (deg ≤ m, some deg = m) have NO common complex root, then a small integer
linear combination `S i₀ + Σ_{i≠i₀} b_i·S i` with `0 ≤ b_i ≤ 2m` is squarefree of
degree m.  The only purpose of this file is the shared definitions; the theorems
are delegated per-file (CubeLemma, NocommonCore, GcdInt, ...).
-/

noncomputable section

open Polynomial

namespace Submission.Nocommon

/-- A squarefree integer polynomial of degree `m` over ℂ:  `natDegree = m` and no
repeated complex root (equivalently, over the algebraically closed field ℂ, the
polynomial is Separable). -/
def DistinctRootData (A : Polynomial ℤ) (m : ℕ) : Prop :=
  A.natDegree = m ∧ (A.map (algebraMap ℤ ℂ)).Separable

/-- The integer combination with lead coefficient 1 at index `i₀` and integer
weights `b` elsewhere:  `A = S i₀ + Σ_{i ≠ i₀} (b i)·(S i)`, i.e. in `CombPoly`
terms `b i₀ = 1`.  All weights (including the lead's) are `≤ 2m + 1`; the
non-lead weights of interest lie in `[0, 2m]`. -/
def CombData (m : ℕ) (K : ℕ) (i₀ : Fin (K+1)) (S : Fin (K+1) → Polynomial ℤ)
    (b : Fin (K+1) → ℕ) : Prop :=
  b i₀ = 1 ∧ (∀ i, b i ≤ 2 * m + 1)

/-- The combination polynomial of `CombData`. -/
def CombPoly (K : ℕ) (S : Fin (K+1) → Polynomial ℤ) (b : Fin (K+1) → ℕ) : Polynomial ℤ :=
  ∑ i : Fin (K+1), Polynomial.C ((b i : ℕ) : ℤ) * S i

end Submission.Nocommon
