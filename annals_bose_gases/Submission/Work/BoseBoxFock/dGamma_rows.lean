import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dGamma_rows` — the two `dGamma` rows of FS `lem:2ndQuand`

On the (coordinate-basis) mode Fock space `Work.BoseB4.RealFock m`, with
`dGamma T = ∑_{ij} (T e_j)_i · a_i† a_j` the second quantisation of a one-particle operator
`T : (Fin m → ℝ) →ₗ (Fin m → ℝ)`:

* `dGamma 1 = N = ∑_i a_i†a_i` — the total number operator (`Work.BoseB4.DGamma_one`);
* `dGamma (x ↦ x 0 • e₀) = a₀†a₀ = n₀` — the condensate number operator
  (`Work.BoseBoxFock.n0`),

the second being the collapse of the double sum to its single `(0,0)` matrix element: the
kernel `(T e_j)_i = δ_{j,0}·δ_{i,0}` vanishes off the diagonal entry `(0,0)`.

These are the two rows of FS `lem:2ndQuand` that identify the second-quantised kinetic /
condensate terms with the box-side operators used in `eq:HLambdaSecond`
(`Work.BoseBoxFock.H2ndF`).
-/

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **The condensate row.**  The second quantisation of the coordinate-`0` operator
`x ↦ x 0 • e₀` is `a₀†a₀`: its matrix `(T e_j)_i = δ_{j,0}δ_{i,0}` has a single nonzero
element, so the double sum `∑_{ij} (T e_j)_i a_i†a_j` collapses to the `(0,0)` term. -/
theorem dGamma_coord_zero {m : ℕ} [NeZero m]
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hT : ∀ x, T x = (x 0) • Work.BoseB4.evec m 0) :
    Work.BoseB4.dGamma m T = Work.BoseBoxFock.n0 (m := m) := by
  rw [Work.BoseB4.dGamma]
  -- The inner sum over `j` collapses to `j = 0`, because `(T e_j)_i ∝ δ_{j,0}`.
  have hinner : ∀ i : Fin m,
      (∑ j : Fin m, (T (Work.BoseB4.evec m j) i) •
          ((Work.BoseB4.cre m i).comp (Work.BoseB4.ann m j)))
        = (Work.BoseB4.evec m 0 i) • ((Work.BoseB4.cre m i).comp (Work.BoseB4.ann m 0)) := by
    intro i
    rw [Finset.sum_eq_single (0 : Fin m)]
    · -- the surviving term `j = 0`: `(T e₀) i = (e₀ i) · 1`
      rw [hT]
      congr 1
      simp [Work.BoseB4.evec, Pi.single_apply]
    · -- `j ≠ 0`: the coefficient `(T e_j) i = (e_j 0)·(e₀ i)` vanishes since `e_j 0 = 0`
      intro j _ hj
      rw [hT]
      have h0 : (Work.BoseB4.evec m j) 0 = 0 := by
        simp [Work.BoseB4.evec, hj]
      rw [h0]
      simp
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin m)) h0
  simp only [hinner]
  -- The outer sum over `i` collapses similarly to `i = 0`, because `e₀ i = δ_{i,0}`.
  rw [Finset.sum_eq_single (0 : Fin m)]
  · simp [Work.BoseB4.evec, Work.BoseBoxFock.n0]
  · intro i _ hi
    have h0 : Work.BoseB4.evec m 0 i = 0 := by
      simp [Work.BoseB4.evec, hi]
    rw [h0, zero_smul]
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin m)) h0

/-- **The two rows of FS `lem:2ndQuand`.**  The second quantisation of the identity one-particle
operator is the total number operator, and that of the coordinate-`0` operator `x ↦ x 0 • e₀`
is the condensate number operator `n₀`. -/
theorem dGamma_rows (m : ℕ) [NeZero m]
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hT : ∀ x, T x = (x 0) • Work.BoseB4.evec m 0) :
    Work.BoseB4.dGamma m LinearMap.id = Work.BoseB4.totNumOp m ∧
      Work.BoseB4.dGamma m T = Work.BoseBoxFock.n0 (m := m) :=
  -- `LinearMap.id` and `1` on `Fin m →ₗ[ℝ] Fin m` are the same operator.
  ⟨Work.BoseB4.DGamma_one m, dGamma_coord_zero T hT⟩

end Work.BoseBoxFock
