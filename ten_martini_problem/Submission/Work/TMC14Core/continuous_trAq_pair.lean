import Mathlib
import Submission.Work.TMC14Core.Rat

/-!
# TMC14Core: continuity of `trAq` in the pair `(z, θ)`

`trAq p q lam z θ` is the trace of the `q`-step transfer matrix
`iterC ((p:ℝ)/(q:ℝ)) lam z q θ`, a finite product of the elementary matrices
`tmC lam z y = !![z - 2λ cos 2πy, -1; 1, 0]`.  Each entry of `tmC lam z y` is a
continuous function of `(z, y)`, so the `q`-fold product — and hence its trace —
is continuous in `(z, θ)`, in particular along the embedding `ℝ × ℝ → ℂ × ℝ`,
`(x, θ) ↦ ((x : ℂ), θ)`.

The proof is a plain induction on the number of steps: continuity of a product of
`2 × 2` matrices is `Continuous.matrix_mul`, and the base case `iterC _ _ _ 0 _ = 1`
is a constant.
-/

noncomputable section

namespace Work.TMC14Core

/-- The elementary transfer matrix `tmC lam z y` is continuous in the pair
`(z, y)` — stated for an arbitrary topological parameter space `X` and arbitrary
continuous `g : X → ℂ`, `h : X → ℝ`. -/
theorem continuous_tmC {X : Type*} [TopologicalSpace X] (lam : ℝ) (g : X → ℂ) (h : X → ℝ)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun x => tmC lam (g x) (h x) := by
  unfold tmC
  fun_prop

/-- Continuity of the `n`-step transfer matrix `iterC α lam z n θ` in `(z, θ)`,
specialised to the embedding `ℝ × ℝ → ℂ × ℝ`, `(x, θ) ↦ ((x : ℂ), θ)`. -/
theorem continuous_iterC (α lam : ℝ) (n : ℕ) :
    Continuous fun u : ℝ × ℝ => iterC α lam (u.1 : ℂ) n u.2 := by
  induction n with
  | zero => simp only [iterC_zero]; exact continuous_const
  | succ n ih =>
      simp only [iterC_succ]
      exact Continuous.matrix_mul (by unfold tmC; fun_prop) ih

/-- `trAq p q lam z θ` is continuous as a function of `(z, θ) = ((x : ℂ), θ)`. -/
theorem continuous_trAq_pair (p : ℤ) (q : ℕ) (lam : ℝ) :
    Continuous fun u : ℝ × ℝ => trAq p q lam (u.1 : ℂ) u.2 := by
  have h := continuous_iterC ((p : ℝ) / (q : ℝ)) lam q
  simp only [trAq]
  exact (h.matrix_elem 0 0).add (h.matrix_elem 1 1)

end Work.TMC14Core
