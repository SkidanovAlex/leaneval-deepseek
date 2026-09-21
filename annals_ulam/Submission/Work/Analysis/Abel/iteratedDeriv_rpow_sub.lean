import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs

namespace Work.Analysis.Abel

open Filter
open scoped Topology

/-- **Derivative of one term of the falling-factorial expansion.**
For `u < σ`, the derivative in `u` of `u ↦ (-1)^j (p)_j (σ-u)^{p-j}` is the
next term `u ↦ (-1)^{j+1} (p)_{j+1} (σ-u)^{p-j-1}`. -/
lemma deriv_rff_rpow_sub {p σ u : ℝ} (hu : u < σ) (j : ℕ) :
    deriv (fun u : ℝ => (-1 : ℝ) ^ j * rff p j * (σ - u) ^ (p - j)) u
      = (-1 : ℝ) ^ (j + 1) * rff p (j + 1) * (σ - u) ^ (p - (j + 1)) := by
  have hne : σ - u ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  have hlin : HasDerivAt (fun t : ℝ => σ - t) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub σ
  have hpow : HasDerivAt (fun y : ℝ => y ^ (p - (j : ℝ)))
      ((p - (j : ℝ)) * (σ - u) ^ (p - (j : ℝ) - 1)) (σ - u) :=
    Real.hasDerivAt_rpow_const (Or.inl hne)
  have hcomp : HasDerivAt (fun t : ℝ => (σ - t) ^ (p - (j : ℝ)))
      ((p - (j : ℝ)) * (σ - u) ^ (p - (j : ℝ) - 1) * (-1)) u := hpow.comp u hlin
  have hmul := hcomp.const_mul ((-1 : ℝ) ^ j * rff p j)
  rw [hmul.deriv, rff_succ, pow_succ]
  rw [show p - ((j : ℝ) + 1) = p - (j : ℝ) - 1 by ring]
  ring

/-- **Iterated derivative of a translated fractional power.**
For `x < σ` and every `j : ℕ`, the `j`-th iterated derivative of `u ↦ (σ - u)^p` at `x` is
`(-1)^j (p)_j (σ - x)^{p-j}`, with `(p)_j = rff p j = p (p-1) ⋯ (p-j+1)` the falling factorial
(defined in `Submission.Work.Analysis.Abel.SweptKernelDefs`). -/
theorem iteratedDeriv_rpow_sub {p σ x : ℝ} (h : x < σ) (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => (σ - u) ^ p) x
      = (-1 : ℝ) ^ j * rff p j * (σ - x) ^ (p - j) := by
  have key : ∀ j : ℕ, iteratedDeriv j (fun u : ℝ => (σ - u) ^ p) =ᶠ[𝓝 x]
      (fun u : ℝ => (-1 : ℝ) ^ j * rff p j * (σ - u) ^ (p - j)) := by
    intro j
    induction j with
    | zero =>
      filter_upwards with u
      simp
    | succ j ih =>
      rw [iteratedDeriv_succ]
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      simp only [hcast]
      have h2 : deriv (fun u : ℝ => (-1 : ℝ) ^ j * rff p j * (σ - u) ^ (p - j)) =ᶠ[𝓝 x]
          (fun u : ℝ => (-1 : ℝ) ^ (j + 1) * rff p (j + 1) * (σ - u) ^ (p - ((j : ℝ) + 1))) := by
        filter_upwards [isOpen_Iio.mem_nhds h] with u hu
        exact deriv_rff_rpow_sub hu j
      exact ih.deriv.trans h2
  exact (key j).eq_of_nhds

end Work.Analysis.Abel
