import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_z^j` preserves smoothness (finite order, global)

`D_z = z ∂_z` is a first-order differential operator with `C^∞` coefficients, hence it lowers
the differentiability order by exactly one: if `G` is `C^{n+1}` on all of `ℝ²`, then
`D_z G` is `C^n`.  Iterating, `D_z^j G` is `C^{n-j}` — and in particular, if `G` is `C^n` for
every `n`, so is `D_z^j G` for every `j`.  That is the statement proved here.

The single-order step is the standard `fderiv` argument: on `ℝ²` the partial derivative
`∂_z` is the Fréchet derivative in the direction `(1,0)` (`Work.Spaces.pz_eq_fderiv`), the
Fréchet derivative of a `C^{n+1}` map is `C^n` (`ContDiff.fderiv_right`), and multiplication
by the `C^∞` coefficient `z` preserves the order.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.DzIterCpt

/-- `∂_z` lowers the differentiability order by one (global version). -/
private theorem contDiff_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) := by
  have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) := by
    have hh := h.fderiv_right (m := (n : WithTop ℕ∞)) (by simp)
    simpa using hh
  have hcomp : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) :=
    hfd.clm_apply contDiff_const
  have hfun : Function.uncurry (Work.Spaces.pz G)
      = fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    funext p
    obtain ⟨z, θ⟩ := p
    exact Work.Spaces.pz_eq_fderiv ((h.differentiable (by norm_num)).differentiableAt)
  rw [hfun]
  exact hcomp

/-- `D_z = z ∂_z` lowers the differentiability order by one (global version). -/
private theorem contDiff_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz G)) := by
  have hpz := contDiff_uncurry_pz_fin h
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact contDiff_fst.mul hpz

/-- `D_z^j` lowers the differentiability order by `j` (global version). -/
private theorem contDiff_uncurry_DzIter_shift {G : ℝ → ℝ → ℝ} :
    ∀ (j n : ℕ), ContDiff ℝ ((n + j : ℕ) : WithTop ℕ∞) (Function.uncurry G) →
      ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter j G)) := by
  intro j
  induction j with
  | zero => intro n h; simpa using h
  | succ j ih =>
      intro n h
      have h' : ContDiff ℝ ((n + 1 + j : ℕ) : WithTop ℕ∞) (Function.uncurry G) := by
        rw [show n + 1 + j = n + (j + 1) from by omega]; exact h
      exact contDiff_uncurry_Dz_fin (ih (n + 1) h')

/-- **`D_z^j` preserves `C^n`-for-all-`n`.**  If `G` is of class `C^n` on `ℝ²` for every `n`,
then so is `D_z^j G`. -/
theorem DzIter_contDiff_of_forall {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (j : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.DzIter j G)) := by
  intro n
  exact contDiff_uncurry_DzIter_shift j n (hG (n + j))

end Work.FTS.PhiStar.Honesty.DzIterCpt
