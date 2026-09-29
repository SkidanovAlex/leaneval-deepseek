import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.EllDerivDefs

/-!
# `RedC8/EllLyapDefs` — the solution sequence behind `ℓ ≤ L`

The inequality `ℓ(E) ≤ L(E)` for `E ∈ ℍ` is proved by exhibiting, for each phase `x`,
a bi-infinite solution `(u_k)` of the transfer recurrence whose ratios of consecutive terms
are the values `m(E, x + kα)` of the `m`-function.  Concretely

* `uSol α lam E k x = ∏_{j=1}^{k} mfun α lam E (x + jα)` (`k ≥ 0`), the `k`-th term of the
  solution with `u_0 = 1`;
* `wv α lam E x = 1 / mfun α lam E x`, the value `u_{-1}` forced by the recurrence,
  so that `(u_0, u_{-1}) = (1, wv)` is an eigenvector of the transfer matrix product in the
  sense `iterC α lam E n x *ᵥ (1, wv) = (u_n, u_{n-1})`.

Everything here is elementary bookkeeping about `mfun`; the mathematics is the covariance
relation `mfun(x+α) = E - pot x - 1/mfun x`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.RedC8

open Work.TMComp.Kotani

/-- `uSol α lam E k x = ∏_{j=1}^{k} mfun α lam E (x + jα)`, the `k`-th term of the solution
of the transfer recurrence with `u_0 = 1`. -/
def uSol (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ∏ j ∈ Finset.range k, mfun α lam E (x + ((j + 1 : ℕ) : ℝ) * α)

/-- `u_{-1} = 1/mfun α lam E x`, the second coordinate of the initial vector. -/
def wv (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ := (mfun α lam E x)⁻¹

theorem mfun_ne_zero (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    mfun α lam E x ≠ 0 := fun h => by
  have := MfunProbs.mfun_im_pos α lam hE x
  rw [h] at this; simp at this

@[simp] theorem uSol_zero (α lam : ℝ) (E : ℂ) (x : ℝ) : uSol α lam E 0 x = 1 := by
  simp [uSol]

theorem uSol_succ (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    uSol α lam E (k + 1) x
      = uSol α lam E k x * mfun α lam E (x + ((k + 1 : ℕ) : ℝ) * α) := by
  simp only [uSol, Finset.prod_range_succ]

theorem uSol_ne_zero (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (k : ℕ) (x : ℝ) :
    uSol α lam E k x ≠ 0 := by
  simp only [uSol]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => mfun_ne_zero α lam E hE _)

theorem norm_uSol (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    ‖uSol α lam E k x‖
      = ∏ j ∈ Finset.range k, ‖mfun α lam E (x + ((j + 1 : ℕ) : ℝ) * α)‖ := by
  simp only [uSol, norm_prod]

theorem log_norm_uSol (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (k : ℕ) (x : ℝ) :
    Real.log ‖uSol α lam E k x‖
      = ∑ j ∈ Finset.range k, Real.log ‖mfun α lam E (x + ((j + 1 : ℕ) : ℝ) * α)‖ := by
  rw [norm_uSol, Real.log_prod]
  intro j _
  exact norm_ne_zero_iff.mpr (mfun_ne_zero α lam E hE _)

theorem continuous_uSol (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (k : ℕ) :
    Continuous (fun x : ℝ => uSol α lam E k x) := by
  simp only [uSol]
  refine continuous_finsetProd _ (fun j _ => ?_)
  exact (continuous_mfun_phase α lam hE).comp (continuous_id.add continuous_const)

end Work.TMComp.RedC8
