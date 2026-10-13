import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped ContDiff Topology

namespace Work.WilE9.Deriv

/-- Unfolding lemma for `glDeriv` on a cons: the head of the list is the *outermost* derivative. -/
theorem glDeriv_cons_apply {n : ℕ} (i : Fin n) (L : List (Fin n)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    Work.WilE9.glDeriv (i :: L) f x = fderiv ℝ (Work.WilE9.glDeriv L f) x (Pi.single i 1) := rfl

/-- The list-indexed iterated derivative agrees with `iteratedFDeriv` on the list of
directions read off a function `Fin k → Fin n`. -/
theorem glDeriv_ofFn {n k : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (v : Fin k → Fin n)
    (hf : ContDiffAt ℝ k f x) :
    Work.WilE9.glDeriv (List.ofFn v) f x = iteratedFDeriv ℝ k f x (fun j => Pi.single (v j) 1) := by
  induction k generalizing f x with
  | zero =>
    rw [List.ofFn_zero]
    rfl
  | succ k ih =>
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      hf.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast Nat.lt_succ_self k)
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ k f y :=
      (hf.eventually (by simp)).mono (fun y hy => hy.of_le (by exact_mod_cast Nat.le_succ k))
    have hge : Work.WilE9.glDeriv (List.ofFn (fun i : Fin k => v i.succ)) f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ k f y (fun i : Fin k => Pi.single (v i.succ) 1)) := by
      filter_upwards [hev] with y hy
      exact ih f y (fun i : Fin k => v i.succ) hy
    rw [List.ofFn_succ]
    rw [glDeriv_cons_apply]
    rw [Filter.EventuallyEq.fderiv_eq hge]
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left'
      (m := fun j : Fin (k + 1) => Pi.single (v j) 1) hdiff]
    rfl

end Work.WilE9.Deriv
