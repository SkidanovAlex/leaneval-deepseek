import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVec_contDiff_periodic`: iterated partial derivatives of a periodic `Cᵐ` function

The STE Fourier toolkit (design note `DESIGN.md`, Layer A) needs the elementary fact that the
`k`-fold iterated partial derivative `pdVec k l u = ∂_{l 0} ⋯ ∂_{l (k-1)} u` of a `Cᵐ`,
`1`-periodic function `u : (ι → ℝ) → ℂ` is `C^{m-k}` and still `1`-periodic (for `k ≤ m`).

Two ingredients, both already in `Submission/Work/Diff/STE/fourierCoeff_pdVec.lean`:

* `contDiff_pd_of_contDiff`: `pd j` lowers the class by one, `C^{N+1} → C^N`;
* `periodicIn_pd_of_differentiable`: `pd j` preserves `PeriodicIn i`.

The iteration is done on lists: `pdVec k l u = pdList (List.ofFn l) u` and `List.foldr` peels the
head, but `List.ofFn_succ'` shows that the *outermost* derivative is the last one, so the
induction peels `pd (l (Fin.last k))` **first** and applies the induction hypothesis to the
`C^{m-1}` function `pd (l (Fin.last k)) u` (this is what keeps the arithmetic honest: the
hypothesis of the auxiliary lemma is stated with `n + k` rather than a subtraction).
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coercion `↑ · : ℕ → WithTop ℕ∞` commutes with truncated subtraction.  This bridges the
form `↑m - ↑k` in which the subtraction of the goal statement elaborates (the expected type of
the `ContDiff` exponent is `WithTop ℕ∞`) with the ordinary subtraction on `ℕ`. -/
lemma withTop_natCast_sub (m k : ℕ) :
    ((m : WithTop ℕ∞) - (k : WithTop ℕ∞)) = ((m - k : ℕ) : WithTop ℕ∞) :=
  (WithTop.coe_sub (a := (m : ℕ∞)) (b := (k : ℕ∞))).symm

/-- **Iterated partial derivatives lower regularity and preserve periodicity.**  In the form
used for the induction: `k` derivatives of a `C^{n+k}` function are `Cⁿ` and again `1`-periodic. -/
lemma pdVec_contDiff_periodic_aux (k : ℕ) :
    ∀ (n : ℕ) (l : Fin k → ι) (u : (ι → ℝ) → ℂ),
      ContDiff ℝ ((n + k : ℕ) : WithTop ℕ∞) u → Periodic1 u →
      ContDiff ℝ (n : WithTop ℕ∞) (pdVec k l u) ∧ Periodic1 (pdVec k l u) := by
  induction k with
  | zero =>
      intro n l u hu hup
      rw [Nat.add_zero] at hu
      simpa only [pdVec, pdList, List.ofFn_zero, List.foldr_nil] using And.intro hu hup
  | succ k ih =>
      intro n l u hu hup
      -- the outermost derivative is the last one
      have hpd : pdVec (k + 1) l u
          = pdVec k (fun i : Fin k => l (Fin.castSucc i)) (pd (l (Fin.last k)) u) := by
        simp only [pdVec, pdList, List.ofFn_succ', List.concat_eq_append, List.foldr_append,
          List.foldr_cons, List.foldr_nil]
      -- the derivative of `u` is `C^{n+k}`
      have hw : ContDiff ℝ ((n + k : ℕ) : WithTop ℕ∞) (pd (l (Fin.last k)) u) :=
        contDiff_pd_of_contDiff (l (Fin.last k)) (m := n + k) (n := n + k + 1) hu (le_refl _)
      -- it is still periodic
      have hperw : Periodic1 (pd (l (Fin.last k)) u) := fun i =>
        periodicIn_pd_of_differentiable i (l (Fin.last k)) (hu.differentiable (by simp)) (hup i)
      rw [hpd]
      exact ih n (fun i : Fin k => l (Fin.castSucc i)) (pd (l (Fin.last k)) u) hw hperw

/-- **Main lemma.**  The `k`-fold iterated partial derivative `pdVec k l u` of a `Cᵐ`,
`1`-periodic function is `C^{m - k}` and `1`-periodic, for `k ≤ m`. -/
theorem pdVec_contDiff_periodic {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ℕ) (hm : k ≤ m)
    (l : Fin k → ι) (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ m u) (hup : Work.Diff.STE.Periodic1 u) :
    ContDiff ℝ (m - k) (Work.Diff.STE.pdVec k l u) ∧ Work.Diff.STE.Periodic1 (Work.Diff.STE.pdVec k l u) := by
  rw [withTop_natCast_sub m k]
  have hu' : ContDiff ℝ (((m - k) + k : ℕ) : WithTop ℕ∞) u := by
    rw [Nat.sub_add_cancel hm]
    exact hu
  exact pdVec_contDiff_periodic_aux k (m - k) l u hu' hup

end Work.Diff.STE
