import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- Route: induction on `k`, with the function-level identity
`(fun x => pdVec k l f x) = fun x => iteratedFDeriv ℝ k f x (fun j => Pi.single (l j) 1)`.
Base case: `List.ofFn` of `Fin 0 → ι` is empty, so `pdVec 0 l f = f`, and
`iteratedFDeriv_zero_apply` gives `iteratedFDeriv ℝ 0 f x m = f x`.
Step: `pdVec (k+1) l f = pd (l 0) (pdVec k (Fin.tail l) f)` (`List.ofFn_cons`, `List.foldr_cons`),
while `iteratedFDeriv ℝ (k+1) f x = (fderiv ℝ (iteratedFDeriv ℝ k f) x).uncurryLeft` (definitional),
so evaluating at `fun j => Pi.single (l j) 1` and using `uncurryLeft_apply` with
`Fin.cons (l 0) (Fin.tail l) = l` (`Fin.cons_self_tail`) leaves the identity
`fderiv ℝ (fun y => iteratedFDeriv ℝ k f y u) x v = (fderiv ℝ (iteratedFDeriv ℝ k f) x v) u`,
which is `fderiv_continuousMultilinear_apply_const` (needs `DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x`,
supplied by `ContDiff.iteratedFDeriv_right` from `hf`). -/
theorem pdVec_eq_iteratedFDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ι → ℝ) (l : Fin k → ι) :
    Work.Diff.STE.pdVec k l f x = iteratedFDeriv ℝ k f x (fun j => Pi.single (l j) 1) := by
  -- `pdVec` one step: peel the *first* index (`l 0`), leaving `Fin.tail l` for the IH.
  have hpd : ∀ (k : ℕ) (l : Fin (k + 1) → ι),
      pdVec (k + 1) l f = pd (l 0) (pdVec k (Fin.tail l) f) := by
    intro k l
    have h : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
      conv_lhs => rw [← Fin.cons_self_tail l]
      rw [List.ofFn_cons]
    simp only [pdVec, pdList]
    rw [h, List.foldr_cons]
  -- smoothness of the `k`-th iterated derivative, needed for `fderiv_continuousMultilinear_apply_const`.
  have hdiff : ∀ (y : ι → ℝ) (k : ℕ), DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y := by
    intro y k
    exact ((hf.contDiffAt.iteratedFDeriv_right (m := 1) (i := k) (by simp)).differentiableAt
      (by norm_num))
  suffices h : ∀ (k : ℕ) (l : Fin k → ι),
      pdVec k l f = fun y => iteratedFDeriv ℝ k f y (fun j => Pi.single (l j) 1) from
    congr_fun (h k l) x
  intro k
  induction k with
  | zero =>
    intro l
    funext y
    rw [pdVec, pdList, List.ofFn_zero, List.foldr_nil]
    exact (iteratedFDeriv_zero_apply (fun j => Pi.single (l j) 1)).symm
  | succ k ih =>
    intro l
    rw [hpd k l, ih (Fin.tail l)]
    funext y
    simp only [pd]
    rw [iteratedFDeriv_succ_apply_left]
    rw [fderiv_continuousMultilinear_apply_const (c := iteratedFDeriv ℝ k f) (x := y) (hdiff y k)]
    rfl

end Work.Diff.STE.Comp
