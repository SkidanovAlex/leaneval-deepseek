import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Sharp

open scoped ContDiff

/-- Unfolding of `glDeriv` on a cons at the level of *functions*: the head of the list is the
outermost derivative. -/
theorem glDeriv_cons_fun {n : ℕ} (i : Fin n) (L : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.WilE9.glDeriv (i :: L) f
      = fun x => fderiv ℝ (Work.WilE9.glDeriv L f) x (Pi.single i 1) := rfl

/-- `glDeriv` of the empty list is the function itself. -/
theorem glDeriv_nil_fun {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Work.WilE9.glDeriv ([] : List (Fin n)) f = f := rfl

/-- One step of the regularity bookkeeping for `glDeriv`: if `g` is `C^{m+1}` at `x` then the
directional derivative of `g` in the (constant) direction `v` is `C^m` at `x`. -/
theorem contDiffAt_fderiv_apply_succ {n m : ℕ} {g : (Fin n → ℝ) → ℝ} {x v : Fin n → ℝ}
    (hg : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g x) :
    ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ g y v) x := by
  have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fderiv ℝ g) x := hg.fderiv_right_succ
  have h2 : ContDiffAt ℝ (m : WithTop ℕ∞)
      ((fun (φ : (Fin n → ℝ) →L[ℝ] ℝ) => φ v) ∘ fderiv ℝ g) x :=
    h1.continuousLinearMap_comp ((ContinuousLinearMap.apply ℝ ℝ) v)
  simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using h2

/-- The iterated directional derivatives `glDeriv L` of a `C^k` function are `C^{k-|L|}`,
for every list `L` of directions of length at most `k`. The exponent is kept as an explicit
coercion of a natural number so that the arithmetic stays in `ℕ`. -/
theorem glDeriv_contDiffAt_aux {n : ℕ} (L : List (Fin n)) (k : ℕ) (g : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (hL : L.length ≤ k) (hg : ContDiffAt ℝ k g x) :
    ContDiffAt ℝ ((k - L.length : ℕ) : WithTop ℕ∞) (Work.WilE9.glDeriv L g) x := by
  induction L generalizing k with
  | nil =>
    rw [glDeriv_nil_fun]
    simpa using hg
  | cons i L ih =>
    have hLcons : L.length + 1 ≤ k := by simpa [List.length_cons] using hL
    have hL' : L.length ≤ k := by omega
    have hpos : 1 ≤ k - L.length := by omega
    have hg' : ContDiffAt ℝ (((k - L.length : ℕ)) : WithTop ℕ∞)
        (Work.WilE9.glDeriv L g) x := ih k hL' hg
    have hstep : ContDiffAt ℝ (((k - L.length - 1 : ℕ)) : WithTop ℕ∞)
        (fun y => fderiv ℝ (Work.WilE9.glDeriv L g) y (Pi.single i 1)) x := by
      have hsub : (k - L.length - 1) + 1 = k - L.length := Nat.sub_add_cancel hpos
      have hg'' : ContDiffAt ℝ (((k - L.length - 1) + 1 : ℕ) : WithTop ℕ∞)
          (Work.WilE9.glDeriv L g) x := by
        rw [hsub]
        exact hg'
      exact contDiffAt_fderiv_apply_succ hg''
    rw [glDeriv_cons_fun]
    have he : (k - (i :: L).length : ℕ) = k - L.length - 1 := by
      rw [List.length_cons, ← Nat.sub_sub]
    rw [he]
    exact hstep

theorem GlDerivContDiffAt2 {n k : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {L : List (Fin n)}
    (hf : ContDiffAt ℝ k f x) (hL : L.length ≤ k) :
    ContDiffAt ℝ (k - L.length) (Work.WilE9.glDeriv L f) x :=
  glDeriv_contDiffAt_aux L k f x hL hf

/-- Companion form: the iterated derivatives of `f` of order `≤ k` are continuous at `x`. -/
theorem glDeriv_continuousAt {n k : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {L : List (Fin n)}
    (hf : ContDiffAt ℝ k f x) (hL : L.length ≤ k) :
    ContinuousAt (Work.WilE9.glDeriv L f) x :=
  (GlDerivContDiffAt2 hf hL).continuousAt

end Work.WilE9.Sharp
