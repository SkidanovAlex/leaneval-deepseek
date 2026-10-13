/-
  Sharp — the mixed partial derivatives `Work.WilE9.glDeriv` commute.

  `Work.WilE9.glDeriv L f x` is the iterated directional derivative `∂_{i₁}⋯∂_{i_k} f` at `x`
  (head of the list = outermost derivative). For a function which is `C^∞` at `x` the value at
  `x` depends only on the *multiset* of directions, i.e. on the list up to permutation. This is
  the classical Clairaut/Schwarz theorem on the symmetry of higher partial derivatives, in the
  list-indexed form used by the WilE9 development.

  The argument has three ingredients:

  * `glDeriv_contDiffAt_top`: `glDeriv L f` is again `C^∞` at `x` when `f` is (induction on the
    list, one application of `ContDiffAt.fderiv_right` per list element);
  * `glDeriv_two_apply`: a mixed second derivative `∂_a ∂_b g` is the second `iteratedFDeriv` in
    the two directions, via `DifferentiableAt.iteratedFDeriv_succ_apply_left'`;
  * Mathlib's `ContDiffAt.iteratedFDeriv_comp_perm`: the iterated derivative of a `C^∞` function
    is symmetric, i.e. invariant under composition of the directions with a permutation of
    `Fin k`.

  Induction on the permutation relation `List.Perm` then gives the result: the `cons` case is
  functoriality of `fderiv` (`Filter.EventuallyEq.fderiv_eq`), the `swap` case is exactly
  `glDeriv_two_apply` combined with the symmetry of `iteratedFDeriv`, and `trans` is
  transitivity.
-/
import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Filter

namespace Work.Sharp

/-- The two directions of a mixed second derivative: `dirPair a b 0` is the *outer* direction
`a` and `dirPair a b 1` is the *inner* direction `b`, matching the convention of `glDeriv`
(the head of the list is the outermost derivative). -/
private def dirPair {n : ℕ} (a b : Fin n) : Fin 2 → (Fin n → ℝ) :=
  fun t => if t = 0 then Pi.single a 1 else Pi.single b 1

/-- Swapping the two directions of `dirPair` is composing with `Equiv.swap 0 1`. -/
private lemma dirPair_comp_swap {n : ℕ} (a b : Fin n) :
    dirPair a b ∘ ⇑(Equiv.swap 0 1) = dirPair b a := by
  funext t
  fin_cases t <;> simp [dirPair]

private lemma dirPair_zero {n : ℕ} (a b : Fin n) : dirPair a b 0 = Pi.single a 1 := by
  simp [dirPair]

private lemma dirPair_tail_zero {n : ℕ} (a b : Fin n) :
    (Fin.tail (dirPair a b)) 0 = Pi.single b 1 := by
  simp [dirPair, Fin.tail]

/-- The iterated directional derivatives `glDeriv L f` of a `C^∞` function are `C^∞` (compare
`Work.WilE9.Sharp.glDeriv_contDiffAt`, which does the bookkeeping of the orders `k - |L|`). -/
private theorem glDeriv_contDiffAt_top {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ ⊤ f x) (L : List (Fin n)) :
    ContDiffAt ℝ ⊤ (Work.WilE9.glDeriv L f) x := by
  induction L with
  | nil => exact hf
  | cons i L ih =>
    show ContDiffAt ℝ ⊤ (fun y => fderiv ℝ (Work.WilE9.glDeriv L f) y (Pi.single i 1)) x
    exact (ih.fderiv_right le_top).clm_apply contDiffAt_const

/-- A mixed second derivative of `C^∞` data is a second `iteratedFDeriv`: for `g` with
`iteratedFDeriv ℝ 1 g` differentiable at `y`, the derivative in the direction `b` (inner) of the
derivative in the direction `a` (outer) is `iteratedFDeriv ℝ 2 g y (dirPair a b)`. -/
private lemma glDeriv_two_apply {n : ℕ} (g : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (a b : Fin n)
    (hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 g) y) :
    fderiv ℝ (fun z => fderiv ℝ g z (Pi.single b 1)) y (Pi.single a 1)
      = iteratedFDeriv ℝ 2 g y (dirPair a b) := by
  have hfun : (fun z => fderiv ℝ g z (Pi.single b 1))
      = fun z => iteratedFDeriv ℝ 1 g z (Fin.tail (dirPair a b)) := by
    funext z
    rw [iteratedFDeriv_one_apply, dirPair_tail_zero]
  rw [hfun]
  exact (hdiff.iteratedFDeriv_succ_apply_left' (m := dirPair a b)).symm

/-- The main auxiliary statement: `glDeriv` is invariant under permutation of the list of
directions, at every point where `f` is `C^∞`. Proved by induction on the permutation. -/
private theorem glDeriv_perm_aux {n : ℕ} (L L' : List (Fin n)) (h : L.Perm L') :
    ∀ (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContDiffAt ℝ ⊤ f x →
      Work.WilE9.glDeriv L f x = Work.WilE9.glDeriv L' f x := by
  induction h with
  | nil => intro f x _; rfl
  | cons i h ih =>
    -- equality of the tails is only an eventual equality, but `fderiv` is a germ operation
    rename_i l₁ l₂
    intro f y hf
    have hev : Work.WilE9.glDeriv l₁ f =ᶠ[𝓝 y] Work.WilE9.glDeriv l₂ f := by
      filter_upwards [hf.eventually (by simp)] with z hz
      exact ih f z hz
    show fderiv ℝ (Work.WilE9.glDeriv l₁ f) y (Pi.single i 1)
        = fderiv ℝ (Work.WilE9.glDeriv l₂ f) y (Pi.single i 1)
    rw [hev.fderiv_eq]
  | swap a b l =>
    -- the only content: `∂_b ∂_a = ∂_a ∂_b` for `glDeriv l f`, by symmetry of `iteratedFDeriv`
    intro f y hf
    have hg : ContDiffAt ℝ ⊤ (Work.WilE9.glDeriv l f) y := glDeriv_contDiffAt_top hf l
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (Work.WilE9.glDeriv l f)) y :=
      hg.differentiableAt_iteratedFDeriv (m := 1) (by simp)
    have hR : fderiv ℝ (fun z => fderiv ℝ (Work.WilE9.glDeriv l f) z (Pi.single a 1)) y
          (Pi.single b 1)
        = iteratedFDeriv ℝ 2 (Work.WilE9.glDeriv l f) y (dirPair b a) :=
      glDeriv_two_apply (Work.WilE9.glDeriv l f) y b a hdiff
    have hL : fderiv ℝ (fun z => fderiv ℝ (Work.WilE9.glDeriv l f) z (Pi.single b 1)) y
          (Pi.single a 1)
        = iteratedFDeriv ℝ 2 (Work.WilE9.glDeriv l f) y (dirPair a b) :=
      glDeriv_two_apply (Work.WilE9.glDeriv l f) y a b hdiff
    have hsymm := hg.iteratedFDeriv_comp_perm (v := dirPair a b) (Equiv.swap 0 1)
    show fderiv ℝ (fun z => fderiv ℝ (Work.WilE9.glDeriv l f) z (Pi.single a 1)) y
          (Pi.single b 1)
        = fderiv ℝ (fun z => fderiv ℝ (Work.WilE9.glDeriv l f) z (Pi.single b 1)) y
            (Pi.single a 1)
    rw [hR, hL, ← dirPair_comp_swap a b]
    exact hsymm
  | trans h₁ h₂ ih₁ ih₂ =>
    intro f y hf
    rw [ih₁ f y hf, ih₂ f y hf]

theorem glDeriv_perm {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ ⊤ f x) {L L' : List (Fin n)} (h : L.Perm L') :
    Work.WilE9.glDeriv L f x = Work.WilE9.glDeriv L' f x :=
  glDeriv_perm_aux L L' h f x hf

end Work.Sharp
