/-
  WilG4c — the vocabulary of the "repeated `hbdd`" lemma `Work.WilG4c.hbdd_sup_finite`
  (BNZ §5.4, "repeatedly applying Lemma 5.6").

  The lemma is proved by induction on the number `k` of `x`-directions of the multiindex `L`.
  For `k = 0` the fibre bound comes from the `y`-jet hypothesis `hY`.  For the step, one applies
  `hbdd` (BNZ Lemma 5.6) to the function

      `f := ψ ∘ (extension of ∂^{L'}g by 0 off the C^{|L|}-locus of g)`,

  where `ψ(u) = 1/2 + u/(2√(1+u²))` is a semialgebraic diffeomorphism `ℝ → (0,1)` with
  `0 < ψ' ≤ 1/2`.  Its `x`-derivative is `ψ'(∂^{L'}g)·∂^{L}g` wherever the junk function agrees
  with `∂^{L'}g`, so `hbdd`'s conclusion bounds `∂^{L}g` up to the positive factor `ψ'`; and
  `hbdd`'s *hypothesis* (the `y`-partials of `f` bounded off a finite set of `x`) is supplied by
  the induction hypothesis because the junk equals `∂^{L'}g` on the `C^{|L|}`-locus.

  This file fixes the two objects (`psi`, `chi`) so that the delegated lemmas about them, and the
  main proof, agree on the notation.
-/
import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `ψ(u) = 1/2 + u/(2√(1+u²))`: a semialgebraic diffeomorphism `ℝ → (0,1)` with
`0 < ψ' ≤ 1/2` (BNZ §5.4).  It is the "rescaler" that turns a definable function with values in
`ℝ` into one with values in `(0,1)` while keeping a strictly positive derivative, so that
`hbdd` (which needs values in `(0,1)`) becomes applicable to `∂^{L'}g` without losing `∂^{L}g`. -/
def psi (u : ℝ) : ℝ := 1 / 2 + u / (2 * Real.sqrt (1 + u ^ 2))

/-- The value of `psi'` at `u`, in closed form. -/
def dpsi (u : ℝ) : ℝ := 1 / (2 * (1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

/-- The junk extension of the `L'`-th directional derivative of `g` over the `C^m`-locus of
`g`: it equals `iterDir L' g v` at the points `v` where `g` is `C^m`, and `0` elsewhere.

Its graph is an `Ω`-set (this uses `S.SharpDeriv`: the graph of the `L'`-th directional
derivative over the `C^{|L'|}`-locus is `Ω`-definable, and the `C^m`-locus is the projection of
the `m`-th one).  On the `C^m`-locus (which is contained in the `C^{|L'|}`-locus when
`|L'| ≤ m`) it agrees with the true derivative `iterDir L' g`. -/
def chi {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (L' : List (Fin (n + 1))) (m : ℕ) :
    (Fin (n + 1) → ℝ) → ℝ :=
  fun v => if ContDiffAt ℝ m g v then Work.WilkG4c.iterDir L' g v else 0

@[simp] theorem chi_of_contDiffAt {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (L' : List (Fin (n + 1))) (m : ℕ) {v : Fin (n + 1) → ℝ} (h : ContDiffAt ℝ m g v) :
    Work.WilkG4c.chi g L' m v = Work.WilkG4c.iterDir L' g v := by
  simp [chi, h]

@[simp] theorem chi_of_not_contDiffAt {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (L' : List (Fin (n + 1))) (m : ℕ) {v : Fin (n + 1) → ℝ} (h : ¬ ContDiffAt ℝ m g v) :
    Work.WilkG4c.chi g L' m v = 0 := by
  simp [chi, h]

end Work.WilkG4c
