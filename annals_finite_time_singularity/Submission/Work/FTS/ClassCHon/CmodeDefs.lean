/-
# `FTS/ClassCHon/CmodeDefs` — the iterated angular operator of the rapid mode decay

The angular operator of the elliptic section is
`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` (`Work.FTS.EllipticEst.Lzero1`).  It is
*self-adjoint* for the weight `cos θ dθ` on `[0, π/2]` (this is
`Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam`), and its Dirichlet eigenfunctions are the
Gegenbauer modes `eFam m` with eigenvalues `lam m = 2m(2m+5)`.

Consequently, for a source `g` which is `C^∞` and supported in a closed interval
`[a,b] ⊂ (0, π/2)` — so that all of its `Lzero1`-iterates are again supported in `[a,b]` and
the boundary terms of the integration by parts vanish — the mode coefficient

  `∫_{0}^{π/2} g θ · eFam m θ · cos θ dθ`

can be pushed onto the `k`-th iterate of `g` at the cost of a factor `(lam m)^{-k}`, and the
remaining integral is bounded by `O(m)`.  That gives decay `m^{-2k+O(1)}` for every `k`, i.e.
rapid decay of all the cosine-mode coefficients.

This module fixes the vocabulary: the iterate `Lop g k` of the operator, and the standing
hypothesis `Good a b g` ("`C^∞` and supported in `[a,b]`").

**Beware of the order convention.**  `Good` uses `Work.Stability.smoothOrder = ∞`, the genuine
`C^∞` order; the order `⊤` of the `ContDiff` notation is the *analytic* order `ω` in this
Mathlib (see `Submission/Work/Stability/Cutoff.lean`).  Applying `Lzero1` to an *analytic* `u`
supported in `[a,b] ⊂ (0,π/2)` is still smooth (indeed analytic) but this is not what we need:
our target hypothesis `ContDiff ℝ ⊤ g` is the analytic order, which is *stronger* than `∞`, and
the target therefore follows from the `∞`-version by `ContDiff.of_le le_top`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.ClassCHon

/-- `Lop g k` is the `k`-fold iterate of the angular operator `Lzero1` applied to `g`
(`Lop g 0 = g`, `Lop g (k+1) = Lzero1 (Lop g k)`). -/
noncomputable def Lop (g : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun k => Nat.rec g (fun _ acc => Work.FTS.EllipticEst.Lzero1 acc) k

@[simp] theorem Lop_zero (g : ℝ → ℝ) : Lop g 0 = g := rfl

@[simp] theorem Lop_succ (g : ℝ → ℝ) (k : ℕ) :
    Lop g (k + 1) = Work.FTS.EllipticEst.Lzero1 (Lop g k) := rfl

/-- A function `g` which is `C^∞` (`∞ = Work.Stability.smoothOrder`, *not* the analytic order
`⊤ = ω`) and vanishes outside the interval `[a,b]`. -/
def Good (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ Work.Stability.smoothOrder g ∧ ∀ θ : ℝ, θ ∉ Set.Icc a b → g θ = 0

theorem Good.contDiff {a b : ℝ} {g : ℝ → ℝ} (h : Good a b g) :
    ContDiff ℝ Work.Stability.smoothOrder g := h.1

theorem Good.eq_zero {a b : ℝ} {g : ℝ → ℝ} (h : Good a b g) :
    ∀ θ : ℝ, θ ∉ Set.Icc a b → g θ = 0 := h.2

end Work.FTS.ClassCHon
