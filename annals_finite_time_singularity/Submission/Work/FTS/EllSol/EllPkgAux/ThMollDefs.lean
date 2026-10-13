/-
# `Work.FTS.EllSol.EllPkgAux.ThMollDefs` — the vocabulary of the `θ`-mollification transfer

The angular mollification of `Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs`,

  `thMoll u ε z θ = ∫_ℝ sKer ε (θ - s) * Qext u z s ds`

where `Qext u z` is the doubly odd extension of the angular slice, is a convolution of the
slice with the bump `sKer ε`.  Because the bump has support in `(-ε, ε)` and `ε ≤ 1/2`, the
whole-line integral only sees the values of the slice inside the (reflected) angle interval
`Iθ = [0, π/2]`.  The two objects that make this precise are

* `Qcut g = 1_{Iθ} · g`, the slice killed outside `Iθ`.  Its relevance is that the doubly odd
  extension agrees, on the window `(-π/2, π)` met by the mollification, with
  `Qcut g s - Qcut g (-s) - Qcut g (π - s)` (this is the identity `Qext_eq_Qcut_combination`
  of `ThMollExt`), so the fold of the kernel carries the signs `- -` on the reflected pieces;
* `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`, the resulting three-image kernel.

Nothing here is a statement of the target; the analytic content lives in `ThMollExt`
(the extension identity) and in `thMollTransfer2` (the folding and derivative identities).
-/
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- The angular slice killed outside the closed angle interval `Iθ = [0, π/2]`. -/
def Qcut (g : ℝ → ℝ) : ℝ → ℝ := Set.indicator (Set.Icc 0 (Real.pi / 2)) g

/-- The three-image kernel combination of a kernel `ρ`: the fold of the doubly odd extension
of a slice carries the signs `+ - -`. -/
def Kern (ρ : ℝ → ℝ) (θ s : ℝ) : ℝ := ρ (θ - s) - ρ (θ + s) - ρ (θ + s - Real.pi)

theorem Qcut_of_mem {g : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Qcut g s = g s :=
  Set.indicator_of_mem hs g

theorem Qcut_of_lt_zero {g : ℝ → ℝ} {s : ℝ} (hs : s < 0) : Qcut g s = 0 := by
  refine Set.indicator_of_notMem ?_ g
  intro h
  exact absurd (Set.mem_Icc.mp h).1 (not_le.mpr hs)

theorem Qcut_of_pihalf_lt {g : ℝ → ℝ} {s : ℝ} (hs : Real.pi / 2 < s) : Qcut g s = 0 := by
  refine Set.indicator_of_notMem ?_ g
  intro h
  exact absurd (Set.mem_Icc.mp h).2 (not_le.mpr hs)

theorem Qcut_apply (g : ℝ → ℝ) (s : ℝ) :
    Qcut g s = if s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) then g s else 0 := by
  rw [Qcut, Set.indicator_apply]

theorem Kern_apply (ρ : ℝ → ℝ) (θ s : ℝ) :
    Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - Real.pi) := rfl

/-- The three-image kernel is differentiable in its first variable, with derivative the
three-image kernel of the derivative. -/
theorem Kern_hasDerivAt {ρ ρ' : ℝ → ℝ} (h : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => Kern ρ θ' s) (Kern ρ' θ s) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => ρ (θ' - s)) (ρ' (θ - s)) θ :=
    HasDerivAt.comp_sub_const θ s (h (θ - s))
  have h2 : HasDerivAt (fun θ' : ℝ => ρ (θ' + s)) (ρ' (θ + s)) θ :=
    HasDerivAt.comp_add_const θ s (h (θ + s))
  have h3 : HasDerivAt (fun θ' : ℝ => ρ (θ' + s - Real.pi)) (ρ' (θ + s - Real.pi)) θ := by
    have := HasDerivAt.comp_add_const θ (s - Real.pi) (h (θ + (s - Real.pi)))
    simpa only [add_sub_assoc] using this
  show HasDerivAt (fun θ' : ℝ => ρ (θ' - s) - ρ (θ' + s) - ρ (θ' + s - Real.pi))
    (ρ' (θ - s) - ρ' (θ + s) - ρ' (θ + s - Real.pi)) θ
  exact (h1.sub h2).sub h3

end Work.FTS.EllSol.EllPkgAux
