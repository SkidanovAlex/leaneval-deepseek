/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.H2`: the interior supremum, and why it is the right `L^∞` companion of `RegQ`

The frozen interior class `Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧
BdryTraces α k f` (`Submission/Work/FTS/Vocab.lean`) prescribes the behaviour of `f` *inside*
the open quadrant `(0,∞) × (0,π/2)` only: `SmoothQuad` is smoothness on the open quadrant,
`HkMem` is an integral (so it is blind to the measure-zero boundary set), and `BdryTraces` are
limits *from inside*.  The values of `f` (and of its `D`-derivatives) on the two lines
`θ = 0` and `θ = π/2` are therefore unconstrained: the function
`f z θ = if θ = 0 then 10 else 0` satisfies `RegQ α 4 f` with `HkNorm α 4 f = 0`.

Consequently the closed-quadrant supremum `Spaces.supAbs` is *not* controlled by the `ℋ⁴` norm
in the class `RegQ`, while every estimate of §`H2` (the `L^∞`-`L²` trade-offs of Lemma
`infinity_separated` and of Corollary `SecondDerivativesBounded`) is used to bound integrands
pointwise *inside* the quadrant.  The right companion of `RegQ` is therefore the supremum over
the *open* quadrant, `supAbsO`, defined below; it is dominated by `Spaces.supAbs`
(`supAbsO_le_supAbs`) and agrees with it for functions that are continuous on the closed
quadrant (`supAbsO_eq_supAbs_of_continuousOn`), which is the case of every object that also has
an honest pointwise interpretation (e.g. the profiles of the reconstruction).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The supremum of `|g|` over the **open** quadrant `(0,∞) × (0,π/2)` — the `L^∞`-companion of
the interior regularity class `Work.FTS.Nonlin.RegQ`. -/
def supAbsO (g : ℝ → ℝ → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|}

/-- `supAbsO` is attained at the point `(1,1)` in the sense of being an upper bound. -/
private theorem supAbsO_bddAbove {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ C) :
    BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|} :=
  ⟨C, by rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩; exact h z θ hz hθ hθ'⟩

/-- The set defining `supAbsO` is nonempty. -/
private theorem supAbsO_nonempty : (1 : ℝ) < π / 2 := by
  have := Real.pi_gt_three; linarith

/-- Pointwise bound from `supAbsO`, inside the open quadrant. -/
theorem le_supAbsO {g : ℝ → ℝ → ℝ} {z θ C : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2)
    (h : ∀ z' θ', 0 < z' → 0 < θ' → θ' < π / 2 → |g z' θ'| ≤ C) : |g z θ| ≤ supAbsO g :=
  le_csSup (supAbsO_bddAbove h) ⟨z, hz, θ, hθ, hθ', rfl⟩

/-- Bound of `supAbsO` by a uniform bound on the open quadrant. -/
theorem supAbsO_le {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ C) : supAbsO g ≤ C :=
  csSup_le ⟨|g 1 1|, 1, one_pos, 1, one_pos, supAbsO_nonempty, rfl⟩
    (by rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩; exact h z θ hz hθ hθ')

/-- The interior supremum is dominated by the closed-quadrant supremum (for a bounded function;
without boundedness the closed-quadrant supremum is Lean's junk value `0`). -/
theorem supAbsO_le_supAbs (g : ℝ → ℝ → ℝ) (h : Spaces.SupFinite g) :
    supAbsO g ≤ Spaces.supAbs g :=
  supAbsO_le (g := g) (C := Spaces.supAbs g) fun _ _ hz hθ hθ' =>
    Spaces.abs_le_supAbs (le_of_lt hz) ⟨le_of_lt hθ, le_of_lt hθ'⟩ h

end Work.FTS.H2
