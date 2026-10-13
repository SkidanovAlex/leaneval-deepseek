/-
# Row 11 of the N4 table: the vocabulary of the proof

The piece of row 11 is `N₁^{**} = 2 ℛ(Φ̃_*) F_*` (`Work.FTS.Nonlin.N1ss`), and the design's
route (`FTS/N45_DESIGN_LEAD.md` §3.4, row 11) is

  `WtoH` (`|f|_{ℋ⁴} ≤ C·|((z+1)³/z²) f|_{𝒲^{4,∞}}`), applied to `f = N₁^{**}`,
  + a product rule in the `𝒲^{4,∞}`-norm: `((z+1)³/z²)·N₁^{**} = 2·ℛ̃(Φ̃_*)·Bv`,
  where

* `ℛ̃(Φ̃_*) = ((z+1)/z)·ℛ(Φ̃_*)` — the *weighted* coefficient of the star package
  (`StarPkg.R` bounds it in `𝒲^{4,∞}` by `Cs·α`); it is the only factor we know about
  through the interface, and it is *not* `SmoothQuad` (it may be discontinuous at `z = 0`),
  so the product rule used below must not require full `SmoothQuad` of both factors;
* `Bv(θ) = 2α·Γ(θ)/c(α)` — an *angular* function, `C^∞` on `(0,π/2)`, which is exactly
  the factor `((z+1)²/z)·F_*` away from `z = 0` (see the identity proved in `row11.lean`).

The product of an angular function and of a `𝒲^{4,∞}` function is again in `𝒲^{4,∞}` (the
`z`-derivatives do not interact at all, and the `θ`-derivatives satisfy Leibniz) — this is the
statement `angMulWlInf` of the sibling file.  This module only carries the *definitions*, so
that the delegated lemmas can be stated in the same vocabulary.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **`C^∞` on the strict open quadrant** `z > 0`, `0 < θ < π/2`.  This is the class in which
the weighted coefficient `ℛ̃(Φ̃_*) = ((z+1)/z)·ℛ(Φ̃_*)` is smooth — it is *not* `SmoothQuad`
(which also requires smoothness at `z = 0`), because of the factor `1/z`. -/
def SmoothPos (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))

/-- The angular factor `Bv(θ) = 2α·Γ(θ)/c(α)` of row 11: away from `z = 0` it is exactly
`((z+1)²/z)·F_*(z,θ)`. -/
def Bv (α : ℝ) : ℝ → ℝ := fun θ => 2 * α * (Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- The weighted coefficient `ℛ̃(Φ̃_*) = ((z+1)/z)·ℛ(Φ̃_*)` of the star package. -/
def Rv (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z + 1) / z * Work.Construction.Rop α
    (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ

/-- The weighted piece of row 11: `G = ((z+1)³/z²)·N₁^{**}` — the function whose
`𝒲^{4,∞}`-norm controls `|N₁^{**}|_{ℋ⁴}` through `WtoH`. -/
def Gv (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlin.N1ss α Φs z θ



/-! ## Two elementary facts about iterated `z`-derivatives and constants

`deriv_const_mul_loc` is the unconditional product rule for a constant (Lean's `deriv` is `0`
at a non-differentiable point, and `c•f` is differentiable at `z` iff `f` is, for `c ≠ 0`, so
the two junk values agree); `pzIter_const_mul` is its iterate.  (The sibling
`RowsN0Aux.deriv_const_mul'` of `Pieces/Basic.lean` is the same statement; it is reproved here
so that this module depends only on `Nonlinear/Defs`.  The neighbouring `DthIter_const_mul` is
taken from `Pieces/Basic.lean` by the consumers.) -/

theorem deriv_const_mul_loc (c : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    deriv (fun z' => c * g z') z = c * deriv g z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp
  · by_cases hg : DifferentiableAt ℝ g z
    · exact deriv_const_mul c hg
    · have hnon : ¬ DifferentiableAt ℝ (fun z' => c * g z') z := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z' => c⁻¹ * (c * g z')) z := h.const_mul c⁻¹
        have heq : (fun z' => c⁻¹ * (c * g z')) = g := by
          funext z'; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rw [heq] at h2
        exact hg h2
      rw [deriv_zero_of_not_differentiableAt hnon,
        deriv_zero_of_not_differentiableAt hg, mul_zero]

theorem pzIter_const_mul (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
    funext z θ
    show deriv (fun z' => c * Work.Spaces.pzIter k f z' θ) z
      = c * deriv (fun z' => Work.Spaces.pzIter k f z' θ) z
    exact deriv_const_mul_loc c (fun z' => Work.Spaces.pzIter k f z' θ) z

end Work.FTS.Nonlinear.Pieces.RNP
