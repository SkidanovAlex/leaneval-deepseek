/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Gdot.lean` — the right-hand side of the `ε`-scheme

`IsEpsSol` (`Submission/Work/FTS/StrongEps/Basic.lean`) is stated *pointwise*: for every point
`(z,θ)` of the open quadrant and every `τ ∈ [0,T]` the fake-time slice `s ↦ g z θ s` has
derivative

  `J_ε[ 𝓛(J_ε g) + 𝓡(Ψ(J_ε g), J_ε g) ](z,θ)`.

This module packages that value as a single function `epsRHS` and draws the consequences that
every later item of the scheme (E3's energy identity, E5's Cauchy/limit step) uses:

* **`IsEpsSol.gdot_eq`** — for `τ` in the *interior* of `[0,T]` the fake-time derivative
  `gdot g τ` of the family coincides with `epsRHS` on the open quadrant (this is what turns the
  pointwise scheme into an identity for `gdot`);
* **`IsEpsSol.mono`** — an `ε`-solution on `[0,T']` restricts to `[0,T]` for `T ≤ T'` (used to
  place all the members of the extracted sequence on a common interval).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false

/-- **The right-hand side of the `ε`-scheme** at the fake time `τ`, as a function of the family:
the `z θ`-profile

  `J_ε[ 𝓛_Γ^T(J_ε g) + 𝓡(Ψ(J_ε g), J_ε g) ]`,

i.e. the value that `IsEpsSol` prescribes for the fake-time derivative of `g`.  With this name the
scheme reads `gdot g τ = epsRHS α ρ ε Φs E g τ` on the open quadrant and the interior of `[0,T]`
(`IsEpsSol.gdot_eq`), and E3's energy identity is
`(d/dτ) ⟨h, h⟩ = 2 ⟨epsRHS α ρ ε Φs E g τ, h⟩` for `h = slice (Jfam ρ ε g) τ`. -/
def epsRHS (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => Jeps ρ ε (fun z' θ' => dynLin α (Jfam ρ ε g) τ z' θ'
      + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ z' θ') z θ

/-- `epsRHS` is by construction the value appearing in the scheme. -/
theorem epsRHS_eq (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : epsRHS α ρ ε Φs E g τ
      = fun z θ => Jeps ρ ε (fun z' θ' => dynLin α (Jfam ρ ε g) τ z' θ'
          + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ z' θ') z θ :=
  rfl

/-- **The profile that `epsRHS` mollifies**: the scheme's right-hand side *before* the outer
`J_ε`, i.e. `𝓛_Γ^T(J_ε g) + 𝓡(Ψ(J_ε g), J_ε g)` at the fake time `τ`.  With this name the scheme
reads

  `epsRHS α ρ ε Φs E g τ = J_ε (epsWU α ρ ε Φs E g τ)`

**by `rfl`** (`epsRHS_eq_Jeps_epsWU`), which is the form in which every estimate about `epsRHS`
is done: the frozen level-six clauses (`H6Lin`, `H6Pair`) are stated for exactly the two summands
of `epsW`, and the only correction is the one-argument `ε`-commutator
`IP6_Jeps_diff_le`. -/
def epsWU (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => dynLin α (Jfam ρ ε g) τ z θ
    + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ z θ

/-- `epsRHS` is the mollification of `epsW`, by `rfl`. -/
theorem epsRHS_eq_Jeps_epsWU (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) : epsRHS α ρ ε Φs E g τ = Jeps ρ ε (epsWU α ρ ε Φs E g τ) := rfl


/-- **The scheme as an identity for `gdot`.**  At every point of the open quadrant and every
`τ ∈ (0,T)` the fake-time derivative of the family is the value `epsRHS` prescribed by the scheme.

The point is that `IsEpsSol` takes its derivative *within* `[0,T]`, so at an interior point of
`[0,T]` this is an honest two-sided derivative, and `deriv` sees it. -/
theorem IsEpsSol.gdot_eq {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (hsol : IsEpsSol α ρ ε T Φs E g₀ g) {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Ioo 0 T) :
    gdot g τ z θ = epsRHS α ρ ε Φs E g τ z θ := by
  rw [gdot, epsRHS]
  exact (hsol.2 z θ τ hz hθ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2) |>.deriv

/-- **The one-sided form at `τ = 0`**: the scheme at the initial time, as a `HasDerivWithinAt`
statement. -/
theorem IsEpsSol.hasDerivWithinAt_zero {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {g : Fam} (hsol : IsEpsSol α ρ ε T Φs E g₀ g) (hT : 0 ≤ T) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivWithinAt (fun s => g z θ s) (epsRHS α ρ ε Φs E g 0 z θ) (Set.Icc 0 T) 0 :=
  hsol.2 z θ 0 hz hθ ⟨le_rfl, hT⟩

/-- **Restriction in time**: an `ε`-solution on `[0,T']` is an `ε`-solution on every shorter
interval `[0,T]` (the derivative is taken within the smaller set). -/
theorem IsEpsSol.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSol α ρ ε T' Φs E g₀ g) (hT : T ≤ T') :
    IsEpsSol α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, le_trans hτ.2 hT⟩).mono (Set.Icc_subset_Icc le_rfl hT)⟩

end Work.FTS.StrongEps
