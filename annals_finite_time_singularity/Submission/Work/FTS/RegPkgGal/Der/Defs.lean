/-
# `Work.FTS.RegPkgGal.Der.Defs` — the second-order `z`-class data at the origin

This file adds **one** class condition to the `St1`-class data of `RVocab.StData`, the one that is
needed to turn the `ℋ⁴` `L^∞`-bounds into a *modulus* of `∂_zg̃` in `z` (item R3 of the design,
`FTS_PHYS_BRIDGE.md` §4):

  `StData2 α S g` — `∃ Q₂, |∂_z²g(z,θ,τ)| ≤ Q₂` for `0 < z ≤ 2` (uniform in `(θ,τ)` in `Iθ × [0,S]`).

**Why it is class data and not derivable.**  `StData.quad` already bounds `|g| ≤ Kz²` and
`|∂_zg| ≤ Qz` near `z = 0`, which is exactly the statement that the Taylor coefficient of `z²` is a
*bounded* function of `(θ,τ)`: `g = z²·h(z,θ,τ)` with `h` bounded and `|∂_zh| ≤ K + Q`.  The
modulus of `∂_zg̃` in `z` is the modulus of `h` up to the factor `z²`, so it needs the *first*
derivative of `h`, i.e. the second `z`-derivative of `g`, to be bounded near `z = 0` — this is
`StData2`.  It is not a consequence of `ℋ⁴`-membership: the weight `w² ~ z^{-4}` of the radial
`ℋ⁴`-slots only forces `∫ (∂_z²g)²/z⁴ < ∞`, hence (by Cauchy–Schwarz) `|∂_z²g| = o(z^{3/2})`,
which is satisfied by `∂_z²g ≈ z^{-1/2}`, unbounded.  It *is* satisfied by the profile of the
construction, where `g = c(τ)z²Γ(θ)·(1 + O(z))`, so that `∂_z²g → 2c(τ)Γ(θ)` as `z → 0⁺`, bounded
by `2·sup|c|` on `Iθ × [0,S]`.

The companion clause used for the *fake-time* derivative of `∂_zg̃` (`∂_z∂_τg̃`) is **not** assumed
here: that regularity is delivered by the right-hand side's `z`-derivative, a field of the R5 slot.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE SECOND-ORDER `z`-CLASS DATA AT THE ORIGIN.**  The boundedness of the second `z`-derivative
of `g` on `(0,2] × Iθ × [0,S]` — the Taylor class condition `g = c(τ)z²Γ(θ)(1 + O(z))` of the
construction, in the form in which the `z`-modulus of `∂_zg̃` consumes it.  See the module
docstring for why it is *not* a consequence of `ℋ⁴`-membership. -/
structure StData2 (α S : ℝ) (g : Fam) : Prop where
  /-- `|∂_z²g| ≤ Q₂` for `0 < z ≤ 2`, uniformly in `(θ,τ) ∈ Iθ × [0,S]` -/
  quad2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
    |Work.Spaces.pz (Work.Spaces.pz (gSlice g τ)) z θ| ≤ Q₂

theorem StData2.quad2' {α S : ℝ} {g : Fam} (h : StData2 α S g) :
    ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz (gSlice g τ)) z θ| ≤ Q₂ := h.quad2

/-! ## The joint regularity class used by the R5 constituents

The R5 constituents (`𝓛_Γ^T(g)(τ)`, `N₀`, `N`, `N_*`) need, for their `z`-differentiability, both the
*joint* regularity (the `Jet` of `FTS.Regularity`: a uniform bound **and** an α-Hölder modulus) and
the `z`-differentiability with a uniform bound — the value bounds are *not* implied by
differentiability alone (the review of `Der.zderiv_LGammaT` produced the witness
`g z θ τ = φ(τ)u(θ)` with `φ` unbounded).  `C1Jet` bundles exactly those two things. -/
def C1Jet (α S N : ℝ) (h : Fam) : Prop :=
  Jet α S N h ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => h z' θ τ) d z ∧ |d| ≤ N

theorem C1Jet.jet {α S N : ℝ} {h : Fam} (H : C1Jet α S N h) : Jet α S N h := H.1

theorem C1Jet.zderiv {α S N : ℝ} {h : Fam} (H : C1Jet α S N h) :
    ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => h z' θ τ) d z ∧ |d| ≤ N := H.2

end Work.FTS.RegPkgGal
