/-
# Shared definitions for the `L₁₂` zero-mode identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`

This file collects the *hypotheses* of the zero-mode identity (as a structure, so that the
auxiliary lemmas proved for it have short statements) and the four functions the argument is
phrased in terms of:

* `uOf f r = L₁₂dens f r = ∫_{Iθ} K(θ) f(r,θ)/r dθ` — the density of `L₁₂(f)`;
* `GOf α f r = L₁₂dens (𝓛_Γ f) r` — the density of `L₁₂(𝓛_Γ f)`;
* `ROf f r = L₁₂f f r = ∫_r^∞ uOf f s ds` — the tail integral;
* `NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ) dz dθ` — the *joint* (hence honest, non-junk) form
  of the angular integral `-∫_{Iθ} K(θ) f(r,θ) dθ`;
* `mdOf f r = ∫_{Iθ} K(θ) ∂_z f(r,θ) dθ` — the angular integral of `∂_z f`.

The point of `NOf` is that, unlike `mdOf`, it is a genuine integral of a (jointly) integrable
function for every `r`, so it is continuous and has clean limits, while `mdOf` is only honest
for a.e. `r`.  The identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)` is then proved by integrating the a.e.
identity `GOf α f r - uOf f r = mdOf f r - 2 uOf f r/(1+r) - 2 ROf f r/(1+r)²` over `(ε,ρ)` and
letting `ε → 0⁺`, `ρ → ∞`, where the boundary terms are `NOf f 0 = 0` and
`ROf f 0 = ∫_0^∞ uOf f`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

set_option autoImplicit false

/-- The hypotheses of the `L₁₂` zero-mode identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`, packaged. -/
structure L12Hyp (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  hα : 0 < α
  hα1 : α ≤ 1
  hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
    HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => Work.Spaces.pz f s θ) (Set.Ici 0)
  hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0)
  hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0
  hint : MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
    (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
  hintL : MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
      * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
  hintL2 : MeasureTheory.IntegrableOn (fun z => Work.Construction.L12dens f z) (Set.Ioi 0)
  hint3 : MeasureTheory.IntegrableOn
    (fun z => Work.Construction.L12dens (Work.Coercivity.LGamma α f) z) (Set.Ioi 0)

/-- `uOf f r = L₁₂dens f r`, the density of `L₁₂(f)`. -/
def uOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ := Work.Construction.L12dens f

/-- `GOf α f r = L₁₂dens(𝓛_Γ f) r`, the density of `L₁₂(𝓛_Γ f)`. -/
def GOf (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  Work.Construction.L12dens (Work.Coercivity.LGamma α f)

/-- `ROf f r = L₁₂f f r = ∫_r^∞ uOf f`, the tail integral of the density of `L₁₂(f)`. -/
def ROf (f : ℝ → ℝ → ℝ) : ℝ → ℝ := Work.Coercivity.L12f f

/-- `NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)`, the `z`-integral form of `-∫_{Iθ} K(θ) f(r,θ)`. -/
def NOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ, Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2

/-- `mdOf f r = ∫_{Iθ} K(θ) ∂_z f(r,θ) dθ`, the angular integral of `∂_z f`. -/
def mdOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ

@[simp] theorem uOf_eq (f : ℝ → ℝ → ℝ) : uOf f = Work.Construction.L12dens f := rfl
@[simp] theorem GOf_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    GOf α f = Work.Construction.L12dens (Work.Coercivity.LGamma α f) := rfl
@[simp] theorem ROf_eq (f : ℝ → ℝ → ℝ) : ROf f = Work.Coercivity.L12f f := rfl
@[simp] theorem NOf_eq (f : ℝ → ℝ → ℝ) : NOf f
    = fun r => ∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ,
        Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 := rfl
@[simp] theorem mdOf_eq (f : ℝ → ℝ → ℝ) : mdOf f
    = fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ := rfl

end Work.FTS.Apriori.ZeroMode
