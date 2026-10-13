/-
# `Work.FTS.StrongPersist.EnergyStep` — the recursion structure of the `ℋ⁶` energy identity

The energy identity of `H6EnergyDeriv` is the statement that

`τ ↦ IP (slice g τ) (slice g τ)` has the one-sided derivative `2 IP (ġ) (slice g τ)`,

where `IP` is the concrete `ℋ⁶`-pairing `IP6` and `ġ = dynLin + dynRHS` is the value of the
equation.  The point of this file is that the *recursion* part of that identity is pure algebra:

* `EnergyDeriv IP u udot τ` is the predicate "the `IP`-energy of the family `u` has derivative
  `2 IP udot (u τ)`";
* `energyDeriv_HkIPStep` transports it through one step of the paper's recursion
  `HkIPStep c₁ c₂` — the shifted slots `D_θu`, `D_zu` carry their own energy (their own
  `EnergyDeriv` facts) and the step is the linear combination
  `EnergyDeriv IP u + c₁ EnergyDeriv IP (D_θu) + c₂ EnergyDeriv IP (D_zu)`;
* `energyDeriv_H1IP` is the base case, from the four `wip`-level derivative facts of `H1IP`
  (two for the `η`-weight at `u` and `D_zu`, one for the `w`-weight at `u`, one for the
  `γ`-weight at `D_θu`).

Consequently the whole `H6EnergyDeriv` obligation reduces to instances of the *proved* product
rule `hasDerivAt_wip_family`
(`Submission/Work/FTS/StrongPersist/hasDerivAt_wip_family.lean`) for the slot families generated
by the recursion.  What is *not* in this file (and is the honest remaining content of the energy
identity) is the production of those `wip`-level facts from the solution's regularity: it needs,
slot by slot, the `τ`-differentiability of the slots of `u` (Clairaut with the equation) and the
a.e. domination of the derivative integrands — exactly the hypotheses of
`hasDerivAt_wip_family`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.Coercivity (HkIPStep H1IP wip LGammaT)
open Work.Spaces (Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The energy-derivative predicate -/

/-- **The energy derivative of a pairing along a family.**  `EnergyDeriv IP u udot τ` records that
`τ ↦ IP (u τ) (u τ)` has derivative `2 IP udot (u τ)` at `τ`.  This is the shape in which the
Grönwall argument of `Persist.lean` consumes the energy identity. -/
def EnergyDeriv (IP : Fn → Fn → ℝ) (u : ℝ → Fn) (udot : Fn) (τ : ℝ) : Prop :=
  HasDerivAt (fun s => IP (u s) (u s)) (2 * IP udot (u τ)) τ

/-- **The recursion step**: one `HkIPStep` of the paper's inner-product recursion transports the
energy derivative, the shifted slots `D_θu` and `D_zu` carrying their own energy derivatives. -/
theorem energyDeriv_HkIPStep {c₁ c₂ : ℝ} {IP : Fn → Fn → ℝ} {u : ℝ → Fn} {udot : Fn} {τ : ℝ}
    (h₁ : EnergyDeriv IP u udot τ)
    (h₂ : EnergyDeriv IP (fun s => Dth (u s)) (Dth udot) τ)
    (h₃ : EnergyDeriv IP (fun s => Dz (u s)) (Dz udot) τ) :
    EnergyDeriv (HkIPStep c₁ c₂ IP) u udot τ := by
  show HasDerivAt (fun s => HkIPStep c₁ c₂ IP (u s) (u s)) (2 * HkIPStep c₁ c₂ IP udot (u τ)) τ
  have hfun : (fun s => HkIPStep c₁ c₂ IP (u s) (u s))
      = fun s => IP (u s) (u s) + c₁ * IP (Dth (u s)) (Dth (u s))
          + c₂ * IP (Dz (u s)) (Dz (u s)) := by
    funext s
    rfl
  have h₂' : HasDerivAt (fun s => IP (Dth (u s)) (Dth (u s)))
      (2 * IP (Dth udot) (Dth (u τ))) τ := h₂
  have h₃' : HasDerivAt (fun s => IP (Dz (u s)) (Dz (u s)))
      (2 * IP (Dz udot) (Dz (u τ))) τ := h₃
  rw [hfun]
  have hmain : HasDerivAt
      (fun s => IP (u s) (u s) + c₁ * IP (Dth (u s)) (Dth (u s))
        + c₂ * IP (Dz (u s)) (Dz (u s)))
      (2 * IP udot (u τ) + c₁ * (2 * IP (Dth udot) (Dth (u τ)))
        + c₂ * (2 * IP (Dz udot) (Dz (u τ)))) τ :=
    ((h₁.add (h₂'.const_mul c₁)).add (h₃'.const_mul c₂))
  convert hmain using 1
  simp only [HkIPStep]
  ring

/-! ## The base case: the four `wip`-level facts of `H1IP` -/

/-- The `η`-weight `w² sin(2θ)^{-η}` of the paper. -/
def rhoEta : Fn := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The `w`-weight `w²`. -/
def rhoW : Fn := fun z _ => Work.Spaces.w z ^ 2

/-- The `γ`-weight `w² sin(2θ)^{-γ}` of the paper. -/
def rhoGam (α : ℝ) : Fn :=
  fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- `wip` is symmetric in its two function arguments. -/
theorem wip_symm (ρ f g : Fn) : wip ρ f g = wip ρ g f := by
  unfold Work.Coercivity.wip
  refine congrArg (fun F : ℝ → ℝ => ∫ z in Work.Spaces.Iz, F z) ?_
  funext z
  refine congrArg (fun G : ℝ → ℝ => ∫ θ in Work.Spaces.Iθ, G θ) ?_
  funext θ
  ring

/-- `H1IP` unfolded in terms of the four weighted pairings. -/
theorem H1IP_unfold (α : ℝ) (f g : Fn) :
    H1IP α f g
      = 10 * wip rhoEta (Dz f) (Dz g) + (10 : ℝ) ^ 10 * wip rhoEta f g
        + (10 : ℝ) ^ 17 * wip rhoW f g
        + (10 : ℝ) ^ 21 * wip (rhoGam α) (Dth f) (Dth g) := by
  unfold Work.Coercivity.H1IP rhoEta rhoW rhoGam
  ring

/-- **The base case of the energy identity.**  If the four weighted pairings of `H1IP` have the
derivative `2·(the corresponding pairing of `udot`)` along the family `u`, then the `H1IP`-energy
of `u` does. -/
theorem energyDeriv_H1IP (α : ℝ) {u : ℝ → Fn} {udot : Fn} {τ : ℝ}
    (h₁ : HasDerivAt (fun s => wip rhoEta (u s) (u s)) (2 * wip rhoEta udot (u τ)) τ)
    (h₂ : HasDerivAt (fun s => wip rhoEta (Dz (u s)) (Dz (u s)))
      (2 * wip rhoEta (Dz udot) (Dz (u τ))) τ)
    (h₃ : HasDerivAt (fun s => wip rhoW (u s) (u s)) (2 * wip rhoW udot (u τ)) τ)
    (h₄ : HasDerivAt (fun s => wip (rhoGam α) (Dth (u s)) (Dth (u s)))
      (2 * wip (rhoGam α) (Dth udot) (Dth (u τ))) τ) :
    EnergyDeriv (H1IP α) u udot τ := by
  show HasDerivAt (fun s => H1IP α (u s) (u s)) (2 * H1IP α udot (u τ)) τ
  have hfun : (fun s => H1IP α (u s) (u s))
      = fun s => 10 * wip rhoEta (Dz (u s)) (Dz (u s)) + (10 : ℝ) ^ 10 * wip rhoEta (u s) (u s)
          + (10 : ℝ) ^ 17 * wip rhoW (u s) (u s)
          + (10 : ℝ) ^ 21 * wip (rhoGam α) (Dth (u s)) (Dth (u s)) := by
    funext s
    exact H1IP_unfold α (u s) (u s)
  rw [hfun]
  have hval : 2 * H1IP α udot (u τ)
      = 10 * (2 * wip rhoEta (Dz udot) (Dz (u τ))) + (10 : ℝ) ^ 10 * (2 * wip rhoEta udot (u τ))
        + (10 : ℝ) ^ 17 * (2 * wip rhoW udot (u τ))
        + (10 : ℝ) ^ 21 * (2 * wip (rhoGam α) (Dth udot) (Dth (u τ))) := by
    rw [H1IP_unfold]
    ring
  rw [hval]
  exact (((h₂.const_mul (10 : ℝ)).add (h₁.const_mul ((10 : ℝ) ^ 10))).add
    (h₃.const_mul ((10 : ℝ) ^ 17))).add (h₄.const_mul ((10 : ℝ) ^ 21))

end Work.FTS.StrongPersist
