/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/EnergyIP4.lean` — the level-four energy identity from the
slot-level facts

`StrongPersist.EnergyIter.energyDeriv_IPiter` (proved) transports the energy derivative of a
pairing up the paper's recursion: if the `H1IP`-energy of *every* slot word `X` in `D_z`, `D_θ`
along the family `τ ↦ X (u τ)` has derivative `2 H1IP (X u̇) (X (u τ))`, then so does the `n`-fold
iterate.  `EnergyIter.IPiter_coefs6` records the instance `n = 5`, i.e. `IP6`.

This module records the instance the **level-four** half of `AprioriP` consumes, `n = 3`:
`IPiter α (coefs6 …) 3 = CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''`, hence

  `energyDeriv_IP4 : (∀ X, IsWord X → EnergyDeriv (H1IP α) (fun s => X (u s)) (X u̇) τ)
      → EnergyDeriv (IP4 c₁ … c₂'' α) u u̇ τ`,

and its immediate corollary for the **projected mollified** family
`x(τ) = slice (JfamP ρ ε g) τ`, whose `u̇` is the *honest* derivative `Pz (J_ε (epsRHSP τ))`
(see `EpsE4Thr/NOTES_EpsE4Thr_session3.md` §1).

Everything here is `sorry`-free.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Eq
import Submission.Work.FTS.StrongPersist.EnergyIter
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongEps.PZeroScheme

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The three times iterated recursion with the coefficient tuple of `coefs6` is the concrete
`ℋ⁴` inner product `IP4`. -/
theorem IPiter_coefs4 (α : ℝ) (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    Work.FTS.StrongPersist.IPiter α
        (Work.FTS.StrongPersist.coefs6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'') 3
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α := by
  simp only [Work.FTS.StrongPersist.IPiter, Work.FTS.StrongPersist.coefs6,
    Work.FTS.CoercivityFix.Assembly.IP4, Work.FTS.CoercivityFix.Assembly.IP3,
    Work.FTS.CoercivityFix.Assembly.IP2]
  norm_num

/-- **The level-four energy identity from the slot-level facts**: the `IP4`-energy of a family has
derivative `2 IP4 u̇ (u τ)` as soon as every slot word of length `≤ 5` carries the corresponding
`H1IP`-energy derivative. -/
theorem energyDeriv_IP4 (α : ℝ) (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) {u : ℝ → Fn} {udot : Fn} {τ : ℝ}
    (h : ∀ X : Fn → Fn, Work.FTS.StrongPersist.IsWord X →
      Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α) (fun s => X (u s))
        (X udot) τ) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) u udot τ := by
  have hmain := Work.FTS.StrongPersist.energyDeriv_IPiter α
    (Work.FTS.StrongPersist.coefs6 0 0 0 0 c₁ c₂ c₁' c₂' c₁'' c₂'') 3 h
  rwa [IPiter_coefs4] at hmain

/-- **The level-four energy identity along the projected mollified family.**  With the slot-level
facts for the projected family `x(τ) = slice (JfamP ρ ε g) τ` and the *honest* derivative
`Pz (J_ε (epsRHSP τ))`, the `IP4`-energy of `x` has that derivative.  This is the `hderiv` input of
`EpsE4Thr.apriori_fourth_of_barrier`. -/
theorem energyDeriv_IP4_JfamP {α : ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) {ρ : ℝ × ℝ → ℝ} {ε T : ℝ}
    {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ}
    (h : ∀ X : Fn → Fn, Work.FTS.StrongPersist.IsWord X →
      Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α)
        (fun s => X (slice (JfamP ρ ε g) s))
        (X (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ)))) τ) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α)
      (fun s => slice (JfamP ρ ε g) s) (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ))) τ :=
  energyDeriv_IP4 α c₁ c₂ c₁' c₂' c₁'' c₂'' h

end Work.FTS.StrongEps.EpsE4Thr
