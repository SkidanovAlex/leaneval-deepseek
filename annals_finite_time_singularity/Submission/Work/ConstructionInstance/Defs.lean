/-
# `Work.ConstructionInstance` — the CONSTRUCTION INSTANTIATION

This is the final area of the `fts` (Elgindi, Annals **194** (2021)) formalisation: it
*instantiates* the input package `Work.SolutionDelivery.ConstructedSolution α` — the datum side of
the `theorem_1` assembly — from the delivered chapters

* `Submission/Work/Construction` (the reference triple `F = F_* + g` of §Modulation),
* `Submission/Work/Stability` (the `St0`–`St3` dynamic-modulation bootstrap),
* `Submission/Work/LWP` (the maximal-solution interface),
* `Submission/Work/Cyl` (the `(ρ,θ) ↔ ℝ³` dictionary),
* `Submission/Work/Spaces`, `Submission/Work/FM` (the profile data),

and, on top of them, closes the challenge statement through
`Work.SolutionDelivery.theorem_1_of_constructed`.

## What is *defined* here (not assumed)

The **self-similar vorticity in physical variables**.  The Construction area produces the profile
`F = F_* + g` of the self-similar variables `(z,θ)`, `F_*(z,θ) = p·(Γ(θ)/c)·2z/(1+z)²`,
`Γ(θ) = (sinθ cos²θ)^{p/3}`.  The physical self-similar vorticity of the paper
(§Setup, tex 222–310) is

  `ω^θ(r,x₃) = F_*(R,θ) + g(R,θ)`,   `R = ρ^p`,   `ρ² = r² + x₃²`,  `θ = arctan(x₃/r)`,

i.e. the `e_θ`-field `x ↦ F(ρ(x)^p, θ(x)) • e_θ(x)`.  This is `omegaS p g` below, defined from
the Construction area's `Work.Construction.Fstar` through the `Work.Cyl` dictionary.

**The two exponents.**  The paper's single symbol `α` plays two roles, and *they differ by a
factor `3`*: it is the exponent of the spatial rescaling `R = ρ^α` (the **profile exponent** `p`),
and it is (through `Γ = (sinθcos²θ)^{α/3}`) the exponent of the angular vanishing, hence of the
solution's Hölder regularity.  With the profile exponent `p`, the physical vorticity vanishes like
`θ^{p/3}` at the plane `x₃ = 0`, so its Hölder exponent is `p/3`.  We therefore take

* `p := 3 * α` for the profile exponent, where `α` is the **Hölder exponent** of the challenge,
  i.e. the parameter of `Work.SolutionDelivery.ConstructedSolution α`;

so that `Γ(θ) = (sinθcos²θ)^α` and the honest vorticity `omegaS (3α) g` is bounded and
`α`-Hölder.  Everything in this directory is stated for a general `p` and instantiated at
`p = 3α` (`profExp`).

## What is *assumed*

The residual list is kept as small as the delivered chapters allow and is spelled out field by
field in `ConstructionData` below.  `NOTES.md` of this directory records, field by field, which
chapter delivers it and, where a field turns out not to be derivable from the construction, the
exact obstruction (`Refute.lean` contains a formal *refutation* of one of the
`Work.SolutionDelivery.ConstructedSolution` fields).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.Cyl
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- `ℝ³` (definitionally `Work.Cyl.R3`, `Work.LWP.R3` and `Work.SolutionDelivery.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The two exponents -/

/-- The **profile exponent** attached to the interface's Hölder exponent `α`: `p = 3α`.

The construction is invoked with this exponent, so that the angular factor is
`Γ(θ) = (sinθcos²θ)^α` and the physical vorticity is `α`-Hölder (rather than `α/3`-Hölder, which
is what invoking the construction at `p = α` would give). -/
def profExp (α : NNReal) : ℝ := 3 * (α : ℝ)

theorem profExp_pos {α : NNReal} (hα : 0 < (α : ℝ)) : 0 < profExp α := by
  rw [profExp]; linarith

theorem profExp_div_three (α : NNReal) : profExp α / 3 = (α : ℝ) := by
  rw [profExp]; ring

theorem profExp_nonneg (α : NNReal) : 0 ≤ profExp α := by
  rw [profExp]; positivity

/-! ## The angular factor

`Γ(θ) = (sinθ·cos²θ)^β`.  For `β = α` this is the paper's `Γ` (with the interface's exponent);
it vanishes at both ends of the angular interval and is the source of the vorticity's vanishing
on the axis `r = 0` and on the plane `x₃ = 0`.  Note that `Γ` is only used on `θ ∈ [0,π/2]`,
where its base `sinθ·cos²θ` is in `[0,1]`; the definition is total (Lean's `Real.rpow`) and the
odd extension of the profile takes care of `θ < 0`. -/

/-- The angular factor `Γ(θ) = (sinθ·cos²θ)^β`. -/
def Gamma (β θ : ℝ) : ℝ := (Real.sin θ * Real.cos θ ^ 2) ^ β

/-- `Γ(p/3)` is `Work.Spaces.Gam p`, definitionally. -/
theorem Gamma_div_three (p θ : ℝ) : Gamma (p / 3) θ = Work.Spaces.Gam p θ := rfl

theorem Gamma_nonneg {β θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Gamma β θ :=
  Real.rpow_nonneg (by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity) _

theorem Gamma_le_one {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ∈ Work.Spaces.Iθ) : Gamma β θ ≤ 1 :=
  Real.rpow_le_one (by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity)
    (by
      have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have h2 : Real.cos θ ^ 2 ≤ 1 := by
        nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.cos θ)]
      nlinarith) hβ

/-- `F_*(z,0) = 0` (for `p ≠ 0`): `Γ(0) = 0`. -/
theorem Fstar_zero_theta {p : ℝ} (hp : p ≠ 0) (z : ℝ) : Work.Construction.Fstar p z 0 = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam, show Real.sin 0 * Real.cos 0 ^ 2 = 0 by simp,
    Real.zero_rpow (by positivity : p / 3 ≠ 0), zero_div]
  ring

/-- **The bound `|F_*(z,θ)| ≤ 20·p·Γ(θ)`** for `0 < p ≤ 1`, `z ≥ 0`, `θ ∈ [0,π/2]`, from
`c(p) ≥ 1/10` (`Work.Spaces.c_bounds`) and `2z/(1+z)² ≤ 1/2`. -/
theorem Fstar_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ| ≤ 20 * p * Gamma (p / 3) θ := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hGam0 : 0 ≤ Work.Spaces.Gam p θ := Gamma_nonneg hθ
  have hGam1 : Work.Spaces.Gam p θ ≤ 1 := by
    rw [← Gamma_div_three]; exact Gamma_le_one (by positivity) hθ
  have hF0 : 0 ≤ Work.FM.Fstar z := by rw [Work.FM.Fstar]; positivity
  have hF1 : Work.FM.Fstar z ≤ 1 / 2 := by
    rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
    nlinarith [sq_nonneg (1 - z)]
  have hpos : 0 ≤ Work.Construction.Fstar p z θ := by
    rw [Work.Construction.Fstar]
    exact mul_nonneg (mul_nonneg hp.le (div_nonneg hGam0 hcpos.le)) hF0
  rw [abs_of_nonneg hpos, Work.Construction.Fstar, ← Gamma_div_three]
  have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 * Gamma (p / 3) θ := by
    rw [Gamma_div_three, div_le_iff₀ hcpos]
    nlinarith [hc, hGam0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * Work.FM.Fstar z
      ≤ p * (10 * Gamma (p / 3) θ) * (1 / 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 hp.le
        · exact hF1
        · exact hF0
        · exact mul_nonneg hp.le (mul_nonneg (by norm_num) (Gamma_nonneg hθ))
    _ = 5 * p * Gamma (p / 3) θ := by ring
    _ ≤ 20 * p * Gamma (p / 3) θ := by
        have hG : 0 ≤ Gamma (p / 3) θ := Gamma_nonneg hθ
        nlinarith [hp.le, hG]

/-! ## The profile and the self-similar vorticity -/

/-- **The profile `F = F_* + g` extended oddly in `θ`.**

`Work.Construction.Fstar` is evaluated by Lean's total `Real.rpow`, whose values for `θ < 0` are
not the physically relevant ones; the odd extension is therefore written out explicitly.  The
physically relevant branch is `0 ≤ θ ≤ π/2`. -/
def profile (p : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  if 0 ≤ θ then Work.Construction.Fstar p z θ + g z θ
  else -(Work.Construction.Fstar p z (-θ) + g z (-θ))

theorem profile_of_nonneg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (h : 0 ≤ θ) :
    profile p g z θ = Work.Construction.Fstar p z θ + g z θ := ite_eq_left h

theorem profile_of_neg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (h : ¬ 0 ≤ θ) :
    profile p g z θ = -(Work.Construction.Fstar p z (-θ) + g z (-θ)) := ite_eq_right h

theorem profile_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg : ∀ z : ℝ, g z 0 = 0) (z : ℝ) :
    profile p g z 0 = 0 := by
  rw [profile_of_nonneg le_rfl, hg z, Fstar_zero_theta hp, add_zero]

/-- **The profile is odd in `θ`** whenever `g` vanishes on `θ = 0` (which is
`Work.Spaces.VanishTheta` for the modulation) and `p ≠ 0` (so that `F_*(z,0) = Γ(0)·… = 0`). -/
theorem profile_odd {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg : ∀ z : ℝ, g z 0 = 0)
    (z θ : ℝ) : profile p g z (-θ) = - profile p g z θ := by
  by_cases h : 0 ≤ θ
  · by_cases h' : 0 ≤ -θ
    · have hθ0 : θ = 0 := le_antisymm (by linarith) h
      rw [hθ0, neg_zero, profile_zero hp hg z, neg_zero]
    · rw [profile_of_neg h', profile_of_nonneg h]; simp
  · have hpos : 0 ≤ -θ := by linarith
    rw [profile_of_neg h, profile_of_nonneg hpos]; simp

/-- **The self-similar vorticity in physical variables** (the paper's `ω^θ` as an `e_θ`-field):

  `omegaS p g x = F(ρ(x)^p, θ(x)) • e_θ(x)`,  `ρ = ‖x‖`, `θ = arctan(x₃/r)`.

On the symmetry axis (`r = 0`) both `e_θ` and the `Γ`-factor of the profile vanish, so the field
is `0` there: the Lean-junk values of `Work.Cyl.theta` (`arctan(0) = 0`) and of
`Work.Cyl.eTheta` (the zero vector) are exactly the right ones. -/
def omegaS (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) : R3 :=
  profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x

/-- **The self-similar vorticity at a prescribed self-similar variable** `z`: the same field with
`F` evaluated at `z` instead of `ρ(x)^p`.  This is the form in which the *time-dependent* ansatz
of `St0`–`St3` reads, `ω(x,t) = λ̄(t)^{-1}·omegaSz p g (ρ(x)^p/λ̄(t)) x` (the rescaling of the
self-similar variable is what makes the vorticity blow up while the profile stays bounded); see
`Boxes.lean`. -/
def omegaSz (p : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) (x : R3) : R3 :=
  profile p g z (Work.Cyl.theta x) • Work.Cyl.eTheta x

theorem omegaS_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) :
    omegaS p g x = profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

theorem omegaS_apply' (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) :
    omegaS p g x
      = profile p g (Work.Cyl.rho x ^ p) (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

theorem omegaSz_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) (x : R3) :
    omegaSz p g z x = profile p g z (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

/-- `omegaS p g` is `omegaSz` at the self-similar variable `z = ρ(x)^p`. -/
theorem omegaS_eq_omegaSz (p : ℝ) (g : ℝ → ℝ → ℝ) (x : R3) :
    omegaS p g x = omegaSz p g (Work.Cyl.rho x ^ p) x := rfl

/-- **The model field** `x ↦ Γ(θ(x))·F_*(ρ(x)^{3β})·e_θ(x)` (`F_*` here the *radial* profile
`z ↦ 2z/(1+z)²` of the fundamental model, `Work.FM.Fstar`): the leading part of `omegaS (3β) g`,
with the angular factor `Γ = (sinθcos²θ)^β` and all constants dropped.  `Holder.lean` proves its
`β`-Hölder regularity, which is the analytic core of the corresponding statement for `omegaS`. -/
def omegaStar (β : ℝ) (x : R3) : R3 :=
  (Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β))) • Work.Cyl.eTheta x

theorem omegaStar_apply (β : ℝ) (x : R3) :
    omegaStar β x
      = (Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β)))
        • Work.Cyl.eTheta x := rfl

/-! ## The datum of the construction

`Work.SolutionDelivery.cutDatum L ω = χ(ρ/L) • ω` is the compactly supported `St1` cut-off; the
datum of the constructed solution is its Biot–Savart field. -/

/-- The cut-off datum vorticity of the construction: `χ(ρ/L) • omegaS p g`. -/
abbrev omega₀ (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) : R3 → R3 :=
  Work.SolutionDelivery.cutDatum L (omegaS p g)

theorem omega₀_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (x : R3) :
    omega₀ p g L x = Work.Stability.chi (Work.Cyl.rho x / L) • omegaS p g x := rfl

/-- The datum of the constructed solution: `u₀ = BS ω₀`. -/
abbrev datum (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) : R3 → R3 :=
  Work.LWP.biotSavart (omega₀ p g L)

/-- **The times before the maximal time `T`**, where the self-similar description of the solution
is meaningful: `preWindow T = Ioo (-2) T`.  It is the part of the extended window
`extWindow T = Ioo (-2) (T+2)` on which the modulation `λ̄` is positive — see
`not_lam_pos_extWindow` for why the remaining times `[T, T+2)` cannot support the fields below:
the combination `λ̄ > 0` at `T`, `λ̄` differentiable at `T` and `λ̄(t) ≤ 2(T-t)` for `t ∈ [0,T)`
is empty. -/
abbrev preWindow (T : ℝ) : Set ℝ := Set.Ioo (-2) T


end Work.ConstructionInstance
