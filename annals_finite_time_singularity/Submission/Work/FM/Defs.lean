/-
# The Fundamental Model of the 3D Euler self-similar blow-up

This directory (`Submission/Work/FM/`) formalizes the *fundamental model* of

  T. M. Elgindi, *Finite-time singularity formation for C^{1,α} solutions to the
  incompressible Euler equations on ℝ³*, Annals of Math. **194** (2021), 1--70,

i.e. Section "Three Examples" / Section "The Fundamental Model"
(`Papers/elgindi/Classical_Euler_arXiv_2.tex`, lines 311--475), restricted to the
angular domain `[0, π/2]` of the axi-symmetric no-swirl setting.

The model is

  ∂_t f(ρ,θ,t) = f(ρ,θ,t) · L₁₂^K(f)(ρ,t),
  L₁₂^K(f)(ρ,t) = ∫_ρ^∞ ∫_0^{π/2} K(θ') f(s,θ',t)/s dθ' ds,

with `K(θ) = 3 sin θ cos²θ` and `Γ(θ) = (sin θ cos²θ)^{α/3}` in the applications.

## Conventions fixed here (downstream areas depend on these)

* `L12 K f ρ` is the *iterated Lebesgue integral* over `Ioi ρ` of the density
  `L12dens K f s = ∫ θ in Icc 0 (π/2), K θ * f s θ / s`; the angular integration
  is over the *set* `Icc 0 (π/2)` (measure `dθ`, no `sin θ` factor), matching the
  paper's Warning in §Notation: the measure is `dρ dθ`, not `ρ dρ dθ`.
* Hypotheses of the abstract lemmas are always phrased in terms of
  `IntegrableOn` on `Set.Ioi ρ` / `Set.Icc 0 (π/2)`, so that every statement is
  meaningful without any implicit regularity assumption on `K` or `f`.
* `selfSim K Γ α ρ θ t` is the paper's self-similar family of Lemma
  `FMSelfSimilar` in the exact normalization of the paper:
  `2α (Γ(θ)/c) (1-t)⁻¹ F_{*,rad}(ρ^α/(1-t))` with `c = cK K Γ` and
  `F_{*,rad} = Fstarp`.  Its equally useful equivalent form is
  `α (Γ(θ)/c) (1-t)⁻¹ Fstar(ρ^α/(1-t))`, see `selfSim_eq`.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ### The angular data -/

/-- The angular weight of the fundamental model: `K(θ) = 3 sin θ cos²θ`.

On the whole line `K` is not `2π`-periodic; periodicity is irrelevant on the
angular domain `[0,π/2]` of the paper's setting. -/
def Kpaper (θ : ℝ) : ℝ := 3 * Real.sin θ * Real.cos θ ^ 2

/-- `Γ(θ) = (sin θ cos²θ)^{α/3}`. -/
def Gamma (α θ : ℝ) : ℝ := (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)

/-! ### The self-similar profile -/

/-- The profile `F_*(z) = 2z/(1+z)²` which satisfies the identity
`F_* + z∂_z F_* = F_* ∫_z^∞ F_*(s)/s ds` of the paper (line 467). -/
def Fstar (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The normalization `F_{*,rad}(z) = z/(1+z)²` used in Lemma `FMSelfSimilar`.
Note `Fstar = 2 * Fstarp`, which is why the paper's prefactor `2α` in the lemma
matches the prefactor `α` of the identity `F_* + z∂_z F_* = F_* ∫ F_*/s`. -/
def Fstarp (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-! ### The operator `L₁₂^K` -/

/-- The normalization constant `c = ∫_0^{π/2} K(θ)Γ(θ) dθ` of the paper. -/
def cK (K Γ : ℝ → ℝ) : ℝ := ∫ θ in Icc 0 (Real.pi / 2), K θ * Γ θ

/-- The angular density of `L₁₂^K`, as a function of the radial variable:
`L12dens K f s = ∫_0^{π/2} K(θ) f(s,θ)/s dθ`.  It satisfies
`∂_ρ L₁₂^K(f)(ρ) = - L12dens K f ρ` (see `hasDerivAt_L12`), and it is the
quantity multiplied by `K(θ)/s` and integrated to produce the model's Riccati
equation. -/
def L12dens (K : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ θ in Icc 0 (Real.pi / 2), K θ * f s θ / s

/-- The integral operator of the fundamental model (paper line 211/453):
`L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`.

It is a function of `ρ` alone: `L₁₂^K(f)` is *radial*, which is what reduces the
model to a one-parameter family of ODEs in `t`. -/
def L12 (K : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ s in Ioi ρ, L12dens K f s

/-! ### The model and its self-similar family -/

/-- The self-similar family of Lemma `FMSelfSimilar`: for `c = ∫KΓ ≠ 0` and
`α > 0`,
`f(ρ,θ,t) = 2α (Γ(θ)/c) (1-t)⁻¹ F_{*,rad}(ρ^α/(1-t))`,
with `F_{*,rad} = Fstarp`. -/
def selfSim (K Γ : ℝ → ℝ) (α : ℝ) (ρ θ t : ℝ) : ℝ :=
  2 * α * (Γ θ / cK K Γ) * (1 - t)⁻¹ * Fstarp (ρ ^ α / (1 - t))

/-- `f` solves the fundamental model on the physical range `ρ ≥ 0`, `t < 1`:
`∂_t f(ρ,θ,t) = f(ρ,θ,t) L₁₂^K(f(·,·,t))(ρ)`. -/
def IsModelSolution (K : ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ ρ θ t, 0 ≤ ρ → t < 1 →
    HasDerivAt (fun t => f ρ θ t) (f ρ θ t * L12 K (fun s θ => f s θ t) ρ) t

/-! ### Elementary restatements -/

theorem Fstar_eq (z : ℝ) : Fstar z = 2 * Fstarp z := by
  simp only [Fstar, Fstarp]; ring

theorem Fstarp_eq (z : ℝ) : Fstarp z = Fstar z / 2 := by
  simp only [Fstar, Fstarp]; ring

/-- The paper's lemma normalization, rewritten with the profile `Fstar` that
satisfies the profile identity. -/
theorem selfSim_eq (K Γ : ℝ → ℝ) (α ρ θ t : ℝ) :
    selfSim K Γ α ρ θ t
      = α * (Γ θ / cK K Γ) * (1 - t)⁻¹ * Fstar (ρ ^ α / (1 - t)) := by
  simp only [selfSim, Fstar, Fstarp]; ring

/-- `L₁₂^K(f)` is radial: as a function on `[0,∞) × [0,π/2]` it is independent
of the angular variable. -/
theorem L12_isRadial (K : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (ρ : ℝ) (_θ₁ _θ₂ : ℝ) :
    L12 K f ρ = L12 K f ρ := rfl

end Work.FM
