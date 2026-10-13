/-
# `Work.FTS.RegPkgGal.RVocab` — the vocabulary of the R-lemmas (design §4)

This file fixes the two extra notions the R-lemmas of design §4
(`Submission/Work/FTS/FTS_PHYS_BRIDGE.md`) are stated over:

* `StData α S g` — the **`St1`-class data** of the paper.  This is the *class* in which the
  perturbation `g` of Elgindi's construction lives (`Papers/elgindi/Classical_Euler_arXiv_2.tex`,
  §Setup and §Modulation): `g` vanishes at least like `Γ(θ) = (sinθcos²θ)^α` in the angular
  variable (together with its angular derivative) and at least quadratically at `z = 0`.  It is
  what makes the physical `e_θ`-field vanish fast enough on the plane `x₃ = 0` and on the axis,
  and it is *assumed* of the solution by R2–R5: see the note below.

  **It is not derivable from `RegPkgMin` + the `ℋ⁴` bound.**  `ℋ⁴`-membership is an `L²`-type
  condition with the *fixed* weight `sin(2θ)^{-γ}`, `γ = 1 + pα/10` (`pα = pExp α = 3α`): the
  angular slot `∫_0^{π/2} (D_θ g)² sin(2θ)^{-γ} < ∞` (and likewise for the higher `D_θ`-slots)
  is satisfied by `g(z,θ) ≈ θ^{pα/20}|log θ|^{-p}`, i.e. by functions that vanish *much more
  slowly* than `Γ ≈ θ^{pα/3}`; and the paper's own embedding `ℋ² ⊂ C^β` (`β < γ-1 = pα/10`) is
  weaker than `Γ`-vanishing for every `pα > 0`.  The `𝒲^{4,∞}`-weight `sin(2θ)^{-pα/5}/(pα+sin2θ)`
  is weaker still (it allows `θ^{pα/5}`, giving `|g| ≲ θ^{pα/5}` by one integration).  So the
  `Γ`-vanishing is genuine *extra* information, carried by the paper's class and preserved by the
  modulation equation (`F = F_* + g` with `F_* ∝ Γ` and a `Γ`-compatible linear part); it must be
  exported by the `a`-priori/strong-solution machinery of the route, exactly as the localized
  datum supplies it at `τ = 0` (`Work.FTS.LocData.locG` vanishes identically near `z = 0` and is
  `Γ`-shaped).

  Likewise the quadratic vanishing at `z = 0` is a class condition (paper, "in order to solve for
  `g`, we need `g` and the RHS to vanish at least quadratically at `z = 0`"): the `ℋ⁴`-weight
  `w² ~ z^{-4}` forces only `g = o(z^{3/2})` by Cauchy–Schwarz.

* `DynEqF' α μ F Φ` — the **dynamic profile equation `(E)`** of design §3, i.e. the transport form
  in which the support propagation (R7) is read: it is the copy of
  `Work.FTS.MeridianDyn.DynEqF` (module of the sibling area `MeridianDyn`, which owns the passage
  `IsDynEqOn ⟹ (E)`), taken here so that R7 does not have to import a file owned by another area.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic

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

/-! ## The `St1`-class data -/

/-- **THE `St1`-CLASS DATA** of the perturbation `g` on the strip `[0,S]`: the two class
conditions of the paper's construction that are *not* consequences of `ℋ⁴`-membership (see the
module docstring):

* `dthvan` — the angular derivative `D_θ g = sin(2θ)∂_θg` is dominated by `Γ`: this is the
  quantitative form of the `Γ`-vanishing of the class.  Integrating it (using `g(z,0) = 0`) gives
  `|g| ≤ Cv Γ` (R4) and the `α`-Hölder modulus of `g` in `θ` (R3).
* `quad` — the quadratic vanishing at `z = 0` (`|g| ≤ K z²` for `z ≤ 2`) and the linear bound on
  `∂_zg` there, i.e. the Taylor datum.  The clause `z ≤ 2` is the one consumed by
  `RegPkg'.htay`. -/
structure StData (α S : ℝ) (g : Fam) : Prop where
  /-- `|D_θ g| ≤ Cθ · z² · Γ(θ)`: the `Γ`-vanishing of the angular derivative, with the `z²`
  factor that makes the class stable under `×z²` (the true profile is `g ≈ c(τ)z²Γ(θ)`).  The
  `z²` is what turns this into the *corrected* `htay` angular clause `≤ K z²|Δθ|^α`, since
  `Γ/sin(2θ) ≈ θ^{α-1}` integrates to `θ^α`. -/
  dthvan : ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |Work.Spaces.Dth (gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, and the linear vanishing of `∂_zg` there -/
  quad : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |Work.Spaces.pz (gSlice g τ) z θ| ≤ Q * z)

theorem StData.dthvan' {α S : ℝ} {g : Fam} (h : StData α S g) :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Gamma α θ := h.dthvan

theorem StData.quad' {α S : ℝ} {g : Fam} (h : StData α S g) :
    ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |Work.Spaces.pz (gSlice g τ) z θ| ≤ Q * z) := h.quad

/-! ## The dynamic profile equation `(E)` -/

/-- The left-hand side of the **dynamic profile equation** `(E)` at a point, with the fake-time
derivative `Fτ` as a parameter: `Fτ + (1+μ)F + (1-μ)D_zF + UVR α F Φ`. -/
def dynEqLHS (α : ℝ) (μ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ Fτ : ℝ) : ℝ :=
  Fτ + (1 + μ) * F Z Θ + (1 - μ) * Work.Spaces.Dz F Z Θ + Work.Construction.UVR α F Φ Z Θ

/-- **The dynamic profile equation `(E)`** (design §3): the paper's modulation equation for the
*full* profile `F = F_* + g` in fake time,

  `∂_τ F + (1+μ(τ))·F + (1-μ(τ))·D_z F + UVR α F Φ = 0`   on the open quadrant, `τ > 0`.

Its transport form is what R7 (support propagation along characteristics) is stated over.  This is
a copy of `Work.FTS.MeridianDyn.DynEqF` (sibling area `MeridianDyn`, which owns the passage from
`IsDynEqOn`). -/
def DynEqF (α : ℝ) (μ : ℝ → ℝ) (F Φ : Fam) : Prop :=
  ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
    deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
      + (1 - μ τ) * Work.Spaces.Dz (famSlice F τ) z θ
      + Work.Construction.UVR α (famSlice F τ) (famSlice Φ τ) z θ = 0

theorem DynEqF.eq {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ)
    {z θ τ : ℝ} (hz : (z, θ) ∈ Work.Construction.Qd) (hτ : 0 < τ) :
    deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
      + (1 - μ τ) * Work.Spaces.Dz (famSlice F τ) z θ
      + Work.Construction.UVR α (famSlice F τ) (famSlice Φ τ) z θ = 0 :=
  h z θ τ hz hτ

theorem DynEqF.pointwise {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ)
    {Z Θ τ : ℝ} (hZ : (Z, Θ) ∈ Work.Construction.Qd) (hτ : 0 < τ) :
    dynEqLHS α (μ τ) (famSlice F τ) (famSlice Φ τ) Z Θ (deriv (fun s => F Z Θ s) τ) = 0 := by
  have h0 := h Z Θ τ hZ hτ
  rw [dynEqLHS]
  simpa only [famSlice, Work.FTS.Galerkin.slice_apply, Work.Spaces.Dz] using h0

/-! ## The clock of the modulation (design §2)

The vorticity amplitude `A_v` and the space scale `B` of the reconstruction are the exponentials of
the two modulation rates `1 ± m`, `m = muDyn` (design §2, item 8):
`A_v(τ) = exp(-∫_0^τ(1+m))`, `B(τ) = exp(-∫_0^τ(1-m))`; note `(1+m)(1+λ) = 1-m` for
`λ = -2m/(1+m)`, which is the paper's second modulation constant (`Galerkin.lamDyn`). -/

/-- `A_v(τ) = exp(-∫_0^τ (1+m(s)) ds)` of the design §2. -/
noncomputable def Avort (m : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 + m s))

/-- `B(τ) = exp(-∫_0^τ (1-m(s)) ds)` of the design §2. -/
noncomputable def Bdyn (m : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 - m s))

theorem Avort_zero (m : ℝ → ℝ) : Avort m 0 = 1 := by simp [Avort]

theorem Bdyn_zero (m : ℝ → ℝ) : Bdyn m 0 = 1 := by simp [Bdyn]

end Work.FTS.RegPkgGal
