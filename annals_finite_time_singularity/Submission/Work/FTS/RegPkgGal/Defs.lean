/-
# `Work.FTS.RegPkgGal.Defs` — the definitions of the Galerkin→regularity bridge (design §4, item 10)

This is the area that owns **item 10 of the physical bridge design**
(`Submission/Work/FTS/FTS_PHYS_BRIDGE.md` §4):

> `regPkg_of_galerkin`: `Galerkin.RegPkg (3α) g`, the equation, the H⁴ bound and the `locG` data
> give `∀ S > 0, Regularity.RegPkg α S A B g̃`, where `g̃` is a C¹ extension of `g` to `τ < 0`.
> Split as R1–R8.

## Correction 5 of the design

The delivered interface `Work.FTS.Regularity.RegPkg` has a **false** third clause in its `htay`
field: the forcing `-μ̄·AK` makes `g ≈ c(τ)·z²·Γ(θ)` near the corner `z = 0, θ = 0`, whence
`∂_θg ~ z²θ^{α-1}`, which is *not* Lipschitz in `θ`.  The correct (and true) form is the *Hölder*
form

  `|g z θ τ - g z θ' τ| ≤ K * z^2 * |θ - θ'|^α`,

which is what `g ≈ c(τ)z²Γ(θ)` does satisfy, `Γ(θ) = (sinθcos²θ)^α` being `α`-Hölder on `Iθ`.

The structure `RegPkg'` below is `Regularity.RegPkg` **verbatim except for that one clause**.  So
that later stages can consume it with the same code shape, its API (`Basic.lean`) mirrors the
delivered `RegPkg` API lemma by lemma; the re-proved consumer of the corrected clause
(`gCompHolder'`, with the constant `gCompConst'`) is in `Consumer.lean`, and `RegPkg → RegPkg'`
(the Lipschitz clause does imply the Hölder one on `z ≤ 2`) is `Regularity.Defs`-free and lives in
`Basic.lean`.

## The extension `g̃`

The design's §4 preamble:

> `g̃ = 0` for `z ≤ 0`; `g̃ = g(z,θ,0) + τ·∂_τg(z,θ,0)` for `τ < 0`; and `g̃ = g` otherwise.

This is `extG g` below.  Note the *order* of the two tests: the `z ≤ 0` clause wins, so
`g̃ z θ τ = 0` for every `z ≤ 0` and every `τ`.

## Conventions

Inherited from `Work.FTS.Regularity` / `Work.Spaces`: `f z θ` is curried, the domain is
`Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, the measure is `dz dθ`, `pExp α = 3α` is the profile exponent, and
`Gamma α θ = (sinθcos²θ)^α` is the angular factor.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- `Fam`, the type of families `(z,θ,τ) ↦ g z θ τ` (definitionally `Work.FTS.Galerkin.Fam`). -/
abbrev Fam := ℝ → ℝ → ℝ → ℝ

/-- The `τ`-slice of a family (definitionally `Work.FTS.Galerkin.slice`). -/
abbrev famSlice (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ

/-- The fake-time derivative `τ ↦ ∂_τ g` (definitionally `Work.FTS.Galerkin.gdot`). -/
abbrev famGdot (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := Work.FTS.Galerkin.gdot g τ

/-! ## The extension `g̃` to negative fake time -/

/-- **THE EXTENSION `g̃` OF `g` TO NEGATIVE FAKE TIME** (design §4 preamble):

  `g̃ z θ τ = 0` if `z ≤ 0`; `g̃ z θ τ = g z θ 0 + τ·∂_τg(z,θ,0)` if `τ < 0`; `g̃ = g` otherwise.

The `z ≤ 0` test comes first, so `g̃` vanishes identically on the closed left half-plane
`{z ≤ 0}`; this is what makes the two axis clauses (`hquad0`, `hquad`) of `RegPkg'` true *by
definition* for `g̃`.  The `τ < 0` branch is the first-order Taylor jet of `g` at `τ = 0` (which is
the jet used in the `Jet α S Nd (∂_τ g)` field of the package), making `g̃` `C¹` across `τ = 0`
once `τ ↦ g z θ τ` is differentiable there. -/
noncomputable def extG (g : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ =>
    if z ≤ 0 then 0 else if τ < 0 then g z θ 0 + τ * deriv (fun s => g z θ s) 0 else g z θ τ

@[simp] theorem extG_of_nonpos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : z ≤ 0) :
    extG g z θ τ = 0 := by
  simp only [extG, if_pos hz]

@[simp] theorem extG_of_neg {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extG g z θ τ = g z θ 0 + τ * deriv (fun s => g z θ s) 0 := by
  simp only [extG, if_neg (not_le.mpr hz), if_pos hτ]

@[simp] theorem extG_of_pos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : 0 < z) (hτ : 0 ≤ τ) :
    extG g z θ τ = g z θ τ := by
  simp only [extG, if_neg (not_le.mpr hz), if_neg (not_lt.mpr hτ)]

theorem extG_eq_of_pos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : 0 < z) (hτ : 0 ≤ τ) :
    extG g z θ τ = g z θ τ := extG_of_pos hz hτ

theorem extG_zero_fun (z θ τ : ℝ) : extG (fun _ _ _ : ℝ => (0 : ℝ)) z θ τ = 0 := by
  rw [extG]
  split_ifs <;> simp

/-! ## The corrected regularity package `RegPkg'` -/

/-- **THE CORRECTED REGULARITY PACKAGE `RegPkg'`**: `Work.FTS.Regularity.RegPkg` **verbatim**
except that the third clause of `htay` is the *Hölder* form of design correction 5,

  `|g z θ τ - g z θ' τ| ≤ K · z² · |θ - θ'|^α`,

instead of the false Lipschitz form `≤ K·z·|θ - θ'|`.  See the module docstring.

Every other field is the delivered one, field for field, so that all the downstream physical
transfer lemmas (`Work.FTS.Regularity.Slice`, `Time`, `Bundle`) can be re-run on `RegPkg'` by the
same arguments with `Basic.tay'`/`Basic.zmod'`/`Basic.thmod'` in place of `RegPkg.tay`/`zmod`/
`thmod`; only the composite Hölder transfer genuinely changes, and its re-proof is
`Consumer.gCompHolder'`. -/
structure RegPkg' (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < α
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the amplitude of the physical vorticity is positive on the strip -/
  hA : ∀ τ ∈ Set.Icc 0 S, 0 < A τ
  /-- the self-similar scaling is positive on the strip -/
  hB : ∀ τ ∈ Set.Icc 0 S, 0 < B τ
  /-- the amplitude is bounded above and below on the strip -/
  hAb : ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S, a₀ ≤ A τ ∧ A τ ≤ a₁
  /-- the scaling is bounded above and below on the strip -/
  hBb : ∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S, b₀ ≤ B τ ∧ B τ ≤ b₁
  /-- the amplitude is differentiable on the strip, with its `deriv` as derivative -/
  hAdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt A (deriv A τ) τ
  /-- the scaling is differentiable on the strip, with its `deriv` as derivative -/
  hBdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt B (deriv B τ) τ
  /-- the derivative of the amplitude is bounded on the strip -/
  hAd : ∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ a₂
  /-- the derivative of the scaling is bounded on the strip -/
  hBd : ∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ b₂
  /-- the derivative of the amplitude is `α`-Hölder on the strip -/
  hAdh : ∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv A τ - deriv A τ'| ≤ a₃ * |τ - τ'| ^ α
  /-- the derivative of the scaling is `α`-Hölder on the strip -/
  hBdh : ∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv B τ - deriv B τ'| ≤ b₃ * |τ - τ'| ^ α
  /-- the perturbation vanishes on the two angular boundaries -/
  hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (gSlice g τ)
  /-- the perturbation vanishes at `z = 0` -/
  hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.pz (gSlice g τ) 0 θ = 0
  /-- the joint `α`-Hölder data of the perturbation -/
  hg : ∃ Ng : ℝ, Jet α S Ng g
  /-- the joint `α`-Hölder data of `∂_z g` -/
  hpz : ∃ Npz : ℝ, Jet α S Npz (fun z θ τ => Work.Spaces.pz (gSlice g τ) z θ)
  /-- the joint `α`-Hölder data of `∂_τ g` -/
  hgdoth : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => g z θ s) τ)
  /-- the uniform angular vanishing `|g| ≤ Cv·Γ(θ)` of the perturbation -/
  hvan : ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |g z θ τ| ≤ Cv * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, with the near-origin `z`-Lipschitz bound and the
  **corrected (Hölder) angular bound** of design correction 5 -/
  htay : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
      |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α)
  /-- the full profile is compactly supported in the self-similar variable `z` -/
  hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0
  /-- the honest `ℋ⁴`-membership of every slice -/
  hH4 : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (gSlice g τ)
  /-- the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ` -/
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
    (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1))

/-! ## The minimal Galerkin input `RegPkgMin` (design `FTS_STRONG_ROUTE.md` §1, §4)

The `Galerkin.RegPkg` interface asked for more than the strong-solution route can supply: a `C^∞`
(`smoothOrder`) field on `τ ∈ (-1,0)`, `ℋ⁵`-membership and an `ℋ³`-*membership* of `∂_τg` (which
does not support R5, since R5 needs a *uniform* bound).  `FTS_STRONG_ROUTE.md` §1 pinpoints which
fields are actually consumed by Open2 and by R1–R8 and proposes the following replacement, which
this area takes as its input (the lead's instruction of 2026-10-07). -/

/-- **THE MINIMAL INPUT `RegPkgMin`** of the Galerkin→regularity bridge
(`Submission/Work/FTS/FTS_STRONG_ROUTE.md` §1 and §4):

* `c1` — joint `C¹` on `z > 0, 0 < θ < π/2, τ > 0`;
* `c4` — `C⁴` on the open quadrant `Q0`, at every strip time `τ ≥ 0` (the field that replaces the
  `C^∞` field `Galerkin.RegPkg.smooth`, and which is what the `𝒲`-sup lemmas of R2–R4 consume);
* `cont` — continuity in `τ` on `Ici 0` at fixed `(z,θ) ∈ Qd`;
* `mem4` — honest `ℋ⁴`-membership at every `τ ≥ 0`;
* `dbd` — a **uniform** `ℋ³` bound on `∂_τg` for `τ > 0` (this is what R5 consumes; the delivered
  `Galerkin.RegPkg.deriv3` gives membership only, which is not a bound);
* `vanish` — vanishing on the two angular boundary lines. -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  /-- joint `C¹` on the open slab `z > 0, 0 < θ < π/2, τ > 0` -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)
  /-- `C⁴` on the open quadrant, at every strip time -/
  c4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
    Work.FTS.EllipticEst.Q0
  /-- continuity in `τ` on `[0,∞)` at every point of the open quadrant -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- honest `ℋ⁴`-membership at every `τ ≥ 0` -/
  mem4 : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ)
  /-- a **uniform** `ℋ³` bound on `∂_τg` for `τ > 0` -/
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd
  /-- vanishing on the two angular boundaries -/
  vanish : ∀ τ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0

/-! ## The corrected composite Hölder constant -/

/-- **The corrected Hölder constant of the composite profile** `x ↦ g (ρ(x)^{3α}) (|θ(x)|)`.

This is `Work.FTS.Regularity.gCompConst` with its last summand changed from the `z·|Δθ|`-term
`K·(3/2)·3^α·(3/2)^{2α}` to the term produced by the corrected Hölder clause
`|Δg| ≤ K·z²·|Δθ|^α`, namely `K·(3/2)^{6α}·(4π)^α` (the near-origin branch gives
`z²|Δψ|^α ≤ (3/2)^{6α}·(4π)^α·min(ρ)^{5α}·d^α ≤ (3/2)^{6α}(4π)^α d^α` since `min ρ ≤ 1` there).
The remaining six summands are literally those of `gCompConst`. -/
def gCompConst' (α Cv Lg Lθ K : ℝ) : ℝ :=
  2 * Cv + (2 * Cv * (3 / 2) ^ α
    + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)
        + K * (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α))))

/-- `gCompConst'` as a nonnegative real (the form in which `HolderWith` consumes it). -/
def gCompConstNN' (α Cv Lg Lθ K : ℝ) : ℝ≥0 :=
  ⟨|gCompConst' α Cv Lg Lθ K|, abs_nonneg _⟩

theorem gCompConst'_nonneg (α Cv Lg Lθ K : ℝ) (hα : 0 ≤ α) (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg)
    (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K) : 0 ≤ gCompConst' α Cv Lg Lθ K := by
  rw [gCompConst']
  have h1 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ (4 * Real.pi) ^ α := Real.rpow_nonneg (by positivity) _
  have h3 : (0 : ℝ) ≤ 3 ^ (6 * α) := Real.rpow_nonneg (by norm_num) _
  have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have h5 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (2 * α) := Real.rpow_nonneg (by norm_num) _
  have h6 : (0 : ℝ) ≤ (3 * α) ^ α := Real.rpow_nonneg (by linarith) _
  positivity

theorem gCompConstNN'_coe (α Cv Lg Lθ K : ℝ) (hα : 0 ≤ α) (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg)
    (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K) :
    (gCompConstNN' α Cv Lg Lθ K : ℝ) = gCompConst' α Cv Lg Lθ K := by
  rw [gCompConstNN']
  exact_mod_cast abs_of_nonneg (gCompConst'_nonneg α Cv Lg Lθ K hα hCv hLg hLθ hK)

end Work.FTS.RegPkgGal
