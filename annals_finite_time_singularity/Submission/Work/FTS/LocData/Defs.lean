/-
# `Work.FTS.LocData` — the LOCALISED DATA of the N9 node of the route

This is the first module of the **localised-data chapter** (`Submission/Work/FTS/LocData/`) of
the dynamic (N9) node of the route of `FTS_AUDIT_LEAD.md` §4:

> N9. Localized data.  Take `F(0) = F_*·χ(z/L) + β h`, with `h` a fixed bump supported in
> `z ∈ [1,2]` that has `L₁₂(h)(0) ≠ 0`, and `β = O(1/L)` chosen so that `L₁₂(g(0))(0) = 0`.
> Then `g(0) = F_*(χ(·/L) − 1) + βh` vanishes near `z = 0`, so the weight `w = (1+z)²/z²` is
> harmless.  Its `𝓗⁴` norm is `O(L^{-1/2})` …  The physical vorticity has compact support for all
> `t`, transported by a Lipschitz field.

The point of the node is that **localisation changes only the initial data**: the profile
`F_* = α (Γ(θ)/c) 2z/(1+z)²` is replaced by its cut-off `F_*·χ(z/L)` plus a small bump `βh`, so
that the *physical* vorticity `F(R,θ) e_θ` is compactly supported — which is what makes the
far-field clauses of the challenge statement trivially true (see `HANDOFF.md`, "ROUTE").

## Conventions

* Functions of the self-similar variables are curried, `f : ℝ → ℝ → ℝ`, applied as `f z θ`; the
  domain is the quadrant `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, with the measure `dz dθ` (never
  `z dz dθ`) — the convention of `Work.Spaces`, `Work.Construction`, `Work.Stability`.
* `F_*` is `Work.Construction.Fstar`, `χ` is `Work.Stability.chi` (the *explicit* cut-off
  `smoothTransition (2 - ‖x‖)`, `= 1` on `[-1,1]`, `= 0` off `(-2,2)`), `zfar L F` is the
  complementary far part `(1 - χ(z/L))·F`.
* `L₁₂` is `Work.Construction.L12 = Work.FM.L12 Work.Spaces.K`.
* Smoothness on the quadrant is `SmoothQuad`: genuine `C^∞` (the order `smoothOrder`) on
  `z > -1, 0 < θ < π/2`.  **It must not be spelled `ContDiffOn ℝ ⊤`**: in this Mathlib
  `⊤ : ℕ∞ω` is *analyticity*, and `Work.Spaces.SmoothNbhd` (used by
  `Work.Spaces.SmoothCompact_HkInf`) is therefore a hypothesis that a compactly supported
  function can satisfy only by vanishing identically (see `Work.Stability.ZcutSmoothCompact`,
  "A remark on the hypothesis `SmoothNbhd`").  A cut-off is `C^∞` but never analytic, so every
  statement of this chapter is phrased with `SmoothQuad` / `smoothOrder`.
* The **physical vorticity** of a profile `F` is the `e_θ`-field `omegaProfile p F`:
  `x ↦ F (ρ(x)^p) (θ(x)) • e_θ(x)`, with `ρ = ‖x‖` (`Work.Cyl.rho`), `θ = arctan(x₃/r)`
  (`Work.Cyl.theta`).  Its support is controlled by the vanishing of `F` for large `z`
  (`ProfileZeroFar`), which is the only property of the profile needed for compact support.

## What is in this module

The definitions and their unfolding lemmas: `locData`, `locG`, `SmoothQuad`, `DataAdm`,
`omegaProfile`, `ProfileZeroFar`, and the concrete bump `hLoc`.  All the *statements* about them
(the smallness of `g(0)` in `𝓗⁴`, the `L₁₂`-orthogonality, the compact support) are in the
sibling modules of the chapter.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- `ℝ³` (definitionally `Work.Cyl.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The localised profile -/

/-- **THE LOCALISED PROFILE** of the route: the profile `F_*` cut off at scale `L`, plus a small
multiple of the bump `h`,

  `locData α L β h = fun z θ => F_*(z,θ)·χ(z/L) + β·h(z,θ)`.

`χ(z/L) = 1` for `z ≤ L` (`L > 0`), so `locData` agrees with the full profile `F_*` near
`z = 0`; it vanishes identically for `z ≥ 2L` together with `h`, so the physical vorticity is
compactly supported (`ProfileZeroFar`). -/
noncomputable def locData (α L β : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Fstar α z θ * Work.Stability.chi (z / L) + β * h z θ

@[simp] theorem locData_apply (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locData α L β h z θ
      = Work.Construction.Fstar α z θ * Work.Stability.chi (z / L) + β * h z θ := rfl

/-- **THE PERTURBATION** `g = locData - F_*` of the modulation: the datum which the
existence theorem (N6) of the route receives.  Note that `locG α L β h` is *not* compactly
supported — `F_*` itself is not — but its support in `z` starts at `z = L`. -/
noncomputable def locG (α L β : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => locData α L β h z θ - Work.Construction.Fstar α z θ

@[simp] theorem locG_apply (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locG α L β h z θ = locData α L β h z θ - Work.Construction.Fstar α z θ := rfl

/-- `locG` in terms of the *far part* of the profile: `g = - zfar L F_* + β h`, where
`Work.Stability.zfar L F = (1 - χ(z/L))·F` vanishes for `z ≤ L`. -/
theorem locG_eq_zfar (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locG α L β h z θ
      = - (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
  rw [locG_apply, locData_apply, Work.Stability.zfar_apply]
  ring

/-- With `β = 0` the localised profile is exactly the cut-off of `F_*`. -/
theorem locData_zero_beta (α L : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locData α L 0 h z θ = Work.Construction.Fstar α z θ * Work.Stability.chi (z / L) := by
  rw [locData_apply]; ring

/-! ## The smoothness class and the admissible data -/

/-- **Genuine `C^∞` on the open quadrant** `z > -1`, `0 < θ < π/2` (the order
`Work.Stability.smoothOrder = ∞`, *not* the analytic order `⊤`).  This is the class in which the
cut-off lives; `Work.Spaces.SmoothNbhd` (analyticity on a neighbourhood of the closed quadrant)
is *not* preserved by a cut-off. -/
def SmoothQuad (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))

/-- **THE ADMISSIBLE PERTURBATIONS** of the self-similar profile at `τ = 0`: the datum class of
the existence theorem (N6) of the route,

* `g` is `C^∞` on the open quadrant (`SmoothQuad`);
* `g` vanishes on the two angular boundaries (`Work.Spaces.VanishTheta`) — the profile of the
  paper vanishes like `Γ(θ) = (sinθ cos²θ)^{α/3}` there, and this is what makes the physical
  `e_θ`-field smooth in the frame and its `div` vanish (`Work.ConstructionInstance`'s
  `div_omega0_all`, `isOddVorticity_omegaS`);
* `g` vanishes to second order at the axis `z = 0` (`g 0 θ = 0` and `∂_z g 0 θ = 0`), which is
  what makes the radial weight `w = (1+z)²/z²` harmless;
* `g ∈ ℋ⁴` **honestly** (`Work.Spaces.HkMem α 4 g`), so that `HkNorm α 4 g` is the sum of the
  squared `L²`-norms of the weighted derivatives rather than the junk value of a non-integrable
  iterated integral.

The class is *inhabited*: `g ≡ 0` is admissible, and so is the perturbation
`locG α L β h = - zfar L F_* + β h` of this chapter (`dataAdm_locG`, `dataAdm_hLoc`). -/
def DataAdm (α : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  SmoothQuad g ∧ Work.Spaces.VanishTheta g ∧
    (∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0) ∧
    Work.Spaces.HkMem α 4 g

theorem DataAdm.smoothQuad {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) : SmoothQuad g := h.1

theorem DataAdm.vanishTheta {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) :
    Work.Spaces.VanishTheta g := h.2.1

theorem DataAdm.zero_axis {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) :
    ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0 := h.2.2.1

theorem DataAdm.hkMem {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) :
    Work.Spaces.HkMem α 4 g := h.2.2.2

/-- All the iterated `D_z`-derivatives of the zero function vanish. -/
theorem DzIter_zero_fun (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- All the iterated `D_θ`-derivatives of the zero function vanish. -/
theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- All the iterated mixed `D`-derivatives of the zero function vanish. -/
theorem mixed_zero_fun (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  simp only [Work.Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zero_fun (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp only [DzIter_zero_fun, mixed_zero_fun, Pi.zero_apply, zero_mul, sq, mul_zero,
    Finset.sum_const_zero, zero_add, ite_self]

/-- The zero function lies in `ℋ^k` for every `k`. -/
theorem HkMem_zero_fun (α : ℝ) (k : ℕ) :
    Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_zero_fun α k z θ).symm
  · refine IntegrableOn.congr_fun integrableOn_zero (fun z _ => ?_) measurableSet_Ici
    rw [funext (fun θ => HkIntegrand_zero_fun α k z θ), integral_zero]

/-- The zero datum is admissible for every `α`: the first witness that `DataAdm` is not a
vacuous class.  (The inhabitation by the *localised* datum is `dataAdm_locG`.) -/
theorem dataAdm_zero (α : ℝ) : DataAdm α (fun _ _ : ℝ => (0 : ℝ)) :=
  ⟨contDiffOn_const, ⟨fun z => rfl, fun z => rfl⟩,
    fun θ _ => ⟨rfl, by simp [Work.Spaces.pz]⟩, HkMem_zero_fun α 4⟩

/-! ## The physical vorticity of a profile -/

/-- **The physical vorticity of a self-similar profile** `F`: the `e_θ`-field
`x ↦ F (ρ(x)^p) (θ(x)) • e_θ(x)`, with `ρ = ‖x‖` and `θ = arctan(x₃/r)`.

This is the paper's `ω^θ` as a vector field (up to the overall sign convention of
`Work.Cyl.vorticity_psiField`): the scalar vorticity of an axisymmetric no-swirl field is a
multiple of `e_θ`, and the self-similar ansatz prescribes its amplitude as a function of
`(R,θ) = (ρ^p, arctan(x₃/r))`.  On the symmetry axis `r = 0` both `e_θ` (Lean's junk `1/0 = 0`)
and the `Γ`-factor of the profile vanish, so the field is `0` there. -/
noncomputable def omegaProfile (p : ℝ) (F : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun x => F (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x

@[simp] theorem omegaProfile_apply (p : ℝ) (F : ℝ → ℝ → ℝ) (x : R3) :
    omegaProfile p F x = F (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl

/-- The profile **vanishes beyond** the self-similar scale `Z`: `F z θ = 0` for every `z ≥ Z`.
This is the hypothesis that transfers localisation of the profile to *compact support* of the
physical vorticity (`hasCompactSupport_omegaProfile`). -/
def ProfileZeroFar (Z : ℝ) (F : ℝ → ℝ → ℝ) : Prop := ∀ z θ : ℝ, Z ≤ z → F z θ = 0

/-! ## The concrete bump `h`, and the angular majorant -/

/-- The **radial factor** of the bump: `bumpZ z = χ(4z - 5)`, with `z`-support the interval
`(3/4, 7/4)` (where `|4z - 5| < 2`) and `= 1` on `(1, 3/2)`. -/
noncomputable def bumpZ (z : ℝ) : ℝ := Work.Stability.chi (4 * z - 5)

/-- **THE BUMP `h`** of the route: `hLoc α z θ = φ(z)·Γ(θ)` with `φ = bumpZ` and
`Γ(θ) = (sinθ cos²θ)^{α/3}` the paper's angular factor.

* Its `z`-support is the interval `(3/4, 7/4)`: it is compactly supported and vanishes on a
  neighbourhood of `z = 0` (so `g 0 θ = ∂_z g 0 θ = 0` for the perturbations built with it).
* Its angular factor is `Γ` itself, so `hLoc` vanishes at `θ = 0` and `θ = π/2`, and — the reason
  for this choice — the whole angular analysis of `hLoc` is *the same* as that of `F_*`: every
  weighted angular derivative is dominated by the single majorant `angMaj` below.
* `L₁₂(hLoc α)(0) = c(α)·∫_0^∞ φ(s)/s ds`, with `c(α) = ∫_0^{π/2} K Γ ∈ [1/10, 10]`
  (`Work.Spaces.c_bounds`) and `∫_0^∞ φ(s)/s ds > 0` (the integrand is `1/s > 0` on the interval
  `(1, 3/2)`), so it is *strictly positive* (see `L12_hLoc` in the sibling modules). -/
noncomputable def hLoc (α : ℝ) (z θ : ℝ) : ℝ := bumpZ z * Work.Spaces.Gam α θ

@[simp] theorem hLoc_apply (α z θ : ℝ) :
    hLoc α z θ = bumpZ z * Work.Spaces.Gam α θ := rfl

@[simp] theorem bumpZ_apply (z : ℝ) : bumpZ z = Work.Stability.chi (4 * z - 5) := rfl

/-- **THE ANGULAR MAJORANT** of the chapter: the single angular function that dominates every
weighted angular derivative of `F_* = α(Γ/c)·2z/(1+z)²` *and* of the bump `hLoc = φ·Γ`:

  `angMaj α θ = Γ(θ)²·sin(2θ)^{-γ(α)} + Γ(θ)²·sin(2θ)^{-η} + 1`.

It is integrable on `Iθ` with `∫_θ angMaj α ≤ 1000/(3α) + 10001` for `0 < α ≤ 1`
(`integrableOn_angMaj`, `integral_angMaj_le` in `Angular.lean`): the exponents are the two
weights of the paper's `ℋ^k`-integrand, `γ(α) = 1 + α/10` (`Work.Spaces.gam`) and `η = 99/100`
(`Work.Spaces.eta`). -/
noncomputable def angMaj (α θ : ℝ) : ℝ :=
  Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1

@[simp] theorem angMaj_apply (α θ : ℝ) :
    angMaj α θ = Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 := rfl

theorem angMaj_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angMaj α θ := by
  rw [angMaj_apply]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have h2 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  linarith

end Work.FTS.LocData
