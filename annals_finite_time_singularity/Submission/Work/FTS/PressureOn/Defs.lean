/-
# `Work.FTS.PressureOn` — the pressure reconstruction for the physical solution (node N8b)

This is the area that owns the **corrected pressure input** of the physical reconstruction,
`Work.FTS.PressureOn.PressureReconstructionOn`, replacing the false
`Work.LWP.PressureReconstruction` (which is refuted by the two counterexamples of
`FTS_INTEGRATION_AUDIT.md` §3, and whose `BiotSavartLaw` sibling is *proved false* in Lean by
`Submission/Work/FTS/FTS_NOTBSL.lean.txt`).

The area is the *pressure half* of the physical bridge design
(`Submission/Work/FTS/FTS_PHYS_BRIDGE.md` §1, item 5 of the dispatch list).  Its input is the
physical vorticity `ω` of a compactly supported swirl profile whose Biot–Savart velocity
`u = physVel ω` is jointly `C^{1,α}` on the strips, and it produces the pressure `p` of the
incompressible Euler equation.

## The construction

Write `f := u × ω` (the Lamb vector) and let `Nfund = −(4π‖·‖)⁻¹` be the *fundamental solution* of
the Laplacian in `ℝ³` (the normalisation with `Δ Nfund = δ₀`).  The pressure is reconstructed
*explicitly* as

  `p := −‖u‖²/2 − q`,   `q := −(∇Nfund)∗(u × ω)`

i.e. `q` is (minus) the `∇Nfund`-convolution of the Lamb vector, which is the decaying solution of
the Poisson equation `Δq = −div f`.  Equivalently `q = ∫ ⟪newtonGrad (x−y), f y⟫ dy` with
`newtonGrad z = ∇(4π‖z‖)⁻¹ = −z/(4π‖z‖³) = −∇Nfund z`; this is `pressurePotential f` below.

The signs are pinned by the classical computation (re-derived here, since it is what fixes the
definitions).  With `N := (4π‖·‖)⁻¹` one has `Δ(N∗g) = −g`, hence

  `Δ q = Δ div(N∗f) = div(Δ(N∗f)) = −div f`,

while taking the divergence of the Euler equation gives `Δ(p + ‖u‖²/2) = div f`.  So `Δq = −div f`
is exactly the Poisson equation satisfied by `q = −p − ‖u‖²/2`, and its decaying solution is
`q = −(∇Nfund)∗f`.  Equivalently the reconstruction is the identity `∇q = ∂_t u − f`, which
combined with `(u·∇)u = ∇(‖u‖²/2) − u×ω` gives `∂_t u + (u·∇)u + ∇p = 0`.

The classical route (`FTS_PHYS_BRIDGE.md` §1):

* `f = u×ω` is compactly supported (the vorticity is, by hypothesis), so the singular integral
  for `q` converges with the integrable kernel `|∇N| ~ ‖x−y‖^{-2}`;
* `∂_t q = −(∇N)∗∂_t f` by dominated convergence, and it is continuous;
* the field `D := ∇q − ∂_t u + f` is continuous, tends to `0` at infinity, and is *distributionally*
  divergence- and curl-free — the curl identity coming from
  `curl(u×ω) = (u·∇)ω − (ω·∇)u` (valid on `Uax`, whose complement is null) together with the
  pointwise vorticity equation and the distributional commutation of `∂_t` with `∂_x`; the
  divergence identity from `Δq = −div f` and `div u(·,t) = 0`.  Hence `D = 0` by the
  Weyl/Liouville lemma, i.e. `∇q = ∂_t u − f`;
* the Euler equation follows from the vector identity `(u·∇)u = ∇(‖u‖²/2) − u×ω`;
* joint `C¹` of `p` is the joint continuity of the pieces (with `∂_t q` continuous).

## Conventions

Everything is stated in the workspace vocabulary: `R3 = EuclideanSpace ℝ (Fin 3)`,
`physVel ω x t = biotSavart (ω · t) x` (from `Work.FTS.Physical.Defs`), `div`, `vorticity`,
`timeDeriv`, `directionalDeriv`, `spaceGrad` (from `ChallengeDeps`), and `IsContDiffHolderOn`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.FTS.Physical.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- `ℝ³`, definitionally `Work.LWP.R3` and `Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The open set on which the pointwise vorticity equation is available -/

/-- **The complement of the singular set.**  `Uax` is `ℝ³` with the axis `x₀ = x₁ = 0` and the
plane `x₂ = 0` removed.  On `Uax` the paper's meridian coordinates are non-degenerate and the
pointwise vorticity equation `∂_tω + (u·∇)ω = (ω·∇)u` is available; its complement is a union of a
plane and a line, hence null. -/
def Uax : Set R3 := {x | x 2 ≠ 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0}

/-- `Uax` is open (the complement of a plane and of a line). -/
theorem isOpen_Uax : IsOpen Uax := by
  have hc0 : Continuous fun x : R3 => x 0 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0
  have hc1 : Continuous fun x : R3 => x 1 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1
  have hc2 : Continuous fun x : R3 => x 2 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2
  have h1 : IsOpen {x : R3 | x 2 ≠ 0} :=
    isOpen_compl_iff.mpr (isClosed_eq hc2 continuous_const)
  have h2 : IsOpen {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} := by
    have hcl : IsClosed {x : R3 | x 0 ^ 2 + x 1 ^ 2 = 0} :=
      isClosed_eq ((hc0.pow 2).add (hc1.pow 2)) continuous_const
    simpa only [ne_eq, Set.compl_ofPred] using isOpen_compl_iff.mpr hcl
  have : Uax = {x : R3 | x 2 ≠ 0} ∩ {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} := rfl
  rw [this]
  exact h1.inter h2

/-! ## The Newtonian kernel and the scalar potential `q` -/

/-- **The gradient of the Newtonian kernel `N = (4π‖·‖)⁻¹`**: `∇N z = −z/(4π‖z‖³)`. -/
noncomputable def newtonGrad (z : R3) : R3 := -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z

/-- **The gradient of the fundamental solution `Nfund = −(4π‖·‖)⁻¹`** (the normalisation with
`Δ Nfund = δ₀`): `∇Nfund z = z/(4π‖z‖³) = −newtonGrad z`.  The design's potential is
`q = −(∇Nfund)∗(u×ω)`. -/
noncomputable def nablaNfund (z : R3) : R3 := ((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z

@[simp] theorem nablaNfund_eq_neg_newtonGrad (z : R3) : nablaNfund z = -newtonGrad z := by
  unfold nablaNfund newtonGrad
  simp

/-- **The scalar potential of the pressure reconstruction**, the design's
`q = −(∇Nfund)∗(u×ω)`: `q x = −∫ ⟪∇Nfund(x−y), f y⟫ dy = ∫ ⟪newtonGrad(x−y), f y⟫ dy`.  It is
the decaying solution of the Poisson equation `Δq = −div f` (see the module docstring). -/
noncomputable def pressurePotential (f : R3 → R3) (x : R3) : ℝ :=
  -∫ y, inner ℝ (nablaNfund (x - y)) (f y)

/-- The kernel form of the potential: `q x = ∫ ⟪newtonGrad(x−y), f y⟫ dy`.  This is the form in
which the kernel bounds are stated. -/
theorem pressurePotential_eq_integral_newtonGrad (f : R3 → R3) (x : R3) :
    pressurePotential f x = ∫ y, inner ℝ (newtonGrad (x - y)) (f y) := by
  have h : (fun y => inner ℝ (nablaNfund (x - y)) (f y))
      = fun y => -inner ℝ (newtonGrad (x - y)) (f y) := by
    funext y
    rw [nablaNfund_eq_neg_newtonGrad, inner_neg_left]
  rw [pressurePotential, h, integral_neg, neg_neg]

/-- **The Lamb vector** of the velocity/vorticity pair, as a space-time field. -/
noncomputable def lamb (u ω : R3 → ℝ → R3) : R3 → ℝ → R3 :=
  fun x t => WithLp.toLp 2 (u x t ⨯₃ ω x t)

/-- **The pressure of the reconstruction**: `p := −‖u‖²/2 − q` with `q` the Newtonian potential of
the Lamb vector `u × ω` of `u = physVel ω`. -/
noncomputable def pressureOn (ω : R3 → ℝ → R3) : R3 → ℝ → ℝ := fun x t =>
  -(‖physVel ω x t‖ ^ 2 / 2)
    - pressurePotential (fun y => WithLp.toLp 2 (physVel ω y t ⨯₃ ω y t)) x

@[simp] theorem newtonGrad_apply (z : R3) :
    newtonGrad z = -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z := rfl

@[simp] theorem pressurePotential_apply (f : R3 → R3) (x : R3) :
    pressurePotential f x = -∫ y, inner ℝ (nablaNfund (x - y)) (f y) := rfl

@[simp] theorem lamb_apply (u ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    lamb u ω x t = WithLp.toLp 2 (u x t ⨯₃ ω x t) := rfl

@[simp] theorem pressureOn_apply (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    pressureOn ω x t = -(‖physVel ω x t‖ ^ 2 / 2)
      - pressurePotential (fun y => WithLp.toLp 2 (physVel ω y t ⨯₃ ω y t)) x := rfl

/-- The kernel is odd: `newtonGrad (−z) = −newtonGrad z`. -/
theorem newtonGrad_neg (z : R3) : newtonGrad (-z) = -newtonGrad z := by
  have hz : ‖-z‖ = ‖z‖ := norm_neg z
  simp only [newtonGrad_apply, hz, smul_neg]

/-- The pointwise size of the kernel: `‖∇N(z)‖ = (4π)^{-1}‖z‖^{-2}`.  This is the `L²`-marginal
kernel which makes the convolution integral conditionally convergent at infinity and integrable
over the (bounded) support of the Lamb vector. -/
theorem norm_newtonGrad (z : R3) :
    ‖newtonGrad z‖ = (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ := by
  rw [newtonGrad_apply, norm_smul, norm_neg]
  have h : ‖((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ : ℝ)‖
      = (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
  rw [h]

/-! ## The statement of the pressure reconstruction -/

/-- **Pressure reconstruction on the physical solution (design §1).**

For a physical vorticity field `ω` whose Biot–Savart velocity `u = physVel ω` is jointly `C^{1,α}`
on the strips `ℝ³ × [0,S]`, `S < T`, is the curl of `ω` at every time, is divergence-free, and is
compactly supported on every strip; and whose time derivative `∂_tω` is jointly continuous on
`ℝ³ × [0,T)` (with `ω x` differentiable in `t` from the right at every `t ∈ [0,T)`, and `Dω(·,t)`
locally integrable), and which solves the vorticity equation pointwise on the open set `Uax` (the
complement of the axis and of the plane, a null set) — there is a pressure `p`, jointly `C¹` on
`ℝ³ × [0,T)`, with `∂_t u + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.

The extra hypotheses are exactly what excludes the two counterexamples to the old
`Work.LWP.PressureReconstruction`: the `HasDerivWithinAt` clause excludes the Cantor-staircase
shear (whose `∂_tω` is not a derivative), and `u = physVel ω` excludes the `u = (a(t),0,0)` field
(which is not the Biot–Savart field of its vorticity).  The pressure is the explicit
`pressureOn ω = −‖u‖²/2 − q`, `q = −(∇N)∗(u×ω)`. -/
def PressureReconstructionOn (α : ℝ≥0) : Prop := ∀ (ω : R3 → ℝ → R3) (T : ℝ),
  let u := physVel ω
  (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
  (∀ t ∈ Ico 0 T, ∀ x, vorticity (u · t) x = ω x t) → (∀ t ∈ Ico 0 T, div (u · t) = 0) →
  (∀ S ∈ Ioo 0 T, ∃ R, ∀ t ∈ Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R) →
  ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (univ ×ˢ Ico 0 T) →
  (∀ x, ∀ t ∈ Ico 0 T, HasDerivWithinAt (ω x) (timeDeriv ω x t) (Ici t) t) →
  (∀ t ∈ Ioo 0 T, LocallyIntegrable (fun x => fderiv ℝ (ω · t) x)) →
  (∀ t ∈ Ioo 0 T, ∀ x ∈ Uax, ContDiffAt ℝ 2 (u · t) x ∧ ContDiffAt ℝ 1 (ω · t) x ∧
     timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t) →
  ∃ p, ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T) ∧
    ∀ x, ∀ t ∈ Ioo 0 T, timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0

/-! ## The Newtonian kernel and the Hessian trace -/

/-- The cross product as an element of `R3` (the notation `⨯₃` returns `Fin 3 → ℝ`). -/
def crossVec (a b : R3) : R3 := WithLp.toLp 2 (a ⨯₃ b)

@[simp] theorem crossVec_apply (a b : R3) : crossVec a b = WithLp.toLp 2 (a ⨯₃ b) := rfl

/-- **The Newtonian kernel** `N z = (4π‖z‖)⁻¹`; `newtonGrad = ∇N`. -/
noncomputable def newtonKernel (z : R3) : ℝ := (4 * Real.pi * ‖z‖)⁻¹

/-- **The trace of the Hessian**, `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)`, the Euclidean Laplacian in
the standard basis (`FiniteTimeSingularity.e i`). -/
noncomputable def laplaceTrace (φ : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) x
    (FiniteTimeSingularity.e i)

/-- The vector-valued analogue of `laplaceTrace`. -/
noncomputable def laplaceTraceVec (g : R3 → R3) (x : R3) : R3 :=
  ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ g w (FiniteTimeSingularity.e i)) x
    (FiniteTimeSingularity.e i)

end Work.FTS.PressureOn
