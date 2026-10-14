import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.R1G.vecResid_eq_scalar_smul

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

/-- **R5 AT THE PRIMITIVE LEVEL**: the constituents of the right-hand side of the fake-time
equation, in the shape in which the paper's estimates produce them.  See the module docstring. -/
structure R5Parts (α S : ℝ) (g Φ : Fam) : Prop where
  /-- the dynamic equation (`IsDynEqOn`, the one-sided-in-`τ` form produced by Open2) -/
  hsol : Work.FTS.Galerkin.IsDynEqOn (pExp α) Φ g
  /-- the two-sided `τ = 0` equation, which glues the extension at `τ = 0` -/
  h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
    HasDerivAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (pExp α) g 0 z θ + Work.FTS.Galerkin.dynRHS (pExp α) Φ g 0 z θ) 0
  /-- the four constituents of `dynLin + dynRHS` are jointly `Jet`s (one common constant) -/
  hJ : ∃ NJ : ℝ,
    Jet α S NJ (fun z θ τ => -(Work.Coercivity.LGammaT (pExp α) (gSlice g τ) z θ))
    ∧ Jet α S NJ (fun z θ τ => Work.Construction.N0 (pExp α)
        (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ) z θ)
    ∧ Jet α S NJ (fun z θ τ => Work.Construction.N (pExp α)
        (Work.Construction.Ftau (pExp α) g τ) (gSlice Φ τ) z θ)
    ∧ Jet α S NJ (fun z θ τ => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (pExp α) Φ g τ) (Work.FTS.Galerkin.lamDyn (pExp α) Φ g τ)
        (gSlice g τ) z θ)
  /-- the uniform bound of `mubar` -/
  hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
    |Work.Construction.mubar
      (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
      (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) g τ) (gSlice Φ τ))| ≤ M
  /-- the `τ`-modulus of `mubar` -/
  hmbh : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) g τ) (gSlice Φ τ))
      - Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) g τ') (gSlice g τ'))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) g τ') (gSlice Φ τ'))|
      ≤ M * |τ - τ'| ^ α
  /-- the `z`-differentiability of the linear constituent -/
  hLz : ∃ NZ : ℝ, 0 ≤ NZ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => -(Work.Coercivity.LGammaT (pExp α) (gSlice g τ) z' θ)) d z
      ∧ |d| ≤ NZ
  /-- the `z`-differentiability of `N₀` -/
  hN₀z : ∃ NZ : ℝ, 0 ≤ NZ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N0 (pExp α)
      (Work.Construction.Ftau (pExp α) g τ) (gSlice g τ) z' θ) d z ∧ |d| ≤ NZ
  /-- the `z`-differentiability of `N` -/
  hNz : ∃ NZ : ℝ, 0 ≤ NZ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N (pExp α)
      (Work.Construction.Ftau (pExp α) g τ) (gSlice Φ τ) z' θ) d z ∧ |d| ≤ NZ
  /-- the `z`-differentiability of `N_*` -/
  hNsz : ∃ NZ : ℝ, 0 ≤ NZ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
      (Work.FTS.Galerkin.muDyn (pExp α) Φ g τ) (Work.FTS.Galerkin.lamDyn (pExp α) Φ g τ)
      (gSlice g τ) z' θ) d z ∧ |d| ≤ NZ
  /-- the right-hand side vanishes at `z = 0` -/
  hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ 0 θ + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ 0 θ = 0
  /-- the right-hand side vanishes at `θ = 0` -/
  hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z 0 + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z 0 = 0
  /-- the right-hand side vanishes at `θ = π/2` -/
  hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z (Real.pi / 2)
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z (Real.pi / 2) = 0

/-- **THE BRIDGE BACK TO THE COMPOSITE INTERFACE.**  The primitive R5 data produce the composite
`R5Slot`; the proof is `Der.R5Slot_of_parts` on the unpacked fields. -/
theorem R5Slot_of_R5Parts {α S : ℝ} {g Φ : Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (H : R5Parts α S g Φ) : ∃ NR : ℝ, R5Slot α S g Φ NR := by
  obtain ⟨NJ, hL, hN₀, hN, hNs⟩ := H.hJ
  obtain ⟨NZ₁, -, hLz⟩ := H.hLz
  obtain ⟨NZ₂, -, hN₀z⟩ := H.hN₀z
  obtain ⟨NZ₃, -, hNz⟩ := H.hNz
  obtain ⟨NZ₄, -, hNsz⟩ := H.hNsz
  exact Der.R5Slot_of_parts hα hα13 hS H.hsol H.h0 hL hN₀ hN hNs H.hmb H.hmbh
    hLz hN₀z hNz hNsz H.hRz0 H.hRθ0 H.hRθπ

end Work.FTS.RegPkgGal
