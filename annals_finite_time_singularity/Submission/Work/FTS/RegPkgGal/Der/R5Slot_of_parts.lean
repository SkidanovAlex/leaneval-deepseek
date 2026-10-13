import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R5Slot
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_of_parts
import Submission.Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem R5Slot_of_parts {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam} {NJ NZ₁ NZ₂ NZ₃ NZ₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hL : Work.FTS.Regularity.Jet α S NJ (fun z θ τ => -(Work.Coercivity.LGammaT
      (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice g τ) z θ)))
    (hN₀ : Work.FTS.Regularity.Jet α S NJ (fun z θ τ => Work.Construction.N0
      (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
      (Work.FTS.Regularity.gSlice g τ) z θ))
    (hN : Work.FTS.Regularity.Jet α S NJ (fun z θ τ => Work.Construction.N
      (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
      (Work.FTS.Regularity.gSlice Φ τ) z θ))
    (hNs : Work.FTS.Regularity.Jet α S NJ (fun z θ τ => Work.Construction.Nstar
      (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
      (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
      (Work.FTS.Regularity.gSlice g τ) z θ))
    (hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice g τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ))| ≤ M)
    (hmbh : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice g τ))
          (Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice Φ τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ')
            (Work.FTS.Regularity.gSlice g τ'))
          (Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ')
            (Work.FTS.Regularity.gSlice Φ τ'))| ≤ M * |τ - τ'| ^ α)
    (hLz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => -(Work.Coercivity.LGammaT
        (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice g τ) z' θ)) d z
        ∧ |d| ≤ NZ₁)
    (hN₀z : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ NZ₂)
    (hNz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z' θ) d z ∧ |d| ≤ NZ₃)
    (hNsz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ NZ₄)
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    ∃ NR : ℝ, Work.FTS.RegPkgGal.R5Slot α S g Φ NR := by
  obtain ⟨NR, hRHS⟩ :=
    rhs_jet_of_parts (α := α) (S := S) hα hα13 hS hL hN₀ hN hNs hmb hmbh
  obtain ⟨N₁, hN₁0, hN₁⟩ :=
    rhs_zderiv_of_parts (α := α) (S := S) hα hα13 hS hLz hN₀z hNz hNsz hmb
  exact ⟨NR, hsol, h0, hRHS, ⟨N₁, hN₁0, hN₁⟩, hRz0, hRθ0, hRθπ⟩

end Work.FTS.RegPkgGal.Der
