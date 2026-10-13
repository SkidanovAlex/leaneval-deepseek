import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.R5Slot
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`

The right-hand side of the fake-time equation,

  `∂_τ g = -𝓛_Γ^T(g) + gRHS(μ̄(τ), λ(τ), F_*+g(τ), Φ(τ), g(τ))`

is the sum of five pieces: the linear term `-𝓛_Γ^T(g)`, the three nonlinear terms `N₀`, `N`, `N_*`
and the coercivity correction `- μ̄(τ)·AK`, where `μ̄(τ) = mubar (N₀(τ)) (N(τ))` is the scalar zero
mode.  This file proves that if each of the four `τ`-families is a `Jet` (bounded and jointly
`α`-Hölder on the strip `[0,S]`) and the scalar `μ̄` is bounded and `α`-Hölder in `τ`, then so is
the whole right-hand side.

The analytic ingredients are `AK α z θ = (Γ(θ)/c)·2z²/(1+z)³` (a function of `(z,θ)` alone, with
both factors bounded and `α`-Hölder) and the `Jet`-closure API; both live in the auxiliary module
`Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux` (`rhsJet_ak_bounds`, `rhsJet_add`, `rhsJet_mul`,
…).
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

theorem rhs_jet_of_parts {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam} {N₁ N₂ N₃ N₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hL : Work.FTS.Regularity.Jet α S N₁
      (fun z θ τ => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ)))
    (hN₀ : Work.FTS.Regularity.Jet α S N₂
      (fun z θ τ => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ))
    (hN : Work.FTS.Regularity.Jet α S N₃
      (fun z θ τ => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z θ))
    (hNs : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Construction.Nstar
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
            (Work.FTS.Regularity.gSlice Φ τ'))| ≤ M * |τ - τ'| ^ α) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := hmb
  obtain ⟨M₂, -, hM₂⟩ := hmbh
  set M := max M₁ M₂ with hMdef
  have hM0 : 0 ≤ M := le_trans hM₁0 (le_max_left M₁ M₂)
  -- the scalar zero mode `μ̄(τ)`, together with its two moduli
  set m : ℝ → ℝ := fun τ => Work.Construction.mubar
      (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ))
      (Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) with hmdef
  have hm : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M := by
    intro τ hτ
    rw [hmdef]
    exact le_trans (hM₁ τ hτ) (le_max_left M₁ M₂)
  have hmh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h := hM₂ τ hτ τ' hτ'
    have hle : M₂ ≤ M := le_max_right M₁ M₂
    calc |m τ - m τ'| ≤ M₂ * |τ - τ'| ^ α := h
      _ ≤ M * |τ - τ'| ^ α := mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (abs_nonneg _) _)
  obtain ⟨hAKbdd, hAKh⟩ := rhsJet_ak_bounds hα hα13
  have hprod : Work.FTS.Regularity.Jet α S (M * 10 + M * 100)
      (fun z θ τ => -(m τ * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)) :=
    rhsJet_neg (rhsJet_mul hα hM0 (by norm_num) (by norm_num) hm hmh hAKbdd hAKh)
  -- the five pieces, added left-to-right: `-𝓛_Γ^T(g) + N₀ + N + N_* + (-μ̄·AK)`
  have hsum : Work.FTS.Regularity.Jet α S (((N₁ + N₂) + N₃ + N₄) + (M * 10 + M * 100))
      (fun z θ τ => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
            (Work.FTS.Regularity.gSlice g τ) z θ)
          + Work.Construction.N0 (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
              (Work.FTS.Regularity.gSlice g τ) z θ
          + Work.Construction.N (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
              (Work.FTS.Regularity.gSlice Φ τ) z θ
          + Work.Construction.Nstar
              (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
              (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
              (Work.FTS.Regularity.gSlice g τ) z θ
          + -(m τ * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)) := by
    have h12 := rhsJet_add hL hN₀
    have h123 := rhsJet_add h12 hN
    have h1234 := rhsJet_add h123 hNs
    exact rhsJet_add h1234 hprod
  refine ⟨((N₁ + N₂) + N₃ + N₄) + (M * 10 + M * 100), ?_⟩
  refine rhsJet_congr (fun z θ τ => ?_) hsum
  simp only [Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS, Work.Construction.gRHS, hmdef]
  rw [show Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ from rfl,
    show Work.FTS.Galerkin.slice Φ τ = Work.FTS.Regularity.gSlice Φ τ from rfl]
  ring_nf

end Work.FTS.RegPkgGal.Der
