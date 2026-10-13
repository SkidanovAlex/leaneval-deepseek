import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.zderiv_LGammaT
import Submission.Work.FTS.RegPkgGal.Der.zderiv_N0
import Submission.Work.FTS.RegPkgGal.Der.zderiv_N
import Submission.Work.FTS.RegPkgGal.Der.jet_Nstar
import Submission.Work.FTS.RegPkgGal.Der.zderiv_Nstar
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

/-- **Monotonicity of the `C1Jet`-constant**: weakening the constant is free, both in the `Jet`
and in the `z`-derivative bound.  Needed to feed two `C1Jet`-hypotheses with *different* constants
into a lemma that asks for a common one (the `D_z`-slots of `zderiv_N0`). -/
theorem c1Jet_mono_N {α S M N : ℝ} {h : Work.FTS.RegPkgGal.Fam} (hMN : M ≤ N)
    (H : Work.FTS.RegPkgGal.C1Jet α S M h) : Work.FTS.RegPkgGal.C1Jet α S N h :=
  ⟨jet_mono_N hMN H.1, fun τ hτ θ hθ z hz => by
    obtain ⟨d, hd, hb⟩ := H.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb hMN⟩⟩

theorem R5Parts_of_pieces {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam}
    {N₁ N₂ N₃ N₄ N₅ N₆ N₇ N₈ N₉ N₁₀ N₁₁ N₁₂ N₁₃ N₁₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hg : Work.FTS.RegPkgGal.C1Jet α S N₁ g)
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hF : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hL12g : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.RegPkgGal.C1Jet α S N₈ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0))
    (hL12Fstar : Work.FTS.RegPkgGal.C1Jet α S N₉ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z))
    (hDthFstar : Work.FTS.RegPkgGal.C1Jet α S N₁₀ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ))
    (hDzFstar : Work.FTS.RegPkgGal.C1Jet α S N₁₁ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ))
    (hRop : Work.FTS.RegPkgGal.C1Jet α S N₁₂ (fun z θ τ => Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hUopF : Work.FTS.RegPkgGal.C1Jet α S N₁₃ (fun z θ τ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hVopFK : Work.FTS.RegPkgGal.C1Jet α S N₁₄ (fun z θ τ => Work.Construction.Vop
      (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hFK : Work.FTS.RegPkgGal.C1Jet α S N₁₄ (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z))
    (hNsJet : Work.FTS.Regularity.Jet α S N₁ (fun z θ τ => Work.Construction.Nstar
      (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
      (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
      (Work.FTS.Regularity.gSlice g τ) z θ))
    (hNsZ : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ N₁)
    (hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) (Work.FTS.Regularity.gSlice g τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) (Work.FTS.Regularity.gSlice Φ τ))| ≤ M)
    (hmbh : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) g τ) (Work.FTS.Regularity.gSlice g τ))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) g τ) (Work.FTS.Regularity.gSlice Φ τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) g τ') (Work.FTS.Regularity.gSlice g τ'))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) g τ') (Work.FTS.Regularity.gSlice Φ τ'))|
        ≤ M * |τ - τ'| ^ α)
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    Work.FTS.RegPkgGal.R5Parts α S g Φ := by
  -- The three `N`-side pieces and the `𝓛_Γ^T`-piece as `C1Jet`s, on top of the given `C1Jet` data.
  obtain ⟨NL, hL⟩ := zderiv_LGammaT (α := α) (S := S) (g := g) hα hα13 hS
    hg hDzg hDthg hL12g hL12T
  have hLneg : Work.FTS.RegPkgGal.C1Jet α S NL
      (fun z θ τ => -Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ) :=
    Work.FTS.RegPkgGal.C1Jet.neg hL
  obtain ⟨N0c, hN0⟩ := zderiv_N0 (α := α) (S := S) (g := g) hα hα13 hS
    hF hDthF (c1Jet_mono_N (le_max_left _ _) hDzF) (c1Jet_mono_N (le_max_right _ _) hDzg)
    hL12g hL12Fstar hDthFstar hDzFstar
  obtain ⟨NNc, hN⟩ := zderiv_N (α := α) (S := S) (g := g) (Φ := Φ) hα hα13 hS
    hF hDthF hDzF hRop hUopF hVopFK hFK
  -- The `N_*`-piece: the two given hypotheses *are* its `C1Jet`-data.
  have hNs : Work.FTS.RegPkgGal.C1Jet α S N₁
      (fun z θ τ => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ) := ⟨hNsJet, hNsZ⟩
  refine ⟨hsol, h0, ⟨max (max (max NL N0c) NNc) N₁, ?_, ?_, ?_, ?_⟩,
    hmb, hmbh, ⟨NL, hL.1.1, ?_⟩, ⟨N0c, hN0.1.1, ?_⟩, ⟨NNc, hN.1.1, ?_⟩,
    ⟨N₁, hNsJet.1, hNsZ⟩, hRz0, hRθ0, hRθπ⟩
  · -- `Jet` of `-𝓛_Γ^T`
    exact jet_mono_N
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hLneg.1
  · -- `Jet` of `N₀`
    exact jet_mono_N
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN0.1
  · -- `Jet` of `N`
    exact jet_mono_N (le_trans (le_max_right _ _) (le_max_left _ _)) hN.1
  · -- `Jet` of `N_*`
    exact jet_mono_N (le_max_right _ _) hNsJet
  · -- `z`-differentiability of `-𝓛_Γ^T`
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hL.2 τ hτ θ hθ z hz
    exact ⟨-d, hd.neg, by simpa using hb⟩
  · -- `z`-differentiability of `N₀`
    intro τ hτ θ hθ z hz
    exact hN0.2 τ hτ θ hθ z hz
  · -- `z`-differentiability of `N`
    intro τ hτ θ hθ z hz
    exact hN.2 τ hτ θ hθ z hz

end Work.FTS.RegPkgGal.Der
