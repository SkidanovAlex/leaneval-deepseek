import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS.StrongPersist.H6Rows.MismatchSummand
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Sys.vop_pert_pth_bd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd` — the `∂_θ`-slot of `𝒱(Φ̃(τ))` is bounded

For the modulated residual `Φ̃(τ) = v2_PhiT α Φs E g τ` of the RX-export interface, the
`θ`-derivative of the transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is bounded on the open
quadrant uniformly in `τ ∈ [0,S]`.

## Route

`v2_phiTil_split` (in `velVanish2Aux`) decomposes `Φ̃(τ) = Φ̃_* + Φ̃_pert` on the open quadrant
`Q0`, where `Φ̃_* = PhiTil (F_*) Φs` is the star residual and `Φ̃_pert = PhiTil (g(τ)) (E(g(τ)))`
is the perturbation residual.  Both pieces are smooth enough on `Q0` (`SmoothOpen Φ̃_*` from
`StarPkgo2`, `C³` for `Φ̃_pert` from `Sys.pert_tilde_contDiffOn`), so `∂_θ ∘ 𝒱` splits over the
sum (`pth_vop_add_of_split` below, built from the additivity of `pth`/`Vop` on `Q0`).

Each half is then priced by the *flat coefficient norm* `CoefTh` of `EllPkgGo`/`StarPkgo`:

* the star half `|∂_θ 𝒱(Φ̃_*)| ≤ Cs·α` is literally the `Vth` field of `StarPkgo2` read at
  order `0` (`abs_pth_le_coefTh`);
* the perturbation half `|∂_θ 𝒱(Φ̃_pert)| ≤ max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)` is
  `Sys.vop_pert_pth_bd`, which prices the class-`C` approximants of `LimApprox` with the `Vth`
  field of `EllPkgGo` (and the uniform bound `Xn (g(τ)) ≤ C₀α²` of `DynOK'`) and passes to the
  limit along the jet convergence.

The two halves are added, giving `M = |Cs·α| + max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

set_option linter.unusedVariables false

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-! ## §1 The split of `∂_θ(𝒱 ·)` over a pointwise sum on the open quadrant -/

/-- The `θ`-derivative of `Vop Ψ` splits over a pointwise decomposition `Ψ = Ψ₁ + Ψ₂` of the
datum on the open quadrant, as soon as the two pieces are smooth enough (`Ψ₁` of class `C^∞`,
`Ψ₂` of class `C²`): both `pth` and `Vop` are additive on `Q0` for such data. -/
theorem pth_vop_add_of_split {Ψ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen Ψ₁)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0)
    (hsplit : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Ψ z θ = Ψ₁ z θ + Ψ₂ z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Construction.Vop Ψ) z θ
        = Work.Spaces.pth (Work.Construction.Vop Ψ₁) z θ
          + Work.Spaces.pth (Work.Construction.Vop Ψ₂) z θ := by
  intro z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- additivity of `Vop` on the quadrant
  have hsum : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Vop Ψ z' θ'
        = Work.Construction.Vop Ψ₁ z' θ' + Work.Construction.Vop Ψ₂ z' θ' := by
    intro z' θ' hz' hθ' hθ'2
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩
    have h1c : ContDiffOn ℝ 1 (Function.uncurry Ψ₁) Work.FTS.EllipticEst.Q0 := h₁.forall 1
    have h2c : ContDiffOn ℝ 1 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0 :=
      h₂.of_le (by norm_num)
    calc Work.Construction.Vop Ψ z' θ'
        = Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hsplit z' θ' hz' hθ' hθ'2
      _ = Work.Construction.Vop Ψ₁ z' θ' + Work.Construction.Vop Ψ₂ z' θ' :=
          Work.FTS_RegExport.RXT.v2_vop_add_at h1c h2c hzθ'
  -- `pth` only sees the quadrant
  have hcongr : Work.Spaces.pth (Work.Construction.Vop Ψ) z θ
      = Work.Spaces.pth (fun z θ =>
          Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ) z θ :=
    Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hsum z θ hz hθ hθ2
  -- additivity of `pth` on the two `Vop`-pieces
  have hV1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ₁))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.NonlinRows.smoothOpen_Vop h₁).forall 1
  have hV2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ₂))
      Work.FTS.EllipticEst.Q0 := by
    have hp : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth Ψ₂))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0
        (h₂.of_le (by norm_num))
    have htan : ContDiffOn ℝ 1 (Function.uncurry (fun z θ : ℝ => Real.tan θ * Ψ₂ z θ))
        Work.FTS.EllipticEst.Q0 := by
      have h1 : ContDiffOn ℝ 1 (Function.uncurry (fun _ : ℝ => fun (θ : ℝ) => Real.tan θ))
          Work.FTS.EllipticEst.Q0 := (Work.FTS.NonlinRows.smoothOpen_tan).forall 1
      have h2 : ContDiffOn ℝ 1 (Function.uncurry Ψ₂) Work.FTS.EllipticEst.Q0 :=
        h₂.of_le (by norm_num)
      refine (h1.mul h2).congr (f₁ := Function.uncurry (fun _ : ℝ => fun (θ : ℝ) => Real.tan θ)
        * Function.uncurry Ψ₂) ?_
      intro p _
      rcases p with ⟨z', θ'⟩
      simp only [Function.uncurry, Pi.mul_apply]
    have hsame : Function.uncurry (Work.Construction.Vop Ψ₂)
        = (Function.uncurry (Work.Spaces.pth Ψ₂))
          - (Function.uncurry (fun z θ : ℝ => Real.tan θ * Ψ₂ z θ)) := by
      funext p
      rcases p with ⟨z', θ'⟩
      simp only [Function.uncurry, Work.Construction.Vop, Pi.sub_apply]
    rw [hsame]
    exact hp.sub htan
  exact hcongr.trans (Work.FTS_RegExport.RXT.v2_pth_add_at hV1 hV2 hzθ)

/-! ## §2 The target -/

theorem pth_vop_slot_bd {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) z θ| ≤ M := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  intro S hS
  refine ⟨|Cs * Work.FTS.Regularity.pExp α|
    + max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
      * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2), ?_, ?_⟩
  · refine add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _) ?_) ?_)
    · exact Real.rpow_nonneg (le_of_lt hαG) _
    · exact mul_nonneg (le_max_right _ _) (sq_nonneg _)
  · intro τ hτ z θ hz hθ hθ2
    -- the star half: the `Vth` field of `StarPkgo2` read at order `0`
    have hstar : |Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ| ≤ |Cs * Work.FTS.Regularity.pExp α| := by
      have h1 : |Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
          Φs)) z θ| ≤ Cs * Work.FTS.Regularity.pExp α :=
        (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh hStar.Vth.1 z θ hz hθ hθ2).trans
          hStar.Vth.2
      simpa only [Work.FTS_RegExport.RXT.v2_PhiStar] using h1.trans (le_abs_self _)
    -- the perturbation half: `Sys.vop_pert_pth_bd`
    have hpert : |Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ|
        ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      simpa only [Work.FTS_RegExport.RXT.v2_PhiPert] using
        vop_pert_pth_bd (α := α) (Ce := Ce) (C₀ := C₀) hα hα13 hEll hEL3 hOK S hS τ hτ
          z θ hz hθ hθ2
    -- the split of `∂_θ(Vop ·)` over `Φ̃ = Φ̃_* + Φ̃_pert` on the open quadrant
    have hsplit : Work.Spaces.pth (Work.Construction.Vop
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)) z θ
        = Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ
          + Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ := by
      refine pth_vop_add_of_split (Ψ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Ψ₁ := Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
        (Ψ₂ := Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) ?_ ?_ ?_ z θ hz hθ hθ2
      · exact Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hαG hαG1 hStar
      · exact (pert_tilde_contDiffOn (α := α) (C₀ := C₀) hα hα13 hEL3 hOK τ hτ.1).of_le
          (by norm_num)
      · intro z' θ' hz' hθ' hθ'2
        exact Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ.1 z' θ'
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩)
    calc |Work.Spaces.pth (fun z θ => Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) z θ|
        = |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)) z θ| := rfl
      _ = |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ
          + Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ| := by rw [hsplit]
      _ ≤ |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z θ|
          + |Work.Spaces.pth (Work.Construction.Vop
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z θ| := abs_add_le _ _
      _ ≤ |Cs * Work.FTS.Regularity.pExp α|
          + max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
            * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := add_le_add hstar hpert

end Work.FTS_RegExport.RXT.Sys
