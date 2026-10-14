import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB5.Core
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.far_rate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB6

theorem far_rate {αG M L Mf K2 : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hth2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K2)
    (hdec : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) Filter.atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j : ℕ, j ≤ 2 →
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ K * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
  obtain ⟨hL, hF0⟩ := hF.2.2.2.2
  -- the two `θ`-constants: `∂_θ psiP` is bounded by `3M` (SB5 `abs_pth_psiP_le`), and
  -- `∂_θ² psiP` is the hypothesis `hth2`
  set K : ℝ := max (3 * M) K2 with hKdef
  have hK1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K :=
    fun z θ hzθ =>
      (Work.FTS_StreamBdry.SB5.abs_pth_psiP_le hαG h3 hslot z θ hzθ).trans (le_max_left _ _)
  have hK2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K :=
    fun z θ hzθ => (hth2 z θ hzθ).trans (le_max_right _ _)
  -- the core Phragmén–Lindelöf / maximum-principle decay, with the barrier `sb5_barrier_proved`
  have hcore := Work.FTS_StreamBdry.SB5.sb5_decay_core
    (P := Work.FTS.StreamBdryIface.psiP αG Ψ) (F := F) (K := K)
    hαG hL (Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot)
    (Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot) hF0
    (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot) hK1 hK2
    (Work.FTS_StreamBdry.SB5.tendsto_psiP_atTop hαG hsol h3 hslot)
    Work.FTS_StreamBdry.sb5_barrier_proved
  -- the constant of the core decay need not be positive; `max M 1` is, and only increases it
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro z θ hzθ hLz j hj
  have hz : 0 < z := Work.FTS_StreamBdry.Qd_pos hzθ
  have hnn : 0 ≤ Work.Construction.s2 θ * (L / z) ^ (4 / αG) :=
    mul_nonneg (le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hzθ))
      (le_of_lt (Real.rpow_pos_of_pos (div_pos hL hz) _))
  calc |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := hcore z θ hzθ hLz j hj
    _ = M * (Work.Construction.s2 θ * (L / z) ^ (4 / αG)) := by ring
    _ ≤ max M 1 * (Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ = max M 1 * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by ring

end Work.FTS_StreamBdry.SB6
end
-- ===== merged: Submission.Work.FTS_StreamBdry.sb0_psiField_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb0_psiField_proved` — the frozen SB0 producer `StreamBdryIface.sb0_psiField`

The gauge summand of `slice (PsiCan Φs E g) τ` (`SB1′`) and the jump-sheet extension contribute
nothing to `Cyl.psiField` on `Uax` (`x₂ ≠ 0`, `r ≠ 0`): the gauge part gives the potential-flow
profile `κA⁻¹B^{3/p}·sgn(z)/r`, whose `u_r = ∂_z ψ` and `u_z = -ψ/r - ∂_r ψ` both vanish there.
Consequently the firing family `psiFire` and the `U`-slot family `psiHatP` induce the same meridian
velocity field on `Uax` — the replacement for the (false) P3 function equality `merPsi_dict`.

Proved by `Work.FTS_StreamBdry.SB0.sb0_psiField` (with support `sb0_psiFieldAdd`,
`sb0_psiFieldJump`, `sb0_hsm_psiHatP`, `sb0_gauge_alg`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

set_option autoImplicit false

/-- **SB0 proved** (frozen type `sb0_psiField`). -/
theorem sb0_psiField_proved {a : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3
      (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hdec : ∀ τ : ℝ, 0 ≤ τ → ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode (Work.FTS.Regularity.pExp a) z θ)
    (hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.oddPerS
        (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)))
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.Cyl.psiField (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
          (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi a A B
          (Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t) x :=
  Work.FTS_StreamBdry.SB0.sb0_psiField ha hC3 hdec hPsm hB

end Work.FTS_StreamBdry
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.sb2_c2_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb2_c2_proved` — the frozen SB2 producer `StreamBdryIface.sb2_c2`

`oddPerS (psiP αG Ψ)` is `C²` on the strip `Ioi 0 × (-(π/2)-1, π/2+1)`: on the interior pieces it is
`±psiP` composed with `θ ↦ ±θ`, `θ ↦ π - θ` (`SB25.oddPerS_pieces`, `SB3.psiP_c2`), and across the
seams `θ = 0, ±π/2` the gluing lemma `SB25.glue_line_C2` is fed by the edge limits
`SB25.psiP_edge_zero` / `SB25.psiP_edge_axis` (which is where `hdthDV` is used).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd SrcOK psiP oddPerS)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB2 proved** (frozen type `sb2_c2`). -/
theorem sb2_c2_proved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hdthDV : ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') :
    ContDiffOn ℝ 2 (Function.uncurry (oddPerS (psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
  SB2.sb2_c2 hαG hsol h3 hslot hF hdthDV

end Work.FTS_StreamBdry
end
end
