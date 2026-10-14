import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.wlInf_divz_slotsB
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConvLev0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarPzJepsSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- **`F_*(Pz (J_ε W))` is smooth to all orders on `(0,∞)`** — the `fsm` residual of the class-`C`
clause, from the `ℋ¹`-honesty of `W`. -/
theorem FstarPzJepsSmooth {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W)))
      (Set.Ioi 0) := by
  intro m
  -- the mollified angular moment
  have hA : ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W)) (Set.Ioi 0) :=
    FstarJepsSmooth hρ hε hsm hmem m
  -- the angular constant of the bump and the `z`-cut-off
  have hconst : ContDiffOn ℝ m (fun _ : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ) (Set.Ioi 0) :=
    contDiff_const.contDiffOn
  have hB : ContDiffOn ℝ m (fun r : ℝ => Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))
      (Set.Ioi 0) :=
    (Work.FTS.StrongEps.contDiff_zCut m).contDiffOn.mul hconst
  -- the scalar of the projection
  set c : ℝ := Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε W) 0 / Work.FTS.StrongEps.pzNorm
    with hc
  have hBc : ContDiffOn ℝ m (fun r : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)))
      (Set.Ioi 0) := (contDiffOn_const (c := c)).mul hB
  refine (hA.sub hBc).congr ?_
  intro r hr
  have hf : IntegrableOn (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ *
      Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    JepsMulSinCos2Integrable hρ hε hα hsm hmem r hr
  have hcont : Continuous (fun θ : ℝ => Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) :=
    continuous_const.mul ((Work.FTS.StrongEps.contDiff_thCut 0).continuous.mul continuous_sinCos2)
  have hb : IntegrableOn (fun θ : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) Work.Spaces.Iθ :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).const_mul c
  have hkey : ∀ θ : ℝ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ *
        Work.Elliptic.sinCos2 θ
      = Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
        - c * (Work.FTS.StrongEps.zCut r *
            (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) := by
    intro θ
    rw [Work.FTS.StrongEps.Pz_apply]
    simp only [Work.FTS.StrongEps.bump, hc]
    ring
  have hii : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ *
        Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
          - c * (Work.FTS.StrongEps.zCut r *
              (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) :=
    integral_congr_ae (Filter.Eventually.of_forall hkey)
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hii, MeasureTheory.integral_sub hf hb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PieceStarBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two level-six bounds, in the range `α ≤ 1` -/



/-! ## The target -/


end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5.R5PiecesF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# O2 repair: `R5Parts` from PRODUCT elliptic slots (review of fts_velpkg_fix, 2026-10-11)

`Der.R5Parts_of_pieces` asks for closed-`Iθ` `C1Jet`s of `Rop Φ̃` and `Vop Φ̃` ALONE; these jump
at `θ = π/2` unless (★). `N` only contains them multiplied by `F` resp. `D_zF`, which vanish at
the axis (`RegPkgMin.vanish`, `Γ(π/2) = 0`), so the products have no jump. Same conclusion (the
frozen `R5Parts`); no frozen file changes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal.Der

theorem zderiv_N_F {α S : ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.RegPkgGal.C1Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hRopF : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ))
    (hUopF : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hVopDzF : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ τ => Work.Construction.Vop
      (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hFK : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  have hTh : Work.FTS.RegPkgGal.C1Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) :=
    Work.FTS.RegPkgGal.C1Jet.sin_sq hα hα1
  have hT1 : Work.FTS.RegPkgGal.C1Jet α S (|(2:ℝ)| * N₄)
      (fun z θ τ => 2 * (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (2:ℝ))
      hRopF
  have hT2 : Work.FTS.RegPkgGal.C1Jet α S (|(2:ℝ)| * N₅)
      (fun z θ τ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (2:ℝ)) hUopF
  have hT3 : Work.FTS.RegPkgGal.C1Jet α S
      (|2 * Work.FTS.Regularity.pExp α| * N₆)
      (fun z θ τ => 2 * Work.FTS.Regularity.pExp α * (Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 2 * Work.FTS.Regularity.pExp α)
      hVopDzF
  have hT4 : Work.FTS.RegPkgGal.C1Jet α S (|(1/2:ℝ)| * (2 * N₇ * N₂))
      (fun z θ τ => (1/2) * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (1/2:ℝ))
      (Work.FTS.RegPkgGal.C1Jet.mul hFK hDthF)
  have hT5 : Work.FTS.RegPkgGal.C1Jet α S (|(1:ℝ)| * (2 * 4 * (2 * N₇ * N₁)))
      (fun z θ τ => 1 * (Real.sin θ ^ 2 * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := (1:ℝ))
      (Work.FTS.RegPkgGal.C1Jet.mul hTh (Work.FTS.RegPkgGal.C1Jet.mul hFK hF))
  have hcomb := Work.FTS.RegPkgGal.C1Jet.add
    (Work.FTS.RegPkgGal.C1Jet.add
      (Work.FTS.RegPkgGal.C1Jet.add
        (Work.FTS.RegPkgGal.C1Jet.add hT1 (Work.FTS.RegPkgGal.C1Jet.neg hT2))
        (Work.FTS.RegPkgGal.C1Jet.neg hT3))
      (Work.FTS.RegPkgGal.C1Jet.neg hT4))
    (Work.FTS.RegPkgGal.C1Jet.neg hT5)
  exact ⟨_, hcomb.congr (fun z θ τ hz hθ hτ => by
    simp only [Work.Construction.N, Work.Spaces.Dth, Work.Construction.s2]
    ring)⟩


theorem R5Parts_of_pieces_F {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam}
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
    (hRopF : Work.FTS.RegPkgGal.C1Jet α S N₁₂ (fun z θ τ => Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ))
    (hUopF : Work.FTS.RegPkgGal.C1Jet α S N₁₃ (fun z θ τ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hVopDzF : Work.FTS.RegPkgGal.C1Jet α S N₁₄ (fun z θ τ => Work.Construction.Vop
      (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
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
  obtain ⟨NNc, hN⟩ := zderiv_N_F (α := α) (S := S) (g := g) (Φ := Φ) hα hα13 hS
    hF hDthF hRopF hUopF hVopDzF hFK
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
end
