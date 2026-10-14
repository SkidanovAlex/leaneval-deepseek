import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Sys.FBDefs
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Joint.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §9  Assembly of the `hFjoint` field -/

/-- Joint continuity of the transport right-hand side `K7` on the slab. -/
theorem K7_contOn_slab {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => K7 α Φs E g p.1 p.2.1 p.2.2) (R7Slab S) :=
  Work.FTS_RegExport.RXR7.Support.K7cont hS hα hα13 hOK hVP

/-- Joint continuity of the `z`-coordinate of the `F_*`-part. -/
theorem FstarPz_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          q.1 q.2)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS_RegExport.RXR7.Support.FstarPartCont (α := α)
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) (R7Slab S) :=
    (p1.prod p2).continuous.continuousOn
  exact (h2.comp h3 (fun p hp => ⟨hp.1, hp.2.1.1, hp.2.1.2⟩)).fst

/-- Joint continuity of the `θ`-coordinate of the `F_*`-part. -/
theorem FstarPth_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          q.1 q.2)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS_RegExport.RXR7.Support.FstarPartCont (α := α)
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) (R7Slab S) :=
    (p1.prod p2).continuous.continuousOn
  exact (h2.comp h3 (fun p hp => ⟨hp.1, hp.2.1.1, hp.2.1.2⟩)).snd

/-- Joint continuity of the two spatial coordinates of the `F_*`-part. -/
theorem FstarPart_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1)) (R7Slab S) :=
  (FstarPz_contOn_slab (α := α) (S := S)).prodMk (FstarPth_contOn_slab (α := α) (S := S))

/-- Joint continuity of the candidate derivative field `ProfD` on the slab. -/
theorem ProfD_contOn_slab {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs E g p) (R7Slab S) :=
  ProfD_contOn
    (FPz_contOn hS hα hα13 hOK (FstarPart_contOn_slab (α := α) (S := S)).fst)
    (FPt_contOn hS hα hα13 hOK (FstarPart_contOn_slab (α := α) (S := S)).snd)
    (K7_contOn_slab hS hα hα13 hOK hVP)

/-- The profile is differentiable within the slab everywhere, with derivative `ProfD`. -/
theorem profile_hasFDerivWithinAt {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S)
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Prof α g z θ s) (-(K7 α Φs E g z θ τ)) τ) :
    ∀ x ∈ R7Slab S, HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => Prof α g y.1 y.2.1 y.2.2)
      (ProfD α Φs E g x) (R7Slab S) x := by
  intro x hx
  by_cases hτ : 0 < x.2.2
  · exact (hasFDerivAt_profD_of_pos hS hα hα13 hOK hEq x hx hτ).hasFDerivWithinAt
  · have h0 : x.2.2 = 0 := le_antisymm (not_lt.mp hτ) hx.2.2.1
    exact hasFDerivWithinAt_profD_of_eq_zero hS hα hα13 hOK
      (K7_contOn_slab hS hα hα13 hOK hVP) hEq x hx h0

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.FBDecomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBDecomp` — the algebraic decomposition of `Ẑ`

With `β = pExp α`, `μ = μR α Φs E g`, `Φ̃ = phiTil β (GR α g) (ΦR α Φs E g) σ`,
`F = Ftau β (GR α g) σ` and `Lg = L₁₂(F) - 2β/(1+z)`, `Kg = 𝔽K(F) - β·2z/(1+z)²`, the three
coefficients

  `VR = (1-μ) + L₁₂(F)·c2m + 2β·Vop Φ̃`,
  `bR = 2·Uop Φ / sin 2θ`,
  `cR = (1+μ) - L₁₂(F)/β + sin²θ·𝔽K(F) - 2·Rop Φ̃`

expand, using the `F_* + g̃`-split of `L₁₂`/`𝔽K` (`SysAux.L12_FK_Ftau_split`), the additivity of
`Uop` over `Φ = Φ̃ + Θ(F)` (`SysAux.bR_decomp`) and the closed form of `2·Uop(Θ(F))`
(`SysAux.Theta_ops`), into

  `VR·A1 + bR·B1 + cR·F̂ = E + Lg·α₁ + Kg·α₂ + (2β·Vop Φ̃)·A1 + (2·Uop Φ̃/sin 2θ)·B1 - (2·Rop Φ̃)·F̂`

with `E`, `α₁`, `α₂`, `A1`, `B1`, `F̂` the explicit pieces of `Sys.FBDefs`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The algebraic decomposition of `Ẑ` (`= VR·A1 + bR·B1 + cR·F̂`) into its six explicit
pieces. -/
theorem forcing_decomp {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hL12d : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z
        = -Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z) :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ
      = Ef (Work.FTS.RegExportIface.RXT.μR α Φs E g σ) (Work.FTS.Regularity.pExp α) z θ
        + Work.Construction.L12 (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z * al1f (Work.FTS.Regularity.pExp α) z θ
        + Work.Construction.FK (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z * al2f (Work.FTS.Regularity.pExp α) z θ
        + (2 * Work.FTS.Regularity.pExp α
            * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
          * A1f z θ
        + (2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
            / Real.sin (2 * θ))) * B1f (Work.FTS.Regularity.pExp α) z θ
        + (-2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
          * Fhf z θ := by
  intro σ hσ z θ hz hθ0 hθ1
  have hβpos : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  -- the `F_* + g̃`-split of the two radial transforms
  have hLK := Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split hα hα13 hS hOK hw σ hσ z hz
  have hL := hLK.1
  have hK := hLK.2
  -- the closed form of `2·Uop(Θ(F))`
  obtain ⟨-, hU2, -⟩ := Work.FTS_RegExport.RXT.SysAux.Theta_ops
    (αG := Work.FTS.Regularity.pExp α) hβpos
    (fun z' hz' => hL12d σ hσ z' hz') z θ hz hθ0 hθ1
  -- the additivity of `Uop` over `Φ = Φ̃ + Θ(F)`, from `bR_decomp`
  have hb := Work.FTS_RegExport.RXT.SysAux.bR_decomp hα hα13 hS hOK hC2 hL12 hw σ hσ
    z θ hz hθ0 hθ1
  have hs : Real.sin (2 * θ) ≠ 0 := by
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos]))
  have hbΘ : 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ
        / Real.sin (2 * θ))
      = -(3 / (2 * Work.FTS.Regularity.pExp α)) * Work.Construction.L12 (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z
        + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z / 2 := by
    rw [show 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ
          / Real.sin (2 * θ))
        = (2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ)
          / Real.sin (2 * θ) from by ring]
    rw [hU2]
    field_simp
  simp only [Work.FTS.RegExportIface.RXT.VR, Work.FTS.RegExportIface.RXT.cR,
    Work.FTS.RegExportIface.Vz7, Work.FTS.RegExportIface.cs7,
    Ef, V0f, C0f, b0f, A1f, Fhf, B1f, al1f, al2f]
  rw [hb, hbΘ, hL, hK]
  field_simp
  ring

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FKDeriv` — the `z`-derivatives of the angular moments of `F(τ)`

* `Ftau_slot_le3` — uniform slot bounds of order `≤ 3` for `F_* + slice (gn n) τ`;
* `Qlim_eq_FK` — `FK (F_* + slice (GR α g) τ)(z) = Qlim α g τ 0 z`;
* `Qlim_bound` — `|Qlim k z| ≤ 3(π/2)C_B` for `k ≤ 2`;
* `Qlim_hasDerivAt_1`, `Qlim_hasDerivAt_2` — the first two `z`-derivatives of `Qlim · 0`, by
  passing to the limit in the corresponding derivatives of the approximants
  (`RXR1.hasDerivAt_of_tendsto_deriv`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 Order-`3` slot bounds for the approximants -/

/-- `F_*` is `C^n` on the open quadrant, at every order `n`. -/
theorem Fstar_contDiffOn {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 β n
  have hc : Work.Spaces.c β ≠ 0 := by
    have h := (Work.Spaces.c_bounds β hβ hβ1).1
    intro h0; rw [h0] at h; norm_num at h
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2 / Work.Spaces.c β)
      Work.FTS.EllipticEst.Q0 := hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => β * (Work.Spaces.Gam β p.2 / Work.Spaces.c β))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.ftau_contDiffOn_fst_of
      (Work.FTS_RegExport.RXT.ftau_contDiffOn_FM_Fstar n)
  exact (h2.mul h3).congr (fun _ _ => rfl)


/-! ## §2 `FK` of the limit profile and the bounds on the moments -/

/-- `FK (F_* + slice (GR α g) τ)(z) = Qlim α g τ 0 z`. -/
theorem Qlim_eq_FK {α : ℝ} (hα : 0 < α) {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ) z = Qlim α g τ 0 z := by
  rw [Work.Construction.FK, Qlim]
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ hθ => ?_)
  have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ = g z θ τ :=
    Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) hτ hz hθ.1 hθ.2
  simp only [Work.Spaces.DzIter_zero, Work.FTS.Galerkin.slice_apply,
    Work.Construction.Ftau, hGR]
  ring

/-- **The moments of the limit are bounded by `3(π/2)C_B`** for `k ≤ 2`. -/
theorem Qlim_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    |Qlim α g τ k z| ≤ 3 * (Real.pi / 2) * CB := by
  refine le_of_tendsto ((Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hk hz).abs)
    (Filter.Eventually.of_forall fun n => ?_)
  exact Qapp_bound (α := α) hα hα13 hCB h2 hsl n (by omega) hz


/-! ## §3 The `z`-derivatives of `Qlim · 0` -/

/-- **First derivative.** -/
theorem Qlim_hasDerivAt_1 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qlim α g τ 0) (Qlim α g τ 1 z / z) z := by
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (Qapp α gn τ n 0) (Qapp α gn τ n 1 x / x) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    exact Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 0) (by norm_num) hx0
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => Qapp α gn τ n 1 x / x)
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.div ?_ differentiableOn_id ?_
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1, hz]
      exact ((Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega)
        hx0).differentiableAt).differentiableWithinAt
    · intro x hx
      exact ne_of_gt (by linarith [hx.1, hz] : (0 : ℝ) < x)
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Qapp α gn τ n 1 x / x| ≤ M := by
    refine ⟨3 * (Real.pi / 2) * CB * 2 / z, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h1 : |Qapp α gn τ n 1 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
    have h2' : (1 : ℝ) / x ≤ 2 / z := by
      rw [div_le_div_iff₀ hx0 hz]
      linarith [hx.1]
    rw [abs_div, abs_of_pos hx0]
    calc |Qapp α gn τ n 1 x| / x = |Qapp α gn τ n 1 x| * (1 / x) := by ring
      _ ≤ 3 * (Real.pi / 2) * CB * (2 / z) :=
          mul_le_mul h1 h2' (by positivity) (by positivity)
      _ = 3 * (Real.pi / 2) * CB * 2 / z := by ring
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => Qapp α gn τ n 1 y / y) x| ≤ L := by
    refine ⟨2 * (3 * (Real.pi / 2) * CB) / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hq := (Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega)
      hx0).div (hasDerivAt_id x) (ne_of_gt hx0)
    have hval : deriv (fun y => Qapp α gn τ n 1 y / y) x
        = (Qapp α gn τ n 2 x - Qapp α gn τ n 1 x) / x ^ 2 := by
      have hxne : x ≠ 0 := ne_of_gt hx0
      rw [show deriv (fun y : ℝ => Qapp α gn τ n 1 y / y) x
          = deriv (Qapp α gn τ n 1 / id) x from rfl, hq.deriv]
      simp only [id_eq]
      field_simp [hxne]
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have h2b : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have h1b : |Qapp α gn τ n 1 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
    have hnum : |Qapp α gn τ n 2 x - Qapp α gn τ n 1 x|
        ≤ 2 * (3 * (Real.pi / 2) * CB) := by
      calc |Qapp α gn τ n 2 x - Qapp α gn τ n 1 x|
          = |Qapp α gn τ n 2 x + -Qapp α gn τ n 1 x| := by ring_nf
        _ ≤ |Qapp α gn τ n 2 x| + |-Qapp α gn τ n 1 x| := abs_add_le _ _
        _ = |Qapp α gn τ n 2 x| + |Qapp α gn τ n 1 x| := by rw [abs_neg]
        _ ≤ 2 * (3 * (Real.pi / 2) * CB) := by linarith
    have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
      have h1 : z / 2 ≤ x := hx.1.le
      have h2y : 0 ≤ z / 2 := by linarith [hz]
      nlinarith
    exact div_le_div₀ (by positivity) hnum (by positivity) hxd
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 0 x) Filter.atTop (𝓝 (Qlim α g τ 0 x)) := by
    intro x hx
    exact Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 0) (by norm_num)
      (by linarith [hx.1, hz])
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 1 x / x) Filter.atTop (𝓝 (Qlim α g τ 1 x / x)) := by
    intro x hx
    exact (Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 1) (by norm_num)
      (by linarith [hx.1, hz])).div_const x
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z) (by linarith) hder hvdiff
    hM hL hu hv z ⟨by linarith, by linarith⟩


/-- **Second derivative**: `Qlim · 1` is differentiable with derivative `Qlim · 2 / z`. -/
theorem Qlim_hasDerivAt_2 {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw CB : ℝ} (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Qlim α g τ 1) (Qlim α g τ 2 z / z) z := by
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (Qapp α gn τ n 1) (Qapp α gn τ n 2 x / x) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    exact Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 1) (by omega) hx0
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => Qapp α gn τ n 2 x / x)
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.div ?_ differentiableOn_id ?_
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1, hz]
      exact ((Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega)
        hx0).differentiableAt).differentiableWithinAt
    · intro x hx
      exact ne_of_gt (by linarith [hx.1, hz] : (0 : ℝ) < x)
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Qapp α gn τ n 2 x / x| ≤ M := by
    refine ⟨3 * (Real.pi / 2) * CB * 2 / z, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h1 : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have h2' : (1 : ℝ) / x ≤ 2 / z := by
      rw [div_le_div_iff₀ hx0 hz]
      linarith [hx.1]
    rw [abs_div, abs_of_pos hx0]
    calc |Qapp α gn τ n 2 x| / x = |Qapp α gn τ n 2 x| * (1 / x) := by ring
      _ ≤ 3 * (Real.pi / 2) * CB * (2 / z) :=
          mul_le_mul h1 h2' (by positivity) (by positivity)
      _ = 3 * (Real.pi / 2) * CB * 2 / z := by ring
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => Qapp α gn τ n 2 y / y) x| ≤ L := by
    refine ⟨2 * (3 * (Real.pi / 2) * CB) / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hq := (Qapp_hasDerivAt (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega)
      hx0).div (hasDerivAt_id x) hxne
    have hval : deriv (fun y => Qapp α gn τ n 2 y / y) x
        = (Qapp α gn τ n 3 x - Qapp α gn τ n 2 x) / x ^ 2 := by
      rw [show deriv (fun y : ℝ => Qapp α gn τ n 2 y / y) x
          = deriv (Qapp α gn τ n 2 / id) x from rfl, hq.deriv]
      simp only [id_eq]
      field_simp [hxne]
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have h3b : |Qapp α gn τ n 3 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 3) (by omega) hx0
    have h2b : |Qapp α gn τ n 2 x| ≤ 3 * (Real.pi / 2) * CB :=
      Qapp_bound (α := α) hα hα13 hCB h2 hsl n (k := 2) (by omega) hx0
    have hnum : |Qapp α gn τ n 3 x - Qapp α gn τ n 2 x|
        ≤ 2 * (3 * (Real.pi / 2) * CB) := by
      calc |Qapp α gn τ n 3 x - Qapp α gn τ n 2 x|
          = |Qapp α gn τ n 3 x + -Qapp α gn τ n 2 x| := by ring_nf
        _ ≤ |Qapp α gn τ n 3 x| + |-Qapp α gn τ n 2 x| := abs_add_le _ _
        _ = |Qapp α gn τ n 3 x| + |Qapp α gn τ n 2 x| := by rw [abs_neg]
        _ ≤ 2 * (3 * (Real.pi / 2) * CB) := by linarith
    have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
      have h1 : z / 2 ≤ x := hx.1.le
      have h2y : 0 ≤ z / 2 := by linarith [hz]
      nlinarith
    exact div_le_div₀ (by positivity) hnum (by positivity) hxd
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 1 x) Filter.atTop (𝓝 (Qlim α g τ 1 x)) := by
    intro x hx
    exact Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 1) (by norm_num)
      (by linarith [hx.1, hz])
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Qapp α gn τ n 2 x / x) Filter.atTop (𝓝 (Qlim α g τ 2 x / x)) := by
    intro x hx
    exact (Qapp_tendsto (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet (k := 2) (by norm_num)
      (by linarith [hx.1, hz])).div_const x
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z)
    (by linarith) hder hvdiff hM hL hu hv z ⟨by linarith, by linarith⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.Ftau_datum_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false

/-! ## §1 The `τ`-uniform weighted bound for the slices of `g`

This is `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` with the horizon `max τ 1` moved
*inside* the `∀ τ`: the constant returned there is `Cw₀ · (C₀ α²)` with `Cw₀` from
`RXA1w.abs_mixed_le_HkNorm_C4_w_proved` and `C₀ α²` the class-`C` `ℋ⁴`-bound of the approximants,
neither of which mentions the horizon, so the same proof yields a horizon-free constant. -/
theorem mixed_weighted_unif {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  -- the constant `C₀ αG²` is nonnegative (it dominates `Xn` at any slot of any approximant)
  have hC0sq : 0 ≤ C₀ * αG ^ 2 := by
    obtain ⟨gn, B, L, hC, -, -, -⟩ := hA 1 one_pos
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.FTS.Galerkin.slice (gn 0) 0) :=
      Work.Spaces.HkNorm_nonneg αG 4 _
    exact le_trans hX0 (hC 0 0 ⟨le_rfl, zero_le_one⟩).2.1
  refine ⟨Cw * (C₀ * αG ^ 2), mul_nonneg hCw0 hC0sq, ?_⟩
  intro τ hτ b a hab z θ hz hθ0 hθ1
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ :=
    hA (max τ 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left _ _⟩
  -- the existential constant of `LimApprox` does not depend on `n`: the class-`C` bound
  -- transfers slotwise and the `ℋ⁴`-norm is dominated by `C₀ αG²`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro n
    have hcls : Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) := (hC n τ hτT).1
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hcls.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
    have h1 := hCw _ h4 hmem htr b a hab z θ hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
      (hC n τ hτT).2.1
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * αG ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw0)
      _ = Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  exact le_of_tendsto ((hjet τ hτT b a (by omega) z θ hzθ).abs)
    (Filter.Eventually.of_forall hbound)

/-- **`Ftau_datum_of_LimApprox` with a `τ`-uniform constant.**  This is
`Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox`
(`Submission/Work/FTS_RegExport/RXT/Sys/Ftau_datum_of_LimApprox.lean`) with the horizon removed
(unbounded `τ`, and the `hc2` hypothesis dropped because `DynOK'` supplies it through
`RegPkgMin.c4` for every `τ ≥ 0`).

PROOF ROUTE (read the two files first).  Every ingredient constant of the horizon-local proof is
already horizon-free:
* `RXA2w.lim_mixed_weighted_proved` returns `Cw₀ * (C₀ * (pExp α)^2)` with `Cw₀` from
  `RXA1w.abs_mixed_le_HkNorm_C4_w_proved` — no `T`.  Re-run its proof with the horizon
  `max τ 1` *inside* the `∀ τ` to obtain the `τ`-uniform weighted bound
  `∃ Cw, 0 ≤ Cw ∧ ∀ τ, 0 ≤ τ → ∀ b a, a + b ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π/2 →
     |mixed b a (slice (GR α g) τ) z θ| ≤ Cw * (z^{3/2}/(1+z)^2)`
  (use `ftau_slice_GR_eq` to move between `GR` and `g` on the quadrant, and `hOK.2` for the
  approximants at horizon `max τ 1`, `hOK.1.2` for `Xn ≤ C₀ α²`).
* `DatumBnd`: take it from the *proved, `τ`-uniform* `RXT.Ftau_bounds hα hα13 hOK τ hτ`
  (constant `10*M + |K|`, `K = 10/√(γ-1)·(C₀α²)`), instead of the horizon-local
  `Ftau_jets_bounded_of_LimApprox`.
* `ContDiffOn ℝ 2 (uncurry (Ftau (pExp α) (GR α g) τ)) Q0`: from `contDiffOn_Ftau_Q0 hOK τ hτ`.
* density majorant: `RXT.Sys.abs_L12dens_Fstar_add_le` with `u = slice (GR α g) τ` (note
  `Ftau (pExp α) (GR α g) τ = fun z θ => Fstar (pExp α) z θ + slice (GR α g) τ z θ` is `rfl`);
  integrability and the mass bound from `RXT.Sys.majorant_Ioi_integrable hCw0` via
  `MeasureTheory.Integrable.mono'` and `MeasureTheory.integral_mono_of_nonneg`, the a.e. strong
  measurability coming from continuity of the density on `(0,∞)`
  (`RXT.Sys.continuousAt_Qang_of_bounds` + `L12dens_eq_thetaIntegral`).
The final constant can be `max 1 Cdb + 120 + 18 * Cw` with `Cdb`, `Cw` the uniform constants
above; every step is importable from the existing modules. -/
theorem Ftau_datum_unif {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      Work.FTS_RegExport.RXT.Sys.DatumHyp
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) C := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- §A the two `τ`-uniform constants: weighted slice bounds and the profile jet bounds
  obtain ⟨Cw, hCw0, hCw⟩ := mixed_weighted_unif (αG := Work.FTS.Regularity.pExp α)
    (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hp0 hp1 hOK.2
  obtain ⟨Cdb, -, hCdb⟩ := Ftau_bounds_unif hα hα13 hOK
  refine ⟨max 1 Cdb + 120 + 18 * Cw, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
    have h2 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
    linarith
  · -- §B the weighted bound for the `GR`-slice, uniformly in `τ`
    have huAll : ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      intro τ' hτ' z θ hz h1 h2
      rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ' hz h1.le h2.le]
      exact hCw τ' hτ' 0 0 (by norm_num) z θ hz h1 h2
    -- the `C²`-regularity of `F(τ)` on the open quadrant, uniformly in `τ`
    have hFcAll : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
      intro τ hτ
      have hGRc : ContDiffOn ℝ 2
          (Function.uncurry (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS_RegExport.RXT.ftau_contDiffOn_slice_GR_Q0 hOK τ hτ
      have h1 : ContDiffOn ℝ 2
          (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
          Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
      have h2 := h1.add hGRc
      refine h2.congr (fun p _ => ?_)
      simp only [Function.uncurry, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    intro τ hτ
    -- §C the `L¹`-density: integrability and the mass bound
    obtain ⟨hint, hbnd⟩ := L12dens_mass_unif hα hα13 hCw0 (g := g) huAll
      (fun τ' hτ' => (hFcAll τ' hτ').continuousOn) τ hτ
    -- §D the pointwise jet bounds of `F(τ)`, with the single constant `max 1 Cdb + 120 + 18 Cw`
    have hCdb_le : Cdb ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h0 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
      have h1 : Cdb ≤ max 1 Cdb := le_max_right _ _
      linarith
    have hDbnd : Work.FTS_RegExport.RXT.Sys.DatumBnd (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)
        (max 1 Cdb + 120 + 18 * Cw) := by
      intro z θ hz h1 h2
      obtain ⟨a1, a2, a3⟩ := hCdb τ hτ z θ hz h1 h2
      exact ⟨le_trans a1 hCdb_le, le_trans a2 hCdb_le, le_trans a3 hCdb_le⟩
    have hbnd' : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
        ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
      linarith
    exact ⟨hFcAll τ hτ, hDbnd, hint, hbnd'⟩

end Work.FTS_RegExport.RXVP3
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.velVanish2_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)

/-- **`velVanish2` with a `τ`-uniform constant.**  This is `Work.FTS_RegExport.RXT.velVanish2`
(`Submission/Work/FTS_RegExport/RXT/velVanish2.lean`) with the quantifier
`∀ S > 0, ∃ M, ∀ τ ∈ Icc 0 S` replaced by `∃ M, ∀ τ, 0 ≤ τ →`.

PROOF ROUTE (read the two files first).  `RXT/velVanish2.lean` splits
`Φ̃ = Φ̃_* + Φ̃_pert` (`v2_phiTil_split`) and combines the star bounds (`v2_starRop_mixed`,
`starVop`, `v2_starUop` — all `τ`-free already) with `v2_velPert` (which is horizon-local but whose
witness `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))` does **not** contain `S`).  So the uniform
statement follows by re-running the `v2_velPert` proof
(`Submission/Work/FTS_RegExport/RXT/Slots/v2_velPert.lean`, whose five helper lemmas
`velPert_FK_eq`, `velPert_continuousOn_K`, `velPert_contDiffOn_Theta`, `velPert_mixed_sub_three`,
`velPert_hkMem_bound`, `velPert_limit_bound` are public in namespace `Work.FTS_RegExport.RXT`)
with the horizon chosen *inside* the `∀ τ`: for each `τ ≥ 0` instantiate
`hOK.2 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))` to get the class-`C`
approximants `gn` with `Xn α (slice (gn n) τ) ≤ C₀ α²` and the order-≤4 jet convergence
`hJet τ ⟨hτ, le_max_left τ 1⟩`, then take the liminf slotwise with
`velPert_limit_bound` at the constant `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))`
(`C4` from `velPert_hkMem_bound`) and the three slot-jet convergences
(`RXT.Slots.v2_SlotJetsTendsto`, `v2_L12DzIterTendsto`, `v2_thetaJetsTendsto`,
`v2_paramC2`, `contDiffOn_three_L12`, `contDiffOn_slice_PhiR_Q0` for the `E`-jets of the
limit slice via `hEL3`).  `hSol` and `hdat` are not needed for the perturbation half; `hμ` only
enters the star half (which is `τ`-free). -/
theorem velVanish2_unif {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
    ∃ M : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
          Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)} :
            Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the star half (already `τ`-free)
  have hStarR := Work.FTS_RegExport.RXT.v2_starRop_mixed hαG hαG1 hStar
  obtain ⟨CV, hCV0, hCV⟩ := Work.FTS_RegExport.RXT.starVop hαG hαG1 hStar
  obtain ⟨CU, hCU0, hCU⟩ := Work.FTS_RegExport.RXT.Slots.v2_starUop hαG hαG1 hStar
  -- the perturbation half, with a `τ`-uniform constant
  obtain ⟨MP, hMP⟩ := velPert_unif (Φs := Φs) (E := E) hα hα13 hEll hEL3 hSol hOK
  refine ⟨2 * 10 ^ 4 * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP, ?_⟩
  intro τ hτ z θ hz hθ hθ2 Q hQ j i hji
  -- the common infrastructure
  set CR : ℝ := 2 * 10 ^ 4 * (max Cs 1 * Work.FTS.Regularity.pExp α) with hCRdef
  have hQmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- the pointwise split of the stream functions on the quadrant
  have hsplit : ∀ z₁ θ₁ : ℝ, (z₁, θ₁) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ z₁ θ₁
        = Work.FTS_RegExport.RXT.v2_PhiStar α Φs z₁ θ₁
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ z₁ θ₁ :=
    fun z₁ θ₁ hp => Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp
  have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => hsplit z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  -- `C³` of the full and of the star residual, hence of the perturbation residual
  have hPhi3 : ContDiffOn ℝ 3
      (Function.uncurry (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
      hEL3 hStar hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
    obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hC z₁ θ₁ hz₁ hθ₁ hθ₁2).1, (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1,
        (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hL12 : ContDiffOn ℝ 3
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta
      (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
        (1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (Real.contDiff_sin.comp
        (contDiff_const.mul contDiff_snd)).contDiffOn
    have h2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) p.1) Work.FTS.EllipticEst.Q0 :=
      hL12.comp contDiffOn_fst (fun p hp => hp.1)
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  have hFull3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 := hPhi3.sub hTheta3
  have hStar3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hPert3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (hFull3.sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [hsplit z₁ θ₁ hp]
  have hStarC1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
    hStar3.of_le (by norm_num)
  have hPertC1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) Work.FTS.EllipticEst.Q0 :=
    hPert3.of_le (by norm_num)
  have hstarR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁| ≤ CR * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => by
      rw [hCRdef]
      exact hStarR j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hstarV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁|
        ≤ (CV * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCV j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hstarU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁|
        ≤ (CU * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCU j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hpertR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inl rfl) j i hji
  have hpertV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inr (Or.inl rfl)) j i hji
  have hpertU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inr (Or.inr rfl)) j i hji
  have hSC2R : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.NonlinRows.RopW_Rop (α := Work.FTS.Regularity.pExp α)
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1).of_le
        (by simp [Work.Stability.smoothOrder])
  have hSC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hSC2U : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.2.2.1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hPC2R : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hPert3
  have hPC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hPert3
  have hPC2U : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
      (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := Work.FTS.Regularity.pExp α) hPert3)
  have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hC0 : (0 : ℝ) ≤ CR := by
    rw [hCRdef]; positivity
  have harith : ∀ M₀ : ℝ,
      M₀ ≤ CR + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
        + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP →
      M₀ * min z 1 ≤ (CR + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
        + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) * min z 1 :=
    fun M₀ hM₀ => mul_le_mul_of_nonneg_right hM₀ hmm
  have hCVa : 0 ≤ CV * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCV0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have hCUa : 0 ≤ CU * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCU0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  -- the three cases
  have hQ' : Q = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      ∨ Q = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      ∨ Q = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) := by
    have h := hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  rcases hQ' with hQ | hQ | hQ
  · -- the `ℛ`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotR]
      rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (h := hsplitFun) (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_rop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2R hPC2R
      hstarR hpertR j i hji z θ hz hθ hθ2
    exact le_trans hres (harith (CR + MP) (by linarith [hCVa, hCUa]))
  · -- the `𝒱`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotV]
      rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun)
        (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_vop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2V hPC2V
      hstarV hpertV j i hji z θ hz hθ hθ2
    exact le_trans hres
      (harith (CV * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) (by linarith [hCUa]))
  · -- the `𝒰/sin 2θ`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotU]
      rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (h := hsplitFun) (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_uop_div_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2U hPC2U
      hstarU hpertU j i hji z θ hz hθ hθ2
    exact le_trans hres
      (harith (CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) (by linarith [hCVa]))

end Work.FTS_RegExport.RXVP3
end
end
