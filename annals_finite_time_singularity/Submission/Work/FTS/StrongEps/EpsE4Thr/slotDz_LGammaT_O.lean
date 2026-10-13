/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/slotDz_LGammaT_O.lean` — the `D_z`-slot of the
level-one coercivity of `𝓛_Γ^T` in the **open** class

The open-class (`CoerAdmO`, i.e. `SmoothOpen` — `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`
— instead of the frozen `SmoothQuad`, `C^∞` on the strip `z > -1`) twin of
`Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT`.  This is precisely the hypothesis `hP` of
`Work.FTS.StrongEps.EpsE4Thr.ledger_O`, i.e. one of the four slot estimates assembled into the
open-class level-one coercivity of `𝓛_Γ^T` (the open interface `UnifIPO.coer`).

The frozen proof runs on

* the pointwise decomposition `D_z(𝓛_Γ^T f) = D_z(𝓛̂ f) + Z₃ + Z₄ + Z₇`,
* the coercivity of the clean operator on the `D_z`-slot, `Coer1.est_A`, and
* the nonlocal-deflection bound `Zrest_pairing_ge_Q`, which needs `(C₀ f)² ≤ 64 Ef f`.

Its open-class inputs — supplied by the sibling files of `OClass/` — are

* `OClass.est_A_O` (the open twin of `Coer1.est_A`, from `IntPkgO` and `RegQo α 2`),
* `OClass.C0_sq_le_Ef_O` (the open twin of `Coer1T.C0_sq_le_Ef_Q`),
* `OClass.Zrest_pairing_ge_O` (the open twin of `Coer1T.Zrest_pairing_ge_Q`), and
* `OClass.Dz_LGammaT_eq_Lhat_add_Zrest_O` (the pointwise decomposition above, on `SmoothOpen`).

The assembly itself is the frozen one (`Coer1T/slotDz_LGammaT.lean`, the final theorem), with
`IntPkg_Q` replaced by the hypothesis `hIP : IntPkgO α f` and `SmoothQuad` by `SmoothOpen`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_A_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_Ef_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Zrest_pairing_ge_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dz_LGammaT_eq_Lhat_add_Zrest_O
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.thetaDerivative
import Submission.Work.Coercivity.wip_Aop_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem slotDz_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) :
    (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
  have hα1' : α ≤ 1 := by linarith
  have hα4 : α ≤ 1 / 4 := by linarith
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_mono (by norm_num) hf.1
  -- ## the two estimates
  have hC0 := OClass.C0_sq_le_Ef_O α hα hα1' hso hf2 hIP
  obtain ⟨hS2_int, hS_bound, hpair_int, hpair_lb⟩ :=
    OClass.Zrest_pairing_ge_O α hα hα1 hso hf2 hIP hHH hC0
  have hA' : (47 / 100) * Work.Coercivity.EDz f
      - (Work.Coercivity.EfEta f + 4 * Work.Coercivity.EDth α f
        + (1 / 8) * Work.Coercivity.EDz f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
    have h := OClass.est_A_O α hα hα4 hf2 hIP
    rwa [← Work.FTS.CoercivityFix.Coer1.EDz_eq_En,
      ← Work.FTS.CoercivityFix.Coer1.EfEta_eq_En,
      ← Work.FTS.CoercivityFix.Coer1.EDth_eq_En α f] at h
  -- ## integrability of the `𝓛̂`-pairing
  have hDzLhat_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hsum := hIP.intLhat_Dz_eta.add hIP.intE2hat_Dz_eta
    refine hsum.congr ?_
    have hμ : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.iz_prod_restrict.symm
    rw [hμ]
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    obtain ⟨z, θ⟩ := p
    have hkey : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.E2hat f z θ :=
      Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open
        (V := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) (isOpen_Ioi.prod isOpen_Ioo)
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) from hso)
        ⟨hp1, hp2⟩ hp1
    simp only [Pi.add_apply, Function.uncurry_apply_pair]
    rw [hkey]
    ring
  -- ## the a.e. pointwise decomposition and the splitting of the pairing
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    have h := OClass.Dz_LGammaT_eq_Lhat_add_Zrest_O α hα hα1 hso hHH z θ hz hθ
    rw [h]
    ring
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      hDzLhat_int hpair_int
  -- ## nonnegativity of the energies
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDz_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e4 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hsplit' : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := hsplit
  rw [hsplit']
  nlinarith [hA', hpair_lb, e1, e2, e3, e4]

end Work.FTS.StrongEps.EpsE4Thr
