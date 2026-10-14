import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.orthSourceHkNormClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.Galerkin (Fn)

theorem orthSourceHkNormClassC (k : ℕ) (hk7 : k ≤ 7) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 → Work.FTS.EllSol.ClassC α g →
      Work.Spaces.HkNorm α k (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α k g := by
  obtain ⟨Cf, hCfpos, hCf⟩ := Work.FTS.EllipticEst.Fstar_Hk_le_open k
  refine ⟨Real.sqrt 2 * (1 + (15 / 4) * Cf), ?_, ?_⟩
  · have h2 : (0 : ℝ) < 1 + (15 / 4) * Cf := by
      have := mul_pos (by norm_num : (0 : ℝ) < 15 / 4) hCfpos
      linarith
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h2
  · intro α g hα hα1 hg
    have hgsm : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
    have hgraw : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hgsm
    have hmem : Work.Spaces.HkMem α k g :=
      Work.FTS.EllipticEst.TT.HkMem_descend_open hk7 hgraw hg.mem
    have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hg.fsm
    have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    have hPHIsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hFsm hsin
    have hPHIraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hPHIsm
    have hPHImem : Work.Spaces.HkMem α k
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      have h :=
        Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α k g hα hα1 hgsm hmem
      simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
    have hSsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      hPHIsm.const_mul' (-(15 / 4))
    have hSraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry
          (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSsm
    have hSmem : Work.Spaces.HkMem α k
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hPHImem
    have horth : Work.Elliptic.orthSource g
        = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Elliptic.orthSource]
      ring
    have hsum := Work.FTS.EllipticEst.HkNorm_add_le α k hgraw hSraw hmem hSmem
    have hcm := Work.FTS.EllipticEst.HkNorm_const_mul α k (-(15 / 4)) hPHIraw
    have hPhi := hCf α g hα hα1 hgraw hmem
    rw [horth]
    calc Work.Spaces.HkNorm α k
          (fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + Work.Spaces.HkNorm α k
              (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))) :=
          hsum
      _ = Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + (15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
          rw [hcm, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4)]
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + (15 / 4) * (Cf * Work.Spaces.HkNorm α k g)) := by
          have h1 : (15 / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))
              ≤ (15 / 4) * (Cf * Work.Spaces.HkNorm α k g) :=
            mul_le_mul_of_nonneg_left hPhi (by norm_num)
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (1 + (15 / 4) * Cf) * Work.Spaces.HkNorm α k g := by ring

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.RegQoClosure =====
section

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
set_option linter.unusedVariables false

/-! ## `BdryTraces` and `SmoothOpen` for the pieces of a difference -/



/-! ## The closure of `RegQo` -/





end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMulHkSqSliceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fkMulHkSqSliceLe` — the level-six integrand of `(FK f) · f`, integrated over `θ`

The radial factor `z ↦ FK f z` multiplies the datum `f`, and the level-six weighted integrand of
the product is dominated at each *point* `(z,θ)` of the open quadrant by the matched radial sum
`∑_{b ≤ 6} (D_z^b (FK f)(z))² · HkIntegrand α (6-b) f z θ` (`radialMatchedMajorant`, proved in
this directory).  Here the pointwise domination is *integrated* over `θ ∈ Iθ`, the finite sum is
interchanged with the `θ`-integral, and the result is turned into an a.e.-in-`z` statement in the
shape in which the consumers (`fkPsi6TermBound`, `fkMulHkSqLe`) use it.

The three ingredients are all available in the tree:

* `radialMatchedMajorant` — the pointwise matched majorant (constant valid for every `α`);
* the two Leibniz rules `leibniz_rad_Dz_cd6`, `leibniz_rad_mixed_cd6`, whose hypotheses are
  `ContDiffOn ℝ 6` of the uncurried radial factor (`contDiffOn6_FK`, from `DatData` and the
  `ℋ⁷`-honesty of the datum) and of the datum (`SmoothOpen.forall`);
* `HkMem_of_le` (`T5bPrep`) to descend the `ℋ⁶`-honesty of the datum to the matched levels
  `6 - b`, giving the `θ`-integrability of every summand.

The passage from "for every `z > 0`" to "for a.e. `z ∈ Iz`" costs the single point `z = 0`, which
is a null set for `volume.restrict Iz`.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary helpers

The `ℋ⁶`-energy of a function is the square of its `ℋ⁶`-norm (`HkNorm` is *defined* as the
square root of `HkSq`), so a bound on the norm squares into a bound on the energy.  The three
`rpow` facts are the small arithmetic of `α ∈ (0,1]` used to convert the `α`-powers of the
three product estimates (`α^{-1/2}·α ≤ 1`, `(α^{-1})² = α^{-2}`, `1 ≤ α^{-2}`) into the single
factor `α^{-2}` of the statement. -/

private theorem HkSq_eq_norm_sq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k g = (Work.Spaces.HkNorm α k g) ^ 2 :=
  (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k g)).symm

private theorem rpow_neg_half_mul_le_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα0, show (-(1 / 2 : ℝ)) + 1 = (1 / 2 : ℝ) by norm_num]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  simpa [Real.rpow_one] using h1

private theorem rpow_neg_one_sq {α : ℝ} (hα0 : 0 < α) :
    (α ^ (-(1 : ℝ))) ^ 2 = α ^ (-(2 : ℝ)) := by
  rw [pow_two, ← Real.rpow_add hα0]
  norm_num

private theorem one_le_rpow_neg_two {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    1 ≤ α ^ (-(2 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(1 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (α ^ (-(1 : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le_one h1 2
    _ = α ^ (-(2 : ℝ)) := rpow_neg_one_sq hα0

/-! ## The four pieces -/

theorem fkStarPieces : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 6 f) ∧
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f ∧
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f ∧
      Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
            * Work.Construction.Fstar α z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
  -- the four universal constants
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
  obtain ⟨Cmul, hCmulpos, hmul⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_WlInf6_cd6'
  obtain ⟨CF, hCFpos, hFsW⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨Css, hCsspos, hFSS⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
  have hAnn : 0 ≤ A := hApos.le
  have hCmulnn : 0 ≤ Cmul := hCmulpos.le
  have hCFnn : 0 ≤ CF := hCFpos.le
  have hCssnn : 0 ≤ Css := hCsspos.le
  refine ⟨1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2, by positivity, ?_⟩
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- `FK f` is `C⁶` on the open quadrant and lies in `ℋ⁶`
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
    have h6 : ContDiffOn ℝ 6 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
      have hF : ContDiffOn ℝ 6 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) :=
        Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm hmem7
          (by norm_num)
      rw [Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f]
      have h3 : ContDiffOn ℝ 6 (fun z => (3 : ℝ) • Work.Elliptic.Fstar f z)
          (Set.Ioi (0 : ℝ)) := hF.const_smul (3 : ℝ)
      simpa only [Pi.smul_apply, smul_eq_mul] using h3
    exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_radial h6
  have hFKmem : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α hα f hsm hmem6
  -- the norm bound for `FK f`
  have hKfbd : Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
      ≤ A * Work.Spaces.HkNorm α 6 f := hA α hα0 hα1 f hsm hmem6
  have hKfnn : 0 ≤ Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.Spaces.HkNorm_nonneg α 6 _
  -- the constant comparisons
  have hAleC : A ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Cmul * CF * A), sq_nonneg (Css * A)]
  have hC2leC : (Cmul * CF * A) ^ 2 ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Css * A)]
  have hC3leC : (Css * A) ^ 2 ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Cmul * CF * A)]
  -- the norm bound for the `F_* · FK f` product
  have hFstarcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).forall 6
  have hstep2 : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)
      ≤ Cmul * CF * A * Work.Spaces.HkNorm α 6 f := by
    obtain ⟨-, hbd2⟩ := hmul α (Work.Construction.Fstar α)
      (fun z (_ : ℝ) => Work.Construction.FK f z) hα0 hα1 hFstarcd
      (hFsW α hα0 hα1).1 hFKcd hFKmem
    have hx : 0 ≤ Cmul * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCmulnn (Real.rpow_nonneg hα0.le _)
    refine le_trans hbd2 ?_
    calc Cmul * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 (Work.Construction.Fstar α)
          * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (CF * α) * (A * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hFsW α hα0 hα1).2 hx) hKfbd
            (Work.Spaces.HkNorm_nonneg α 6 _) ?_
          positivity
      _ = Cmul * CF * A * (α ^ (-(1 / 2 : ℝ)) * α) * Work.Spaces.HkNorm α 6 f := by ring
      _ ≤ Cmul * CF * A * 1 * Work.Spaces.HkNorm α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg α 6 f)
          refine mul_le_mul_of_nonneg_left (rpow_neg_half_mul_le_one hα0 hα1) ?_
          positivity
      _ = Cmul * CF * A * Work.Spaces.HkNorm α 6 f := by ring
  -- ============ conjunct 1 ============
  have hconj1 : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    refine le_trans hKfbd ?_
    simpa only [Work.Spaces.HkNorm] using
      mul_le_mul_of_nonneg_right hAleC (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ============ conjunct 2 ============
  have hconj2 : Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    have hsq : Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
        = (Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)) ^ 2 := by
      rw [Work.FTS.GalBasis.HkSq_congr_all (fun z θ => mul_comm _ _) α 6]
      exact HkSq_eq_norm_sq α 6 _
    rw [hsq]
    calc (Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)) ^ 2
        ≤ (Cmul * CF * A * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep2 2
      _ = (Cmul * CF * A) ^ 2 * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
      _ ≤ (Cmul * CF * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          calc (Cmul * CF * A) ^ 2 = (Cmul * CF * A) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (Cmul * CF * A) ^ 2 * α ^ (-(2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (one_le_rpow_neg_two hα0 hα1) (sq_nonneg _)
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC2leC (Real.rpow_nonneg hα0.le _)
  -- ============ conjunct 3 ============
  have hconj3 : Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    obtain ⟨⟨-, -, hbd3⟩, -⟩ := hFSS (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 hKfnn hsm hmem6 hFKcd hFKmem le_rfl
    have hstep : Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.FK f z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
      refine le_trans hbd3 ?_
      calc Css * α ^ (-(1 : ℝ))
            * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
          ≤ Css * α ^ (-(1 : ℝ)) * (A * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left hKfbd ?_
            exact mul_nonneg hCssnn (Real.rpow_nonneg hα0.le _)
        _ = Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by ring
    rw [HkSq_eq_norm_sq]
    calc (Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.FK f z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ^ 2
        ≤ (Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep 2
      _ = (Css * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f), rpow_neg_one_sq hα0]
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC3leC (Real.rpow_nonneg hα0.le _)
  -- ============ conjunct 4 ============
  have hconj4 : Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Construction.Fstar α z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    obtain ⟨-, ⟨-, -, hbd4⟩⟩ := hFSS (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 hKfnn hsm hmem6 hFKcd hFKmem le_rfl
    have hstep : Work.Spaces.HkNorm α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
          * Work.Construction.Fstar α z θ)
        ≤ Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
      refine le_trans hbd4 ?_
      calc Css * α ^ (-(1 : ℝ))
            * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
          ≤ Css * α ^ (-(1 : ℝ)) * (A * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left hKfbd ?_
            exact mul_nonneg hCssnn (Real.rpow_nonneg hα0.le _)
        _ = Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by ring
    rw [HkSq_eq_norm_sq]
    calc (Work.Spaces.HkNorm α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
            * Work.Construction.Fstar α z θ)) ^ 2
        ≤ (Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep 2
      _ = (Css * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f), rpow_neg_one_sq hα0]
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC3leC (Real.rpow_nonneg hα0.le _)
  exact ⟨hconj1, hconj2, hconj3, hconj4⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
