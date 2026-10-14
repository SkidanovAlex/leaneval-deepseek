import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS.StrongEps.H5.HAtoms5
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_g2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 800000

/-! ## The five even pieces of the second group

`N_b4_g2` prices the pieces `NBlk α w Φs Φg k`, `k ∈ {10, 12, 14, 16, 18}`, by a single
`α`-free constant times `1 + HkNorm α 5 w`.  We use the same constant `K := 8*C^4 + 1`
(with `C ≥ 1` the context constant) for all five pieces; it dominates every coefficient
that arises from the two product rules:

* piece `10 = -(2α)·(Vs · φD_zw)`:  coefficient `2αC³ ≤ 2C³`;
* piece `12 = -(1/2)·(FKw · D_θw)`: coefficient `(1/2)C²`;
* piece `14 = (1/2)·(FKneg · D_θw)`: coefficient `(1/2)C²`;
* piece `16 = -sin²θ·(FKw · w)`:     coefficient `C³`;
* piece `18 = -sin²θ·(FK(F_*) · w)`: coefficient `C³`.

Each coefficient is `≤ 8*C^4 + 1` (for `C ≥ 1`), and the factor `1 + HkNorm α 5 w` is
nonnegative, so the coefficient bound transfers to `K·(1 + HkNorm α 5 w)`. -/

/-- Coefficient bound for the `α`-small pieces `10`: `2αC³ ≤ 8C⁴+1` for `C ≥ 1`, `α ≤ 1`. -/
private lemma coef_alpha_C3 {C α : ℝ} (hC : 1 ≤ C) (hα1 : α ≤ 1) :
    2 * α * C ^ 3 ≤ 8 * C ^ 4 + 1 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hC3 : (0 : ℝ) ≤ C ^ 3 := by positivity
  have h1 : α * C ^ 3 ≤ C ^ 3 := by
    calc α * C ^ 3 ≤ 1 * C ^ 3 := mul_le_mul_of_nonneg_right hα1 hC3
      _ = C ^ 3 := one_mul _
  have h2 : 2 * C ^ 3 ≤ 8 * C ^ 4 + 1 := by
    have hC3' : (0 : ℝ) ≤ 2 * C ^ 3 := by positivity
    have h4C : (1 : ℝ) ≤ 4 * C := by linarith
    have h : 2 * C ^ 3 ≤ 8 * C ^ 4 := by
      calc 2 * C ^ 3 = (2 * C ^ 3) * 1 := (mul_one _).symm
        _ ≤ (2 * C ^ 3) * (4 * C) := mul_le_mul_of_nonneg_left h4C hC3'
        _ = 8 * C ^ 4 := by ring
    linarith
  linarith

/-- Coefficient bound for the `C²`-pieces `12`, `14`: `(1/2)C² ≤ 8C⁴+1`. -/
private lemma coef_C2 {C : ℝ} (hC : 1 ≤ C) : (1 / 2) * C ^ 2 ≤ 8 * C ^ 4 + 1 := by
  nlinarith [hC, sq_nonneg (C ^ 2), sq_nonneg (C - 1)]


/-- Absorption of the `C`-factor of the outer `-sin²θ`-multiplication
(`hSinMul` gives `Xn (sin²θ·f) ≤ C·Xn f`): `C·(C³·G) ≤ (8C⁴+1)·G`. -/
private lemma C_mul_C3 {C G : ℝ} (hG : 0 ≤ G) :
    C * (C ^ 3 * G) ≤ (8 * C ^ 4 + 1) * G := by
  rw [show C * (C ^ 3 * G) = C ^ 4 * G from by ring]
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (C ^ 2)]) hG

/-- Piece `10`: `-(2α)·(Vs · φD_zw)`, through `mulW_absorb` at `s = 1`. -/
private theorem N_b4_g2_10 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 10) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 10)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) :=
    mul_nonneg ctx.hCpos.le zero_le_G
  have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α ^ 1 := by
    simpa only [pow_one] using ctx.VsW
  have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := -(2 * α)) (s := 1)
    (by norm_num) ctx.hCpos.le hQ ctx.Vssm ctx.VsWm ctx.phiDzwqo hbF ctx.phiDzwX
  have habs : |(-(2 * α))| = 2 * α := by
    rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ctx.hα0]
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show 2 * α * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
      = (2 * α * C ^ 3) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_alpha_C3 ctx.hCone ctx.hα1) zero_le_G

/-- Piece `12`: `-(1/2)·(FKw · D_θw)`, through `mulQo_absorb` at `s = 2`. -/
private theorem N_b4_g2_12 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -(1 / 2)) (s := 2)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKwqo ctx.dthwqo ctx.FKwX ctx.dthwX
  have habs : |(-(1 / 2) : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show (1 / 2) * C * C * (1 + Work.Spaces.HkNorm α 5 w)
      = ((1 / 2) * C ^ 2) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_C2 ctx.hCone) zero_le_G

/-- Piece `14`: `(1/2)·(FKneg · D_θw)`, through `mulW_absorb` at `s = 1`. -/
private theorem N_b4_g2_14 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hbF : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
      ≤ C * α ^ 1 := by
    simpa only [pow_one] using ctx.FKnegW
  have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := (1 / 2)) (s := 1)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKnegsm ctx.FKnegWm ctx.dthwqo hbF ctx.dthwX
  have habs : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at h
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
  refine le_trans h.2 ?_
  rw [show (1 / 2) * C * C * (1 + Work.Spaces.HkNorm α 5 w)
      = ((1 / 2) * C ^ 2) * (1 + Work.Spaces.HkNorm α 5 w) from by ring]
  exact mul_le_mul_of_nonneg_right (coef_C2 ctx.hCone) zero_le_G

/-- Piece `16`: `-sin²θ·(FKw · w)`: inner `ℋ⁴`-product rule, then `hSinMul`. -/
private theorem N_b4_g2_16 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hinner := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := 1) (s := 2)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKwqo ctx.wqo ctx.FKwX ctx.wX
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK w z * w z θ) := by
    simpa only [one_mul] using hinner.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.FK w z * w z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FKwsm ctx.wqo.1
  have h := ctx.hSinMul (fun z θ => Work.Construction.FK w z * w z θ) hsm ⟨hsm, hmem⟩
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
      ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) := by
    have h2 := hinner.2
    have h3 : |(1 : ℝ)| = 1 := by norm_num
    rw [h3] at h2
    have h4 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
        ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [one_mul] using h2
    rw [show C * C * (1 + Work.Spaces.HkNorm α 5 w)
        = C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) from by ring] at h4
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z * w z θ)
        ≤ C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) := h4
      _ ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right (by nlinarith [ctx.hCone]) zero_le_G
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, one_mul] using h.1, ?_⟩
  exact le_trans (le_trans h.2 (mul_le_mul_of_nonneg_left hXn ctx.hCpos.le))
    (C_mul_C3 zero_le_G)

/-- Piece `18`: `-sin²θ·(FK(F_*) · w)`: inner `𝒲^{4,∞} × ℋ⁴` product rule, then `hSinMul`. -/
private theorem N_b4_g2_18 {C C₀ Ce Cs α : ℝ} {Φs w Φg : Fn}
    (ctx : NB4Ctx C C₀ Ce Cs α Φs w Φg) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) := by
  have hbF : Work.Spaces.WlInf α 4 (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
      ≤ C * α ^ 1 := by simpa only [pow_one] using ctx.FKFSW
  have hinner := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := 1) (s := 1)
    (by norm_num) ctx.hCpos.le zero_le_G ctx.FKFSsm ctx.FKFSWm ctx.wqo hbF ctx.wX
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ) := by simpa only [one_mul] using hinner.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z * w z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FKFSsm ctx.wqo.1
  have h := ctx.hSinMul (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z * w z θ)
    hsm ⟨hsm, hmem⟩
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ) ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) := by
    have h2 := hinner.2
    have h3 : |(1 : ℝ)| = 1 := by norm_num
    rw [h3] at h2
    have h4 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * w z θ) ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [one_mul] using h2
    rw [show C * C * (1 + Work.Spaces.HkNorm α 5 w)
        = C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) from by ring] at h4
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * w z θ)
        ≤ C ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) := h4
      _ ≤ C ^ 3 * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right (by nlinarith [ctx.hCone]) zero_le_G
  refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, one_mul] using h.1, ?_⟩
  exact le_trans (le_trans h.2 (mul_le_mul_of_nonneg_left hXn ctx.hCpos.le))
    (C_mul_C3 zero_le_G)

theorem N_b4_g2 (C C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg →
    ∀ k ∈ ({10, 12, 14, 16, 18} : Finset ℕ),
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  refine ⟨8 * C ^ 4 + 1, by nlinarith [sq_nonneg C, sq_nonneg (C ^ 2)], ?_⟩
  intro α _ Φs w Φg ctx k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact N_b4_g2_10 ctx
  · exact N_b4_g2_12 ctx
  · exact N_b4_g2_14 ctx
  · exact N_b4_g2_16 ctx
  · exact N_b4_g2_18 ctx

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkLin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `open scoped Real` makes the bare `π` of the statement below the *notation* for
-- `Real.pi`; without it (and with the workspace's `autoImplicit = false`) `π` is an unknown
-- identifier and the file does not elaborate.  This is the reading of the sibling consumer
-- `RawE6Aux/EpsWPSemitameAux/DevPlaceholders.bdata_blkLin_dev` and of
-- `RawE6Aux/epsWP_semitame_aux`, both of which write the same hypothesis under
-- `open scoped Real`; no other symbol of the statement is affected.
open scoped Real

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

set_option maxHeartbeats 1600000

/-- `BData` for the linear block `blkLin α w = LGammaT α w` of the semi-tame estimate of `epsWP`.  See `Submission/Work/FTS/StrongEps/E4R3/RawE6Aux/NOTES_bdata_blocks.md` for the route. -/
theorem bdata_blkLin (C₀ : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc (0 : ℝ) α₀, ∃ KL : ℝ, 0 < KL ∧
    ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w) := by
  -- ## the constants of the two halves of `𝓛_Γ^T = 𝓛̂ + Corr`
  obtain ⟨Cl, hClpos, hLhat4⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
  obtain ⟨Cl6, hCl6pos, hLhat6⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform_aux 6
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨Crad, hCradpos, hrad⟩ :=
    Work.FTS.StrongEps.EpsRLX.RadBound.radA_slot5_le_classC_of
      Work.FTS.StrongEps.EpsRLX.RadBound.L12fSlotLe
  obtain ⟨C6, α₂, hC6pos, hα₂pos, hCorr6⟩ := Work.FTS.StrongPersist.H6Aux.Corr_HkSq6
  have hKCnn : 0 ≤ Kang * Crad := mul_nonneg hKangpos.le hCradpos.le
  refine ⟨min 1 α₂, lt_min one_pos hα₂pos, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := le_trans hαIoc.2 (min_le_left _ _)
  have hα₂ : α ∈ Set.Ioc (0 : ℝ) α₂ := ⟨hα, le_trans hαIoc.2 (min_le_right _ _)⟩
  refine ⟨2 * Cl + 2 * (Kang * Crad) + (2 * Cl6 + 2 * C6) + 1, by linarith, ?_⟩
  intro w hC hsmall hzero
  -- ## the datum
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 4 (by norm_num) hC.mem
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 5 (by norm_num) hC.mem
  have hmem7 : Work.Spaces.HkMem α 7 w := hC.mem
  have hH6 : Work.FTS.StrongPersist.H6Adm α w :=
    Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hC hzero
  -- ## the two summands of `𝓛_Γ^T = 𝓛̂ + Corr`
  have hLhatsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hC.reg
  have hLGTsm : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hC) hC.reg
  have hCorrsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.NonlinRows.smoothOpen_sub hLGTsm hLhatsm
  -- ## level 4
  have hLhatmem4 : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hC.reg hmem5
  have hCorrmem4 : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hC
  have hLhatSq4 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
      ≤ Cl * Work.Spaces.HkSq α 5 w := hLhat4 α hα w hC.reg hmem5
  have hmono45 : Work.Spaces.HkSq α 4 w ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem5
  have hCorrSq4 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)
      ≤ Kang * Crad * Work.Spaces.HkSq α 5 w := by
    obtain ⟨hint, hbd⟩ := hrad α ⟨hα, hα1⟩ w hC.reg hmem4 hC.l12
    have h1 : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)
        ≤ Kang * (Crad * Work.Spaces.HkSq α 4 w) :=
      (Work.FTS.StrongEps.ClassCRHS.HkSq_Corr_le_classC hα hα1 hKangpos
        (hang α hα hα1) hint).trans (mul_le_mul_of_nonneg_left hbd hKangpos.le)
    refine h1.trans ?_
    rw [show Kang * (Crad * Work.Spaces.HkSq α 4 w)
        = Kang * Crad * Work.Spaces.HkSq α 4 w from by ring]
    exact mul_le_mul_of_nonneg_left hmono45 hKCnn
  have hsum4 : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
          + Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα hLhatsm hCorrsm hLhatmem4 hCorrmem4
  have hb4 : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := by
    calc Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
        ≤ 2 * (Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
            + Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)) := hsum4
      _ ≤ 2 * (Cl * Work.Spaces.HkSq α 5 w
            + Kang * Crad * Work.Spaces.HkSq α 5 w) := by linarith
      _ = (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := by ring
  -- ## level 6
  have hLhatmem6 : Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 6 hC.reg hmem7
  obtain ⟨hCorrmem6, hCorrSq6⟩ := hCorr6 α hα₂ w hH6 hmem7
  have hLhatSq6 : Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Lhat w)
      ≤ Cl6 * Work.Spaces.HkSq α 7 w := hLhat6 α hα w hC.reg hmem7
  have hsum6 : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Lhat w)
          + Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 6 hα hLhatsm hCorrsm hLhatmem6 hCorrmem6
  have hLGmem6 : Work.Spaces.HkMem α 6 (Work.Coercivity.LGammaT α w) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 6 hLhatsm hCorrsm hLhatmem6 hCorrmem6
  have hb6 : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ (2 * Cl6) * Work.Spaces.HkSq α 7 w + (2 * C6) * Work.Spaces.HkSq α 6 w := by
    linarith
  -- ## the assembly
  set KL : ℝ := 2 * Cl + 2 * (Kang * Crad) + (2 * Cl6 + 2 * C6) + 1 with hKLdef
  have hKLnn : 0 ≤ KL := by rw [hKLdef]; linarith
  have hnn5 : 0 ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hnn6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hnn7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hsq : Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    nlinarith [hnn6]
  have hb4' : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ KL * (1 + Work.Spaces.HkSq α 5 w) := by
    have hKL4 : 2 * Cl + 2 * (Kang * Crad) ≤ KL := by rw [hKLdef]; linarith
    calc Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
        ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 w := hb4
      _ ≤ KL * Work.Spaces.HkSq α 5 w := mul_le_mul_of_nonneg_right hKL4 hnn5
      _ ≤ KL * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left (by linarith) hKLnn
  have hb6' : Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
      ≤ KL * (1 + Work.Spaces.HkSq α 7 w)
        + KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have hKL6a : 2 * Cl6 ≤ KL := by rw [hKLdef]; linarith
    have hKL6b : 2 * C6 ≤ KL := by rw [hKLdef]; linarith
    calc Work.Spaces.HkSq α 6 (Work.Coercivity.LGammaT α w)
        ≤ (2 * Cl6) * Work.Spaces.HkSq α 7 w + (2 * C6) * Work.Spaces.HkSq α 6 w := hb6
      _ ≤ KL * Work.Spaces.HkSq α 7 w + KL * Work.Spaces.HkSq α 6 w :=
          add_le_add (mul_le_mul_of_nonneg_right hKL6a hnn7)
            (mul_le_mul_of_nonneg_right hKL6b hnn6)
      _ ≤ KL * (1 + Work.Spaces.HkSq α 7 w) + KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
          have h1 : KL * Work.Spaces.HkSq α 7 w ≤ KL * (1 + Work.Spaces.HkSq α 7 w) :=
            mul_le_mul_of_nonneg_left (by linarith) hKLnn
          have h2 : KL * Work.Spaces.HkSq α 6 w ≤ KL * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hKLnn
          linarith
  exact ⟨hLGTsm, hLGmem6, hb4', hb6'⟩

end Work.FTS.StrongEps.E4R3.RawE6Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC.Part1C =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC

open Work.FTS.Galerkin (Fn)
open Work.FTS.GalFields.RHS.SharpAux.HonTerms

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Part1C {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α g → Work.FTS.ClassC.ClassC α g' →
      Work.FTS.ClassC.ClassC α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
  have hCi : 0 < Ci := hN.pos.1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  obtain ⟨Cang, hCangpos, hangmul0⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Bsin, hBsinpos, -, hBsinle, hBsinIt⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  have hc1 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 := by positivity
  have hc2 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * α * max Ce 0 := by positivity
  have hc3 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have hc4 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) := by
    positivity
  set K : ℝ := 1 + 4 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0)
      + 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * α * max Ce 0)
      + (Ci * α ^ (-(1 / 2 : ℝ))) * Ci
      + (Ci * α ^ (-(1 / 2 : ℝ))) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) with hK
  have hKpos : 0 < K := by rw [hK]; linarith [hc1, hc2, hc3, hc4]
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hg hg' hh hα1
  have hgS : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hhS : Work.FTS.EllipticEst.SmoothOpen h := hh.reg
  have hh4 : Work.Spaces.HkMem α 4 h := cMem hh (k := 4) (by norm_num)
  have hg5 : Work.Spaces.HkMem α 5 g := cMem hg (k := 5) (by norm_num)
  have hg'5 : Work.Spaces.HkMem α 5 g' := cMem hg' (k := 5) (by norm_num)
  have hh5 : Work.Spaces.HkMem α 5 h := cMem hh (k := 5) (by norm_num)
  have hXg' : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g' :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hg'5
  have hXh : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hh5
  have hng : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hng' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hDthhS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) := hhS.Dth
  have hDzhS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) := hhS.Dz
  have hDthh4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith) hh.reg (cMem hh (k := 5) (by norm_num))
  have hDzh4 : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h) :=
    Work.FTS.IPGen.HkMem_Dz_le (k := 4) hh.reg (cMem hh (k := 5) (by norm_num))
  have hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hh5
  have hDzhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hhS hh5
  have hCe_g' : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ce * Work.FTS.Nonlin.Xn α g' →
      Work.FTS.Nonlin.Xn α F
        ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    intro F hF
    exact le_trans hF (le_trans
      (mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 g'))
      (mul_le_mul_of_nonneg_left (by linarith [hXg', hng, hng']) (le_max_right Ce 0)))
  have hCi_g' : ∀ {F : Fn}, Work.FTS.Nonlin.Xn α F ≤ Ci * Work.FTS.Nonlin.Xn α g' →
      Work.FTS.Nonlin.Xn α F
        ≤ Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    intro F hF
    exact le_trans hF (mul_le_mul_of_nonneg_left (by linarith [hXg', hng, hng']) (le_of_lt hCi))
  have hRg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ) := (hEll g' hg').R.1.1
  have hRg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ) := (hEll g' hg').R.1.2
  have hRg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hEll g' hg').R.2
  have hUg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ) :=
    (hEll g' hg').U.1.1
  have hUg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ) :=
    (hEll g' hg').U.1.2
  have hUg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ / Work.Construction.s2 θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hEll g' hg').U.2
  have hVg'S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ) := (hEll g' hg').V.1.1
  have hVg'4 : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ) := (hEll g' hg').V.1.2
  have hVg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ)
      ≤ max Ce 0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCe_g' (hEll g' hg').V.2
  have hFKg' := hN.fkH α hIoc g' (cHQo hg') hg'.l12
  have hFKg'Sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK g' z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hg'
  have hFKg'X : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g' z)
      ≤ Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') :=
    hCi_g' hFKg'.2
  obtain ⟨hnegm_g', hnegs_g'⟩ :=
    (hangmul0 α hα hα1) negSinSq Bsin hBsinpos negSinSq_smooth
      (fun θ hθ => hBsinle θ hθ) (fun i hi1 hi4 θ hθ => hBsinIt i hi1 hi4 θ hθ)
      (fun z _ => Work.Construction.FK g' z) hFKg'Sm hFKg'.1
  obtain ⟨hsinFKg'S, hsinFKg'mem, hsinFKg'Xn⟩ :=
    sinSq_mul hCangpos hBsinpos hFKg'Sm hnegm_g' hnegs_g'
  have hsinFKg'X : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK g' z)
      ≤ (Real.sqrt (Cang * Bsin ^ 2) * Ci)
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    refine le_trans hsinFKg'Xn ?_
    calc Real.sqrt (Cang * Bsin ^ 2)
          * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g' z)
        ≤ Real.sqrt (Cang * Bsin ^ 2)
            * (Ci * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')) :=
          mul_le_mul_of_nonneg_left hFKg'X (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Cang * Bsin ^ 2) * Ci)
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `TRB = 2·(Rop(Φ̃_{g'})·h)`
    obtain ⟨hS1, hM1, hX1⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ) (U := h)
        hRg'S hhS hRg'4 hh4 (A := max Ce 0) (B := 1) (c := 2)
        (le_max_right Ce 0) (by norm_num) hRg'X (by rw [one_mul]; exact hXh)
    refine ⟨hS1, hM1, ?_⟩
    rw [show |(2 : ℝ)| = 2 from by norm_num] at hX1
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX1
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TUB = -2·((U(Φ̃_{g'})/s2)·D_θh)`
    obtain ⟨hS2, hM2, hX2⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ
          / Work.Construction.s2 θ)
        (U := Work.Spaces.Dth h)
        hUg'S hDthhS hUg'4 hDthh4 (A := max Ce 0) (B := 1) (c := -2)
        (le_max_right Ce 0) (by norm_num) hUg'X (by rw [one_mul]; exact hDthhXn)
    refine ⟨hS2, hM2, ?_⟩
    rw [show |(-(2 : ℝ))| = 2 from by rw [abs_neg]; norm_num] at hX2
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX2
      _ = (2 * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TVB = -2α·(V(Φ̃_{g'})·D_zh)`
    obtain ⟨hS3, hM3, hX3⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Zgof α EllSol g') z θ)
        (U := Work.Spaces.Dz h)
        hVg'S hDzhS hVg'4 hDzh4 (A := max Ce 0) (B := 1) (c := -(2 * α))
        (le_max_right Ce 0) (by norm_num) hVg'X (by rw [one_mul]; exact hDzhXn)
    refine ⟨hS3, hM3, ?_⟩
    rw [show |(-(2 * α))| = 2 * α from by rw [abs_neg]; exact abs_of_nonneg (by linarith)] at hX3
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h)
        ≤ 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0 * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX3
      _ = (2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * max Ce 0))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TDB = -(1/2)·(FK(g')·D_θh)`
    obtain ⟨hS4, hM4, hX4⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z _ => Work.Construction.FK g' z) (U := Work.Spaces.Dth h)
        hFKg'Sm hDthhS hFKg'.1 hDthh4 (A := Ci) (B := 1) (c := -(1 / 2))
        (le_of_lt hCi) (by norm_num) hFKg'X (by rw [one_mul]; exact hDthhXn)
    refine ⟨hS4, hM4, ?_⟩
    rw [show |(-(1 / 2 : ℝ))| = 1 / 2 from by rw [abs_neg]; norm_num] at hX4
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α g' h)
        ≤ 1 / 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX4
      _ = ((1 / 2) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring
  · -- `TEB = -1·((sin²θ·FK(g'))·h)`
    obtain ⟨hS5, hM5, hX5⟩ :=
      honest_mul hN hα hαα₂
        (F := fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * Work.Construction.FK g' z)
        (U := h)
        hsinFKg'S hhS hsinFKg'mem hh4
        (A := Real.sqrt (Cang * Bsin ^ 2) * Ci) (B := 1) (c := -1)
        (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hCi)) (by norm_num) hsinFKg'X
        (by rw [one_mul]; exact hXh)
    refine ⟨hS5, hM5, ?_⟩
    rw [show |(-(1 : ℝ))| = 1 from by rw [abs_neg]; norm_num] at hX5
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α g' h)
        ≤ 1 * (Ci * α ^ (-(1 / 2 : ℝ)) * (Real.sqrt (Cang * Bsin ^ 2) * Ci) * 1
            * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := hX5
      _ = ((Ci * α ^ (-(1 / 2 : ℝ))) * (Real.sqrt (Cang * Bsin ^ 2) * Ci))
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith [hng, hng']) hnh)
            rw [hK]; nlinarith [hc1, hc2, hc3, hc4]
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by ring

end Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.IdentityC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option pp.deepTerms true

/-- `PhiTil α F Φ` is `C^∞` on the open quadrant as soon as `Φ` is and `z ↦ L₁₂(F)(z)` is
(the two ingredients of its definition). -/
theorem smoothOpen_PhiTil_of_open {α : ℝ} (hα : 0 < α) {F Φ : Fn}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 F z)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α F Φ) := by
  have hEq : Work.Construction.PhiTil α F Φ = fun z θ =>
      Φ z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z := rfl
  rw [hEq]
  simp only [Work.Construction.s2]
  refine Work.FTS.NonlinRows.smoothOpen_sub hΦ ?_
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    hL

theorem NDiffIdC {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {W₁ W₂ h : Fn} (hW₁ : Work.FTS.ClassC.ClassC α W₁)
    (hW₂ : Work.FTS.ClassC.ClassC α W₂) (hh : Work.FTS.ClassC.ClassC α h)
    (hh_eq : ∀ z θ : ℝ, h z θ = W₁ z θ - W₂ z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ) z θ)
      = (List.foldr (fun f acc => f + acc) (0 : Fn)
          (Work.FTS.GalFields.RHS.Sharp.termList α Φs E W₁ W₂ h)) z θ := by
  intro z θ hq
  obtain ⟨hz, hθ1, hθ2⟩ : z ∈ Set.Ioi (0 : ℝ) ∧ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    simpa only [Work.Construction.Qd, Set.mem_prod] using hq
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hs2ne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  -- the difference potential `δ = E W₁ - E W₂`
  set δ : Fn := fun z θ => E W₁ z θ - E W₂ z θ with hδdef
  -- ## smoothness of the data
  have hFstarS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hW₁S : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hW₂S : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hhS : Work.FTS.EllipticEst.SmoothOpen h := hh.reg
  have hδS : Work.FTS.EllipticEst.SmoothOpen δ := by
    rw [hδdef]
    exact Work.FTS.EllipticEst.smoothOpen_sub (hEll W₁ hW₁).1.smooth (hEll W₂ hW₂).1.smooth
  have hZs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα hα1 hstar
  have hZg₁ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α W₁ (E W₁)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll W₁ hW₁).1
  have hZg₂ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α W₂ (E W₂)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll W₂ hW₂).1
  have hDl : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α h (E h)) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα (hEll h hh).1
  have hDlδ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α h δ) :=
    smoothOpen_PhiTil_of_open hα hδS
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hh)
  -- ## honesty of the data
  have hW₁4 : Work.Spaces.HkMem α 4 W₁ := cMem hW₁ (by norm_num)
  have hW₂4 : Work.Spaces.HkMem α 4 W₂ := cMem hW₂ (by norm_num)
  have hh4 : Work.Spaces.HkMem α 4 h := cMem hh (by norm_num)
  -- ## the potential identities on `Q0`
  have hpot1 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α W₁ (E W₁) z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 (Work.Construction.Ftot α W₁) z'
        = Work.Construction.L12 (Work.Construction.Fstar α) z'
          + Work.Construction.L12 W₁ z' :=
      (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hW₁.reg hW₁4).1 z'
        (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  have hpot2 : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ) z' θ'
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ'
          + Work.Construction.PhiTil α W₂ (E W₂) z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 (Work.Construction.Ftot α W₂) z'
        = Work.Construction.L12 (Work.Construction.Fstar α) z'
          + Work.Construction.L12 W₂ z' :=
      (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hW₂.reg hW₂4).1 z'
        (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    ring
  -- the `L₁₂`-additivity along the difference
  have hL12sub : ∀ z' : ℝ, 0 ≤ z' →
      Work.Construction.L12 W₁ z' = Work.Construction.L12 h z' + Work.Construction.L12 W₂ z' :=
    fun z' hz' => Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 hW₁S hW₂S hhS hW₁4 hW₂4 hh4 hh_eq hz'
  -- the *new* potential identity: the `h`-node potential is `PhiTil α h δ`
  have hpot3δ : ∀ z' θ' : ℝ, 0 < z' →
      Work.Construction.PhiTil α W₁ (E W₁) z' θ'
        = Work.Construction.PhiTil α h δ z' θ'
          + Work.Construction.PhiTil α W₂ (E W₂) z' θ' := by
    intro z' θ' hz'
    have hL := hL12sub z' (le_of_lt hz')
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL]
    rw [hδdef]
    simp only
    ring
  -- the **slot identity** on the quadrant: the slot of the `h`-node depends only on the source
  have hslots := by
    have hfun : h = fun z θ => W₁ z θ - W₂ z θ := by
      funext z θ
      exact hh_eq z θ
    have hsub : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce h δ := by
      rw [hfun, hδdef]
      exact Work.FTS.StrongEps.EComparison.EllPkgCls_E_sub_of_theta hEll hW₁ hW₂
        (Work.FTS.StrongEps.EComparison.theta_sub_of_classC hW₁ hW₂)
    have hpkg : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce h (E h) :=
      Work.FTS.StrongEps.EComparison.EllPkgCls_of_pkg hEll hh
    exact Work.FTS.StrongEps.EComparison.slots_eq_of_source_quadrant hα hα1 hsub hpkg
  have hslotR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    simpa only [Work.FTS.StrongEps.EComparison.SlotR] using hslots.1 z θ hz' hθ0 hθ1
  have hslotU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    have h := hslots.2.1 z θ hz' hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    simp only [Work.FTS.StrongEps.EComparison.SlotU, div_eq_mul_inv] at h
    exact mul_right_cancel₀ (inv_ne_zero hs) h
  have hslotV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop (Work.Construction.PhiTil α h δ) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ := by
    intro z θ hz' hθ0 hθ1
    simpa only [Work.FTS.StrongEps.EComparison.SlotV] using hslots.2.2 z θ hz' hθ0 hθ1
  -- ## additivity of `ℛ`, `U`, `V` on the potentials
  have r1 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have r2 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have r3 : Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Rop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Rop α (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Rop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotR z θ hz hθ1 hθ2]
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hz0 : z ≠ 0 := ne_of_gt hz
  have r4 : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = (z / (1 + z)) * Work.FTS.GalFields.RHS.Sharp.StarH α Φs z θ := by
    have hfac : (z / (1 + z)) * ((z + 1) / z) = 1 := by field_simp <;> ring
    simp only [Work.FTS.GalFields.RHS.Sharp.StarH, Work.FTS.Nonlin.PhiTs]
    rw [show (z / (1 + z)) * ((z + 1) / z
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        = ((z / (1 + z)) * ((z + 1) / z))
          * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        from by ring, hfac, one_mul]
  have u1 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have u2 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have u3 : Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Uop α (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Uop α (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotU z θ hz hθ1 hθ2]
  have hcancel : ∀ (X : ℝ), Real.sin (2 * θ) * (X / Real.sin (2 * θ)) = X := by
    intro X
    rw [div_eq_mul_inv, mul_comm (Real.sin (2 * θ)) (X * (Real.sin (2 * θ))⁻¹), mul_assoc,
      inv_mul_cancel₀ hs2ne, mul_one]
  have u4 : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      = Real.sin (2 * θ) * Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs z θ := by
    have hc := hcancel (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    simp only [Work.FTS.GalFields.RHS.Sharp.UsPhi, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTs] at hc ⊢
    exact hc.symm
  have u5 : Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α W₂ (E W₂)) z θ)).symm
  have u6 : Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
      = Real.sin (2 * θ)
        * (Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ
          / Real.sin (2 * θ)) :=
    (hcancel (Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ)).symm
  have v1 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₁ (E W₁) z θ)
            (fun z' θ' hz' _ _ => hpot1 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hZs hZg₁ z θ hz hθ1 hθ2
  have v2 : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ))
            (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot2 z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hZs hZg₂ z θ hz hθ1 hθ2
  have v3 : Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
    calc Work.Construction.Vop (Work.Construction.PhiTil α W₁ (E W₁)) z θ
        = Work.Construction.Vop (fun z θ =>
            Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Work.Construction.PhiTil α W₁ (E W₁))
            (g := fun z θ => Work.Construction.PhiTil α h δ z θ
              + Work.Construction.PhiTil α W₂ (E W₂) z θ)
            (fun z' θ' hz' _ _ => hpot3δ z' θ' hz') z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α h δ) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hDlδ hZg₂ z θ hz hθ1 hθ2
      _ = Work.Construction.Vop (Work.Construction.PhiTil α h (E h)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α W₂ (E W₂)) z θ := by
          rw [hslotV z θ hz hθ1 hθ2]
  -- ## the derivative, moment and value identities
  have hW₁_eq : W₁ = fun z θ => W₂ z θ + h z θ := by
    funext z' θ'
    have := hh_eq z' θ'
    linarith
  have d1 : Work.Spaces.pz (Work.Construction.Ftot α W₁) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W₁ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hW₁S z θ hz hθ1 hθ2
  have d2 : Work.Spaces.pz (Work.Construction.Ftot α W₂) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz W₂ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFstarS hW₂S z θ hz hθ1 hθ2
  have d3 : Work.Spaces.pz W₁ z θ = Work.Spaces.pz W₂ z θ + Work.Spaces.pz h z θ := by
    rw [hW₁_eq]
    exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hW₂S hhS z θ hz hθ1 hθ2
  have d4 : Work.Spaces.pth (Work.Construction.Ftot α W₁) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W₁ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hW₁S z θ hz hθ1 hθ2
  have d5 : Work.Spaces.pth (Work.Construction.Ftot α W₂) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth W₂ z θ :=
    Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFstarS hW₂S z θ hz hθ1 hθ2
  have d6 : Work.Spaces.pth W₁ z θ = Work.Spaces.pth W₂ z θ + Work.Spaces.pth h z θ := by
    rw [hW₁_eq]
    exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hW₂S hhS z θ hz hθ1 hθ2
  have k1 : Work.Construction.FK (Work.Construction.Ftot α W₁) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W₁ z :=
    Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hW₁.reg hW₁4 hz
  have k2 : Work.Construction.FK (Work.Construction.Ftot α W₂) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK W₂ z :=
    Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hW₂.reg hW₂4 hz
  have k3 : Work.Construction.FK W₁ z
      = Work.Construction.FK W₂ z + Work.Construction.FK h z :=
    (Work.FTS.GalFields.RHS.Sharp.FK_sub hW₁S hW₂S hhS hW₁4 hW₂4 hh4
      (fun z θ => (hh_eq z θ)) hz).trans (by ring)
  have k4 : Work.Construction.FK (Work.Construction.Fstar α) z
      = Work.FTS.GalFields.RHS.Sharp.Fkstar α z θ := by
    simp only [Work.FTS.GalFields.RHS.Sharp.Fkstar, Work.Spaces.hKer_apply,
      Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    ring
  have f1 : Work.Construction.Ftot α W₁ z θ
      = Work.Construction.Fstar α z θ + W₁ z θ := by
    simp only [Work.Construction.Ftot]
  have f2 : Work.Construction.Ftot α W₂ z θ
      = Work.Construction.Fstar α z θ + W₂ z θ := by
    simp only [Work.Construction.Ftot]
  -- ## the `U`-terms in undivided form (the `sin 2θ` denominator cancels)
  have hTUAund : Work.FTS.GalFields.RHS.Sharp.TUA α Φs h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUA, Work.FTS.GalFields.RHS.Sharp.UsPhi,
      Work.FTS.Nonlin.PhiTs, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUBund : Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α W₂ (E W₂)) z θ
        * Work.Spaces.pth h z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUB, Work.FTS.GalFields.RHS.Sharp.Zgof,
      Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUCund : Work.FTS.GalFields.RHS.Sharp.TUC α E h z θ
      = (-2) * (Work.Spaces.pth (Work.Construction.Fstar α) z θ
        * Work.Construction.Uop α (Work.Construction.PhiTil α h (E h)) z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUC, Work.FTS.GalFields.RHS.Sharp.DthFstar,
      Work.FTS.GalFields.RHS.Sharp.Dof, Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  have hTUDund : Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ h z θ
      = (-2) * (Work.Construction.Uop α
          (Work.Construction.PhiTil α h (E h)) z θ
        * Work.Spaces.pth W₁ z θ) := by
    simp only [Work.FTS.GalFields.RHS.Sharp.TUD, Work.FTS.GalFields.RHS.Sharp.Dof,
      Work.Spaces.Dth, Work.Construction.s2]
    field_simp <;> ring
  -- ## the telescoping
  rw [Work.FTS.GalFields.RHS.Sharp.termList_foldr]
  simp only [Work.Construction.N, Work.Spaces.Dz, Work.Construction.s2]
  rw [r1, r2, r3, r4, u1, u2, u3, v1, v2, v3,
    d1, d2, d3, d4, d5, d6, k1, k2, k3, k4, f1, f2]
  simp only [Pi.add_apply]
  rw [hTUAund, hTUBund, hTUCund, hTUDund]
  simp only [Work.FTS.GalFields.RHS.Sharp.TRA, Work.FTS.GalFields.RHS.Sharp.TRB,
    Work.FTS.GalFields.RHS.Sharp.TRC, Work.FTS.GalFields.RHS.Sharp.TRD,
    Work.FTS.GalFields.RHS.Sharp.TUA, Work.FTS.GalFields.RHS.Sharp.TUB,
    Work.FTS.GalFields.RHS.Sharp.TUC, Work.FTS.GalFields.RHS.Sharp.TUD,
    Work.FTS.GalFields.RHS.Sharp.TVA, Work.FTS.GalFields.RHS.Sharp.TVB,
    Work.FTS.GalFields.RHS.Sharp.TVC, Work.FTS.GalFields.RHS.Sharp.TVD,
    Work.FTS.GalFields.RHS.Sharp.TDA, Work.FTS.GalFields.RHS.Sharp.TDB,
    Work.FTS.GalFields.RHS.Sharp.TDC, Work.FTS.GalFields.RHS.Sharp.TDD,
    Work.FTS.GalFields.RHS.Sharp.TEA, Work.FTS.GalFields.RHS.Sharp.TEB,
    Work.FTS.GalFields.RHS.Sharp.TEC, Work.FTS.GalFields.RHS.Sharp.TED,
    Work.FTS.GalFields.RHS.Sharp.StarH, Work.FTS.GalFields.RHS.Sharp.UsPhi,
    Work.FTS.GalFields.RHS.Sharp.Vstar, Work.FTS.GalFields.RHS.Sharp.Fkstar,
    Work.FTS.GalFields.RHS.Sharp.DthFstar, Work.FTS.GalFields.RHS.Sharp.DzFstar,
    Work.FTS.GalFields.RHS.Sharp.Zgof, Work.FTS.GalFields.RHS.Sharp.Dof,
    Work.FTS.Nonlin.PhiTs, Work.Spaces.Dz, Work.Spaces.Dth, Work.Construction.s2,
    Work.FTS.GalFields.RHS.Sharp.sinSq, Work.FTS.GalFields.RHS.Sharp.pfac]
  rw [d6, d3, hh_eq]
  ring

end Work.FTS.StrongEps.EpsRLX.CCSharp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ModDiffAux.TransportDiffClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ModDiffAux/TransportDiffClassC` — the transport `L₁₂`-difference on the class `C`

The third of the three `L₁₂`-zero-mode differences whose combination is the difference of the
modulation constants (`Work.FTS.StrongEps.EpsRLX.ModDiffClassC`).  The transport zero mode
`g ↦ L₁₂(3·D_θg/(1+z))(0)` is **linear** in the profile (`L12_sub_eq_of_smoothOpen`, valid on
the class), so its difference is the *single-profile* row estimate
`Work.FTS.Nonlinear.Open.Rl2` (`Work.FTS_MuLamOK.KMu2_row`, constant `KMu2 = 9`) applied to the
difference `W₁ - W₂` of the two `ClassC` data.

The two auxiliary facts supplied here are

* `smoothOpen_hkMem_three_div_Dth`: the transport datum `3·D_θf/(1+z)` of an
  `SmoothOpen`/`HkMem α 5` profile is `C^∞` on the open quadrant and honest in `ℋ⁴`
  (the `RegQ α 5`-free version of `SharpMod.smoothOpen_and_hkMem_three_div_Dth`), and
* `L12_transport_diff_classC`: the difference estimate itself.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ModDiffAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The transport datum `3·D_θf/(1+z)` is `C^∞` on the open quadrant and honest in `ℋ⁴`**,
from `SmoothOpen f` and `HkMem α 5 f` alone (no `SmoothQuad`/`RegQ` hypothesis: the interior
class of `ClassC` is enough).  This is `SharpMod.smoothOpen_and_hkMem_three_div_Dth` with the
`RegQ α 5`-hypothesis replaced by its two *interior* consequences. -/
theorem smoothOpen_hkMem_three_div_Dth {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) := by
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := hsm.Dth
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith [hα.le]) hsm hmem
  obtain ⟨Cphi, _hCphi, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hphiMem : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ) :=
    (hmulphi hα hα1 ⟨hDthSm, hDthMem⟩).1
  have hphiSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen hDthSm
  constructor
  · exact Work.FTS.GalFields.RHS.SharpMod.smoothOpen_three_div_mul hDthSm
  · have h1 : Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth f z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hDthMem
    have h2 : Work.Spaces.HkMem α 4
        (fun z θ => 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hphiMem
    have hsub : Work.Spaces.HkMem α 4
        (fun z θ => 3 * Work.Spaces.Dth f z θ
          - 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hDthSm)
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hphiSm) h1 h2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsub ?_
    intro z hz θ hθ
    have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < z from hz])
    simp only [Work.FTS.NonlinRows.NRow10aux.phiF]
    field_simp
    ring

/-- The `ℋ⁴`-honesty of a `ClassC` datum descends to any order `≤ 7`. -/
theorem hkMem_classC_le {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {k : ℕ} (hk : k ≤ 7) :
    Work.Spaces.HkMem α k W :=
  Work.FTS.OpenPkg.HkMem_mono_open hW.reg k hk hW.mem

/-- **The `L₁₂`-zero-mode difference of the transport term, on the class `C`.** -/
theorem L12_transport_diff_classC {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  refine ⟨Work.FTS_MuLamOK.KMu2 + 1, by linarith [Work.FTS_MuLamOK.KMu2_pos], ?_⟩
  intro W₁ W₂ hW₁ hW₂
  -- the difference datum
  have hhC : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongEps.EpsRLX.CCSharp.sub_classC hW₁ hW₂
  have hh5 : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 5 (by norm_num) hhC.mem
  -- the three data
  obtain ⟨hsm₁, hmem₁⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hW₁.reg (hkMem_classC_le hW₁ (by norm_num))
  obtain ⟨hsm₂, hmem₂⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hW₂.reg (hkMem_classC_le hW₂ (by norm_num))
  obtain ⟨hsmh, hmemh⟩ :=
    smoothOpen_hkMem_three_div_Dth hα0 hα1 hhC.reg hh5
  -- linearity of `L₁₂` in the profile
  have hlin := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hmem₁ hmem₂ 0 le_rfl
  -- the difference datum is the datum of `W₁ - W₂`
  have hkey : Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)
        - 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0
      = Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ) z θ
          / (1 + z)) 0 := by
    refine Work.FTS.GalFields.RHS.SharpMod.L12_congr_of_dens (fun s hs => ?_)
    refine Work.FTS.GalFields.RHS.SharpMod.L12dens_congr_of_Iθ (fun θ hθ => ?_)
    have hadd := Work.FTS.GalFields.RHS.SharpMod.Dth_add_of_pointwise
      (g := W₁) (g' := W₂) (h := fun z θ => W₁ z θ - W₂ z θ) hW₂.reg hhC.reg
      (fun z θ => by ring) s θ hs hθ
    rw [hadd]
    ring
  rw [hlin, hkey]
  -- the row estimate at the difference, and the `ℋ⁴ ≤ ℋ⁵` comparison
  have hh4 : Work.Spaces.HkMem α 4 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 4 (by norm_num) hhC.mem
  have hrow := Work.FTS_MuLamOK.KMu2_row (α := α) (f := fun z θ => W₁ z θ - W₂ z θ)
    hα0 hα1 hhC.reg hh4
  have hXle : Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ)
      ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hh5
  have hXn0 : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hfac : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ := by
    have h1 := Work.Spaces.HkNorm_nonneg α 5 W₁
    have h2 := Work.Spaces.HkNorm_nonneg α 5 W₂
    linarith
  calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ) z θ
          / (1 + z)) 0|
      ≤ Work.FTS_MuLamOK.KMu2 * Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ) := hrow
    _ ≤ Work.FTS_MuLamOK.KMu2 * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
        mul_le_mul_of_nonneg_left hXle (le_of_lt Work.FTS_MuLamOK.KMu2_pos)
    _ ≤ (Work.FTS_MuLamOK.KMu2 + 1)
          * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
        have hd : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hXn0
        have hK : (0 : ℝ) < Work.FTS_MuLamOK.KMu2 + 1 :=
          by linarith [Work.FTS_MuLamOK.KMu2_pos]
        have h1 : Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
            ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          simpa using mul_le_mul_of_nonneg_right hfac hd
        calc Work.FTS_MuLamOK.KMu2
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
            ≤ (Work.FTS_MuLamOK.KMu2 + 1)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
              mul_le_mul_of_nonneg_right (by linarith [Work.FTS_MuLamOK.KMu2_pos]) hd
          _ ≤ (Work.FTS_MuLamOK.KMu2 + 1)
              * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
                * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hK)
          _ = (Work.FTS_MuLamOK.KMu2 + 1)
              * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring

end Work.FTS.StrongEps.EpsRLX.ModDiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Nb5Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The level-`5` `N`-block data from the atomic packages** (the analogue of
`ClassCRHS.nb_data`): smoothness, `ℋ⁵`-membership and a uniform level-`5` norm bound of each of
the twenty pieces, together with their agreement with `N` on the open quadrant. -/
theorem Nb5_data
    (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg)
    (hsmB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      ∀ k ∈ Finset.range 20,
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        (∀ k ∈ Finset.range 20,
          Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) ∧
        (∀ k ∈ Finset.range 20,
          Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
          Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ Kbig) ∧
        (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
          Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ) z θ
            = ∑ k ∈ Finset.range 20,
                Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k z θ) := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  obtain ⟨Kbig, hKbig, hpieces⟩ := Nb5_pieces hH hWs hWf hHf hsin5 hαI
    (C₀ := C₀) (B := B) (Ce := Ce) (Cs6 := Cs6) (Φs := Φs)
  refine ⟨Kbig, hKbig, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  -- ## the split of `N` into the twenty pieces
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hLadd : ∀ z : ℝ, 0 < z →
      Work.Construction.L12 (Work.Construction.Ftot α w) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 w z :=
    fun z hz => Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα0 hαI.2 hw.reg hmem4w z hz
  have hFKadd : ∀ z : ℝ, 0 < z →
      Work.Construction.FK (Work.Construction.Ftot α w) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
    fun z hz => Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα0 z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4w hz)
  have hL12d : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 w z') z :=
    fun z hz => Work.FTS.StrongEps.EComparison.differentiableAt_L12_of_Vop (ne_of_gt hα0)
      (F := w) (Ψ := Φg) hell.smooth hell.V.1.1 hz
  have hsplit := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := w) (Φs := Φs) (Φg := Φg)
    hα0 hαI.2 hw.reg hstar.smooth hell.smooth hLadd hFKadd hL12d
  refine ⟨hsmB hαI hw hell hstar, hpieces hw hXw hX6 hell hstar, ?_⟩
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ1⟩ := hzθ
  rw [hsplit z θ ⟨hz, hθ0, hθ1⟩, ← Work.FTS.StrongEps.ClassCRHS.PB_sum_eq α w Φs Φg z θ]
  exact Finset.sum_congr rfl (fun k hk =>
    Work.FTS.StrongEps.ClassCRHS.PB_eq_NBlk hα0 hαI.2 w Φs Φg k hk z θ hz hθ0 hθ1)

/-- **The level-`5` `N`-block from the atomic packages** — the level-`5` analogue of
`ClassCRHS.HkMemXnN`. -/
theorem HkMemXnN5_of_atoms
    (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg)
    (hsmB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      ∀ k ∈ Finset.range 20,
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k))
    (hsmN : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ K : ℝ, 0 < K ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        Work.Spaces.HkMem α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  obtain ⟨Kbig, hKbig, hdata⟩ := Nb5_data hH hWs hWf hHf hsin5 hsmB hαI (C₀ := C₀) (B := B)
    (Ce := Ce) (Cs6 := Cs6) (Φs := Φs)
  refine ⟨Kbig * (2 ^ 20 * 20) + 1, by positivity, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  obtain ⟨hsm, hpm, hid⟩ := hdata hw hXw hX6 hell hstar
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (hsmN hαI hw hell hstar) α 5
  obtain ⟨hmem, hbnd⟩ := HkSumOpenClosure5 (α := α) hα0 hcont hsm
    (fun k hk => (hpm k hk).1) (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  refine ⟨hmem, ?_⟩
  refine le_trans hbnd ?_
  have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : ∑ k ∈ Finset.range 20, Work.Spaces.HkNorm α 5
      (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ 20 * Kbig := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpm k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc Real.sqrt ((2 : ℝ) ^ 20)
        * ∑ k ∈ Finset.range 20, Work.Spaces.HkNorm α 5
            (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
      ≤ 1024 * (20 * Kbig) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Kbig * (2 ^ 20 * 20) + 1 := by nlinarith [hKbig]

end Work.FTS.StrongEps.H5
end
end
