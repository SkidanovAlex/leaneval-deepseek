import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.WlInfTermsBoundC
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components2
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.H5.HAtoms5
import Submission.Work.FTS.StrongEps.H5.Nb5Core
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.H2.T1Q.SlotOpen
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.N_b4` — the level-`4` semi-tame estimate of the `N`-block, `α`-free

The proof is the assembly of four ingredients, all in this directory:

* `N_aux.N_b4_ctx` — the pricing context `NB4Ctx C C₀ Ce Cs α Φs w Φg` at an `α`-free constant
  `C` (`N_aux.NB4Aux` holds the structure and the absorption lemmas `mulQo_absorb`,
  `mulW_absorb`);
* `N_aux.N_b4_g1`, `N_aux.N_b4_g2`, `N_aux.N_b4_s` — the twenty pieces
  `ClassCRHS.NBlk α w Φs Φg k`, each `ℋ⁴`-honest and priced by `K·(1 + HkNorm α 5 w)`;
* the identity `N = ∑_{k<20} NBlk k` on the open quadrant, from `ClassCRHS.nb_data` (its `B`-slot
  is instantiated with `HkNorm α 6 w`), and the closure `ClassCRHS.HkSumOpenClosure`.

Everything is summed with `HkNorm_finset_sum_le` (`√(2²⁰) = 1024`, twenty pieces) and the final
arithmetic `(1 + HkNorm α 5 w)² ≤ 2(1 + HkSq α 5 w)`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The level-4 semi-tame estimate of the `N`-block**, with an `α`-free constant.

This is the `b4` field of `BData α w K (blkN α Φs w Φg)`: the ℋ⁴-energy of
`N α (Ftot α w) (Φs + Φg)`, priced by `1 + HkSq α 5 w` (the `HkNorm α 5 w` of the slot shifts).

Route (see `Submission/Work/FTS/StrongEps/E4R3/Apriori4Proofs/blocks/N_aux/NOTES_N_BData.md`,
§1–§2 for the details and the list of available α-free atom prices):

* use the twenty-piece decomposition `ClassCRHS.NBlk α w Φs Φg` (`ClassCRHS.HkMemXnNDefs`), whose
  sum equals `N α (Ftot α w) (Φs+Φg)` on the open quadrant (`ClassCRHS.HkMemXnNIdent`);
* price every piece at level `4` with the level-4 product rules of `OpenPkg`
  (`prod_field`, `wprod_field_winf`, `ang_mul_HkSq_le`): each coefficient is α-small at level 4
  (perturbed coefficients have `HkNorm α 4 ≤ Ce·Xn α w ≤ Ce C₀ α²` by `EllPkgGo`; the star
  coefficients have `WlInf α 4 ≤ Cs α` by `StarPkg6`; `FK w` has `HkNorm α 4 ≤ C·Xn α w`;
  the fixed atoms are bounded by `alpha`-powers by `Nonlinear.FstarPkg`/`H5.fixed_atoms5`), and
  each slot is either a `w`-slot (`HkNorm α 4 ≤ HkNorm α 5 w` by the level shifts
  `StrongPersist.H6Aux.HkSq_Dth_le_succ'`, `HkSq_Dz_le_succ'`) or an `F_*`-slot (`HkNorm α 4 ≤ C`);
  after squaring, the `α^{-1}` of the product rule is absorbed by the α-smallness of the
  coefficient, so a single `K` independent of `α ∈ (0,1]` works;
* sum with the additivity of `HkSq` and conclude
  `HkNorm α 4 N ≤ C·(1 + HkNorm α 5 w)`, hence
  `HkSq α 4 N ≤ 2C²(1 + HkSq α 5 w)`.

`ClassCRHS.HkMemXnN`/`nb_data` is the template, but it carries an extra `HkNorm α 6 w ≤ B` with
`B` fixed before `w`, and its constants depend on `α`; both must be removed here. -/
theorem N_b4 (C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨C, hCpos, hctx⟩ := N_b4_ctx C₀ Ce Cs
  obtain ⟨K1, hK1, hg1⟩ := N_b4_g1 C C₀ Ce Cs
  obtain ⟨K2, hK2, hg2⟩ := N_b4_g2 C C₀ Ce Cs
  obtain ⟨K3, hK3, hs⟩ := N_b4_s C C₀ Ce Cs
  obtain ⟨C1, hC1, hs1⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
  refine ⟨(1024 * 20 * (K1 + K2 + K3)) ^ 2 * 2 + 1, by positivity, ?_⟩
  intro α hαmem Φs w Φg hw hXw hzero hell hK6 hstar
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hstar2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hstar.toStarPkgo2
  -- the pricing context of the twenty pieces
  have hcx : NB4Ctx C C₀ Ce Cs α Φs w Φg := hctx α hαmem Φs w Φg hw hXw hell hstar
  -- the identity `N = ∑_{k<20} NBlk k` on the open quadrant (and the `SmoothOpen` of the pieces),
  -- through `nb_data` at `B := HkNorm α 6 w`
  obtain ⟨Kbig, hKbig, hdata⟩ :=
    Work.FTS.StrongEps.ClassCRHS.nb_data hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  obtain ⟨hsmAll, -, hid⟩ := hdata hw hXw (le_refl (Work.Spaces.HkNorm α 6 w)) hell hstar2
  -- the per-piece data, in the form consumed by `HkSumOpenClosure`
  set K : ℝ := K1 + K2 + K3 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith [hK1.le, hK2.le, hK3.le]
  have hGnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := zero_le_G
  have hpiece : ∀ k ∈ Finset.range 20,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    have key : ∀ k ∈ ({0, 2, 4, 6, 8} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hg1 α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK2.le, hK3.le] : K1 ≤ K) hGnn)⟩
    have key2 : ∀ k ∈ ({10, 12, 14, 16, 18} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hg2 α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK1.le, hK3.le] : K2 ≤ K) hGnn)⟩
    have key3 : ∀ k ∈ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hs α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK1.le, hK2.le] : K3 ≤ K) hGnn)⟩
    interval_cases k
    · exact key 0 (by decide)
    · exact key3 1 (by decide)
    · exact key 2 (by decide)
    · exact key3 3 (by decide)
    · exact key 4 (by decide)
    · exact key3 5 (by decide)
    · exact key 6 (by decide)
    · exact key3 7 (by decide)
    · exact key 8 (by decide)
    · exact key3 9 (by decide)
    · exact key2 10 (by decide)
    · exact key3 11 (by decide)
    · exact key2 12 (by decide)
    · exact key3 13 (by decide)
    · exact key2 14 (by decide)
    · exact key3 15 (by decide)
    · exact key2 16 (by decide)
    · exact key3 17 (by decide)
    · exact key2 18 (by decide)
    · exact key3 19 (by decide)
  -- the closure
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
        p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar2).2.2.2.2 α 4
  obtain ⟨hmemN, hbndN⟩ := Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure hα0 hcont hsmAll
    (fun k hk => (hpiece k hk).1) (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  -- the sum bound
  have hsum : (∑ k ∈ Finset.range 20,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k))
      ≤ 20 * (K * (1 + Work.Spaces.HkNorm α 5 w)) := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpiece k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hXnN : Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) ≤ 1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w))) := by
    refine le_trans hbndN ?_
    rw [hsqrt]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  -- conclude
  have hsq : Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ))
      = (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))
        = Real.sqrt (Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) := rfl
    rw [h1, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
  rw [hsq]
  have hG2 : (1 + Work.Spaces.HkNorm α 5 w) ^ 2 ≤ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
    have h5 : (Work.Spaces.HkNorm α 5 w) ^ 2 = Work.Spaces.HkSq α 5 w := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 w)]
    nlinarith [h5, sq_nonneg (Work.Spaces.HkNorm α 5 w - 1)]
  have hstep : (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ))) ^ 2
      ≤ (1024 * 20 * K) ^ 2 * (2 * (1 + Work.Spaces.HkSq α 5 w)) := by
    have h1 : (1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w)))) ^ 2
        = (1024 * 20 * K) ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) ^ 2 := by ring
    have h2 : (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) ^ 2
        ≤ (1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w)))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hXnN 2
    rw [h1] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_left hG2 (sq_nonneg _))
  have hfin : (1024 * 20 * K) ^ 2 * (2 * (1 + Work.Spaces.HkSq α 5 w))
      ≤ ((1024 * 20 * K) ^ 2 * 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    have hnn : 0 ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith [Work.Spaces.HkSq_nonneg α 5 w]
    nlinarith [hnn, sq_nonneg (1024 * 20 * K)]
  exact le_trans hstep hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The `-μ̄AK` block**, honest version of `Open2.AKTerm_bound2`. -/
theorem AKTerm_boundT {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Fn} {A : ℝ}
    (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg)
    (hA : |A| ≤ 2 * (C * (α ^ 2 + Real.sqrt α * (Xn α g)
      + α ^ (-(3 / 2 : ℝ)) * (Xn α g) ^ 2))) :
    |IP α (fun z θ => -A * Work.Construction.AK α z θ) g|
      ≤ 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀pos : 0 < K₀ := h.hK₀pos
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := h.hg4
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α (Xn α g) := Pbd_nonneg hα.le hX0
  have hsm : IP α (fun z θ => -A * Work.Construction.AK α z θ) g
      = -A * IP α (Work.Construction.AK α) g :=
    hE.smul α hαIoc (-A) (Work.Construction.AK α) g hR.rak.1 hg4
  have hAK : |IP α (Work.Construction.AK α) g| ≤ Ct * Xn α (Work.Construction.AK α) * Xn α g :=
    hE.cs α hαIoc _ g hR.rak.1 hg4
  have hAK' : |IP α (Work.Construction.AK α) g| ≤ K₀ * C * Xn α g := by
    have h1 : Ct * Xn α (Work.Construction.AK α) * Xn α g ≤ Ct * C * Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR.rak.2 hCt.le) hX0
    have h2 : Ct * C * Xn α g ≤ K₀ * C * Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hX0
    linarith [hAK, h1, h2]
  have hm1 : α ^ 2 * Xn α g ≤ Pbd α (Xn α g) := alpha_sq_mul_le_Pbd hα hX0
  have hm2 : Real.sqrt α * Xn α g * Xn α g ≤ Pbd α (Xn α g) := by
    have he : Real.sqrt α * Xn α g * Xn α g = Real.sqrt α * Xn α g ^ 2 := by ring
    rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0
  have hm3 : α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g ≤ Pbd α (Xn α g) := by
    have he : α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g
        = α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3 := by ring
    rw [he]; exact rpow_neg_three_half_mul_cube_le_Pbd hα hX0
  have hprod : |A| * |IP α (Work.Construction.AK α) g|
      ≤ 2 * (C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2))
        * (K₀ * C * Xn α g) :=
    mul_le_mul hA hAK' (abs_nonneg _) (by positivity)
  have hexp : 2 * (C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2))
      * (K₀ * C * Xn α g)
      = 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g) := by ring
  have hsum : α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g ≤ 3 * Pbd α (Xn α g) := by
    linarith [hm1, hm2, hm3]
  have hfin : 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g)
      ≤ 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
    have h1 : 2 * K₀ * C ^ 2 * (α ^ 2 * Xn α g + Real.sqrt α * Xn α g * Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Xn α g * Xn α g * Xn α g)
        ≤ 2 * K₀ * C ^ 2 * (3 * Pbd α (Xn α g)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : 2 * K₀ * C ^ 2 * (3 * Pbd α (Xn α g)) = 6 * K₀ * C ^ 2 * Pbd α (Xn α g) := by
      ring
    linarith [h1, h2.le, h2.ge]
  rw [hsm, abs_mul, abs_neg]
  exact hprod.trans (hexp.le.trans hfin)

/-- **The honest §8 pairing estimate, from the honest row table.**  The honest analogue of
`Open2.pairing_bound_of_rows2_open` (its pairing conjunct), with the row bundle supplied as a
hypothesis rather than derived inside. -/
theorem pairing_bound_of_rowsT (IP : ℝ → Fn → Fn → ℝ) {α₂ Ct Ce Cs : ℝ}
    (hCs : 0 < Cs) (hCe : 0 < Ce)
    (hE : N4ExtraH IP α₂ Ct) (hR : RowsT IP α₂ Ce Cs) :
    ∃ CcN α₄ : ℝ, 0 < CcN ∧ 0 < α₄ ∧ α₄ ≤ α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₄, ∀ {g Φs Φg : Fn},
        CtxT Cs Ce α₂ α g Φs Φg →
        Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Pbd α (Xn α g) := by
  have hCt : 0 < Ct := hE.pos.1
  have hα₂ : 0 < α₂ := hE.pos.2
  set K₀ : ℝ := 4096 * (Ct + 4) with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  have hK₀Ct : Ct ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le]
  have hK₀one : (1 : ℝ) ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le]
  set CC : ℝ := max hR.K₁ (max hR.K₂ hR.K₃) with hCCdef
  have hCCpos : 0 < CC := lt_of_lt_of_le hR.hK₁ (le_max_left _ _)
  have hK1C : hR.K₁ ≤ CC := le_max_left _ _
  have hK2C : hR.K₂ ≤ CC := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3C : hR.K₃ ≤ CC := le_trans (le_max_right _ _) (le_max_right _ _)
  set C₀ : ℝ := 4096 * K₀ * (CC + 1) + 4096 * K₀ / CC with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  have hC₀Ceq : C₀ * CC = 4096 * K₀ * (CC * (CC + 1)) + 4096 * K₀ := by
    rw [hC₀def]; field_simp; try ring
  have hbig : 6 * K₀ * CC ^ 2 + 58 * (K₀ * (CC + 1)) ≤ C₀ * CC := by
    rw [hC₀Ceq]; nlinarith [hK₀pos.le, hCCpos.le]
  have hbigK : K₀ * (CC + 1) ≤ C₀ * CC := by
    nlinarith [hbig, hK₀pos.le, hCCpos.le]
  obtain ⟨α₄μ, hα₄μ_pos, hα₄μ⟩ := mu_le_half (4 * CC) (by positivity)
  refine ⟨C₀ * CC, min α₂ (min α₄μ 1), mul_pos hC₀pos hCCpos,
    lt_min hα₂ (lt_min hα₄μ_pos one_pos), min_le_left _ _, ?_⟩
  intro α hαle g Φs Φg hctx hX74
  have hα : 0 < α := hαle.1
  have hαα₄ : α ≤ min α₂ (min α₄μ 1) := hαle.2
  have hαα₂ : α ≤ α₂ := le_trans hαα₄ (min_le_left _ _)
  have hαμ : α ≤ α₄μ := le_trans hαα₄ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα1 : α ≤ 1 := le_trans hαα₄ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hgC : Work.FTS.ClassC.ClassC α g := hctx.hg
  have hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g := hctx.hco
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  have hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α (Xn α g) := Pbd_nonneg hα.le hX0
  have hsmN0 := PairingT.smoothOpen_pieces_N0 hα hα1 hgC hell hstar
  have hsmN := PairingT.smoothOpen_pieces_N hα hα1 hgC hell hstar
  have hRI : RowInputsTO IP α CC g Φs Φg :=
    rowInputsTO_of_rows hα hα1 hαα₂ hgC hco hell hstar
      (hR.rowsN0 hctx) (hR.rowsN hctx) (hR.rowsAux hctx)
      hK1C hK2C hK3C (hR.hk hctx) (hR.splits hctx) hsmN0 hsmN
  have hblk : BlkCtxO IP α₂ Ct K₀ CC C₀ α g Φs Φg :=
    { hE := hE, hα := hα, hαα₂ := hαα₂, hα1 := hα1, hgC := hgC, hco := hco, hR := hRI,
      hCt := hCt, hK₀pos := hK₀pos, hK₀Ct := hK₀Ct, hK₀one := hK₀one, hC := hCCpos,
      hbigK := hbigK }
  set N0v := Work.Construction.N0 α (Work.Construction.Ftot α g) g with hN0vdef
  set Nv := Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ) with hNvdef
  set μ := Work.Construction.mufunS α N0v Nv g with hμdef
  have hμ4 : |μ| ≤ 4 * CC * (α + α ^ (-(1 : ℝ)) * Xn α g
      + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2) := by
    have h := mu_bound_mul (N0v := N0v) (Nv := Nv) hα hα1 hX0 hCCpos.le hRI.rl0 hRI.rl1 hRI.rl2
    rw [hμdef]
    exact h.trans (le_of_eq (by ring_nf))
  have hμ1 : μ ≠ -1 := by
    intro h
    have hh : |μ| ≤ 1 / 2 :=
      hα₄μ α hα hαμ (Xn α g) hX0 hX74 μ hμ4
    rw [h] at hh
    norm_num at hh
  set A := Work.Construction.mubar N0v Nv with hAdef
  have hAb : |A| ≤ 2 * (CC * (α ^ 2 + Real.sqrt α * Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)) := by
    rw [hAdef]; exact mubar_bound_mul hCCpos.le hRI.rl0 hRI.rl1
  set Ns := Work.Construction.Nstar μ (Work.Construction.lamfun μ) g with hNsdef
  -- the `GoodO`-data of the four blocks
  have hg4 : HQo α 4 g := classC_hqo4 hgC
  have hAKq : GoodO α (Work.Construction.AK α) := hRI.rak.1
  have g1 : GoodO α (fun z θ => -A * Work.Construction.AK α z θ) :=
    goodO_const_mul (-A) hAKq
  have gN0v : GoodO α N0v := hRI.hkN0
  have gNv : GoodO α Nv := hRI.hkN
  have gNstarLam : GoodO α (NstarLam μ g) := by
    rw [show NstarLam μ g = (fun z θ => μ * Work.Spaces.Dz g z θ)
        + (fun z θ => (-μ) * g z θ) from by
      funext z θ; simp only [NstarLam, Pi.add_apply]; ring]
    exact goodO_add (goodO_const_mul μ hRI.hkDz) (goodO_const_mul (-μ) hg4)
  have gNs : GoodO α Ns :=
    goodO_of_eqOn_Qd gNstarLam (fun z θ _ => by
      rw [hNsdef]; exact (hRI.hNs μ hμ1 z θ).symm)
  have gs12 : GoodO α ((fun z θ => -A * Work.Construction.AK α z θ) + N0v) := goodO_add g1 gN0v
  have gs123 : GoodO α ((fun z θ => -A * Work.Construction.AK α z θ) + N0v + Nv) :=
    goodO_add gs12 gNv
  -- the exact split of `gRHS`
  have hgr : Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g
      = (fun z θ => -A * Work.Construction.AK α z θ) + N0v + Nv + Ns := by
    funext z θ
    simp only [Work.Construction.gRHS, Pi.add_apply, hAdef, hN0vdef, hNvdef, hNsdef]
    try ring
  have hIPsplit : IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g) g
      = IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g + IP α Nv g
        + IP α Ns g := by
    rw [hgr]
    exact IPO_add4 hE hαIoc hg4 g1 gN0v gNv gNs gs12 gs123
  -- the four block estimates
  have hAKterm : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g|
      ≤ 6 * K₀ * CC ^ 2 * Pbd α (Xn α g) := AKTerm_boundT hblk hAb
  have hN0term : |IP α N0v g| ≤ 7 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hN0vdef]; exact PairingT.N0Term_boundT hblk
  have hNterm : |IP α Nv g| ≤ 20 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hNvdef]; exact PairingT.NTerm_boundT hblk
  have hNsterm : |IP α Ns g| ≤ 24 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by
    rw [hNsdef]; exact PairingT.NsTerm_boundT hblk hμ1 hμ4
  have hmain : |IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g) g|
      ≤ C₀ * CC * Pbd α (Xn α g) := by
    rw [hIPsplit]
    have htri : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g
        + IP α Nv g + IP α Ns g|
        ≤ |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
          + |IP α Nv g| + |IP α Ns g| := Work.Construction.abs_sum_le_four _ _ _ _
    have hfinal : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
        + |IP α Nv g| + |IP α Ns g| ≤ C₀ * CC * Pbd α (Xn α g) := by
      have h56 : 6 * K₀ * CC ^ 2 * Pbd α (Xn α g)
          + 58 * (K₀ * (CC + 1) * Pbd α (Xn α g)) ≤ C₀ * CC * Pbd α (Xn α g) := by
        have h := mul_le_mul_of_nonneg_right hbig hPbd0
        have he : (6 * K₀ * CC ^ 2 + 58 * (K₀ * (CC + 1))) * Pbd α (Xn α g)
            = 6 * K₀ * CC ^ 2 * Pbd α (Xn α g)
              + 58 * (K₀ * (CC + 1) * Pbd α (Xn α g)) := by ring
        rw [he] at h
        exact h
      linarith [hAKterm, hN0term, hNterm, hNsterm, h56,
        abs_nonneg (IP α (fun z θ => -A * Work.Construction.AK α z θ) g),
        abs_nonneg (IP α N0v g), abs_nonneg (IP α Nv g), abs_nonneg (IP α Ns g)]
    linarith [htri, hfinal]
  simpa only [Work.FTS.Apriori.muOf, Work.FTS.Apriori.rhsPair] using hmain

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rowsHkT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The seven rows of the `N₀`-block

The individual conjuncts of the proof of `EpsZero.ClassCHk.N0Mem`, exposed as a single
private lemma (the union of the seven product rows, each transferred from its open-quadrant
form). -/
private theorem hkMem_N0_rows {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Fn}
    (hg : Work.FTS.ClassC.ClassC α g) :
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) := by
  -- ## the universal product rules
  obtain ⟨_Cp, _hCp, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨_Cw, _hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨_Cang, _hCang, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨_C1, _hC1, hl12⟩ := Work.FTS.OpenPkg.l12H_field
  obtain ⟨_CF, _hCF, hDthFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨_Cdz, _hCdz, hDzFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨_Cw0, _hCw0, hc2mL12FstarW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  -- ## the class-`C` data
  have hsmw : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hm7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hQw : Work.FTS.VocabO.HQo α 4 g := ⟨hsmw, hm4⟩
  have hL12 := hl12 α hα hα1 g hQw hg.l12
  have hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) := hL12.1
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 g z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hg
  have hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hsmw hm5
  have hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  -- ## the factor `A = (3/(2α))·L₁₂(g)`
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  -- ## the factor `B = c2m·L₁₂(g)`
  have hc2msm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hc2mb : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 := by
    intro θ hθ
    have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
    linarith
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) := by
    intro i hi hi4 θ hθ
    have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
      Real.rpow_natCast _ 2] at h
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
    linarith
  have hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 g z) 1000 hc2msm hc2mb hc2mIt hL12sm hL12mem).1
  have hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  have hnegBmem : Work.Spaces.HkMem α 4
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) hBmem
  -- ## the fixed profile atoms
  have hFstarsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hDthFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFstarsm.Dth
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFstarsm.Dz
  have hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
  -- ## row 0: the fixed block
  have hp0 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.NonlinRows.HkMem_N0fix α hα hα1
  -- ## row 1: `N₀₃ᵍ = (1/α)·L₁₂(g)·g`
  have h1eq : Work.FTS.Nonlin.N03g α g
      = fun z θ => (1 / α) * (Work.Construction.L12 g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hp1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) := by
    rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α)
      (hprod α hα hα1 (fun z θ => Work.Construction.L12 g z) g
        ⟨hL12sm, hL12mem⟩ ⟨hsmw, hm4⟩).1
  -- ## row 2: `N₀₄ᵃ = D_θF_* · A`
  have h2eq : Work.FTS.Nonlin.N04aF α g
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) := by
    rw [h2eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      hDthFsm (hDthFstarW α hα hα1).1 ⟨hAsm, hAmem⟩).1
  -- ## row 3: `N₀₄ᵇ = D_θg · A`
  have h3eq : Work.FTS.Nonlin.N04bF α g
      = fun z θ => Work.Spaces.Dth g z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) := by
    rw [h3eq]
    exact (hprod α hα hα1 (Work.Spaces.Dth g)
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩).1
  -- ## row 4: `N₀₅ᵃ = D_zF_* · (-B)`
  have h4eq : Work.FTS.Nonlin.N05aF α g
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * ((-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hp4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) := by
    rw [h4eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z))
      hDzFsm (hDzFstarW α hα hα1).1
      ⟨Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt, hnegBmem⟩).1
  -- ## row 5: `N₀₅ᵇ = -B·D_zg`
  have h5eq : Work.FTS.Nonlin.N05bF α g
      = fun z θ => (-1) * ((Work.Construction.c2m θ * Work.Construction.L12 g z)
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hp5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) := by
    rw [h5eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hprod α hα hα1
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z)
        (Work.Spaces.Dz g) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩).1
  -- ## row 6: `N₀₆ = -c2m·L₁₂(F_*)·D_zg`
  have h6eq : Work.FTS.Nonlin.N06F α g
      = fun z θ => (-1) * ((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hp6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) := by
    rw [h6eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hwprod α hα hα1
        (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
        (Work.Spaces.Dz g) hc2mL12Fsm (hc2mL12FstarW α hα hα1).1
        ⟨hsmw.Dz, hDzw_mem⟩).1
  exact ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6⟩

/-- Every one of the 31 conjuncts of `Work.FTS.OpenPkg.PiecesHk` is `ℋ⁴`-honest on the
class-`C` row context.  Nothing here uses the `IP`-level clauses (`N4Norm'`, `N4ExtraH`). -/
private theorem piecesHk_of_ctx {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Φg : Fn} (hg : Work.FTS.ClassC.ClassC α g)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hkMem_N0_rows hα hα1 hg
  have hm7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 5 (by norm_num) hm7
  have hDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hg.reg hm5
  exact
    { p1 := h1
      p2 := h2
      p3 := h3
      p4 := h4
      p5 := h5
      p6 := h6
      p7 := h7
      p8 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1gg hα hα1 hg hell).hk
      p9 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1gs hα hα1 hg hell).hk
      p10 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1sg hα hα1 hg hstar).hk
      p11 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1ss hα hα1 hstar).hk
      p12 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2gg hα hα1 hg hell).hk
      p13 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2gs hα hα1 hell).hk
      p14 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2sg hα hα1 hg hstar).hk
      p15 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2ss hα hα1 hstar).hk
      p16 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3gg hα hα1 hg hell).hk
      p17 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3gs hα hα1 hell).hk
      p18 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3sg hα hα1 hg hstar).hk
      p19 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3ss hα hα1 hstar).hk
      p20 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4gg hα hα1 hg).hk
      p21 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4gs hα hα1 hg).hk
      p22 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4sg hα hα1 hg).hk
      p23 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4ss hα hα1).hk
      p24 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5gg hα hα1 hg).hk
      p25 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5gs hα hα1 hg).hk
      p26 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5sg hα hα1 hg).hk
      p27 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5ss hα hα1).hk
      pAK := Work.FTS.NonlinRows.HkMem_AK α hα hα1
      pN0 := Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem hα hα1 hg hell
      pN := Work.FTS.StrongEps.EpsZero.ClassCHk.NMem hα hα1 hg hell hstar
      pDz := hDz }

theorem rowsHkT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.OpenPkg.PiecesHk α g Φs Φg := by
  intro α g Φs Φg hctx
  exact piecesHk_of_ctx hctx.hα hctx.hα1 hctx.hg hctx.hell hctx.hs

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

theorem ProfRHSTraces {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W (E W))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  constructor
  · intro z hz
    exact ProfRHSAux.tendsto_profRHS hα hW hell hstar
      { hz := hz
        hquad := ProfRHSAux.eventually_mem_Ioo_left
        gam := (ProfRHSAux.GamTraces hα.1).1
        dth_gam := (ProfRHSAux.GamTraces hα.1).2.2.1
        slot := fun a b hab => (ProfRHSAux.BdryTracesMixedTendsto hα.1 hW.bdry hab hz).1 }
  · intro z hz
    exact ProfRHSAux.tendsto_profRHS hα hW hell hstar
      { hz := hz
        hquad := ProfRHSAux.eventually_mem_Ioo_right
        gam := (ProfRHSAux.GamTraces hα.1).2.1
        dth_gam := (ProfRHSAux.GamTraces hα.1).2.2.2
        slot := fun a b hab => (ProfRHSAux.BdryTracesMixedTendsto hα.1 hW.bdry hab hz).2 }

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWPBounds =====
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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The uniform sup bound of the `L₁₂`-mode -/

/-- **A sup bound for `L₁₂(·)(z)` on the whole domain, from the `ℋ⁴`-size of the profile.**
`|L₁₂ f z| ≤ C |f|_{ℋ⁴}` for every `z ≥ 0`, with a universal `C`: the `ℋ⁴`-Lipschitz property of
`L₁₂(·)(z)` (`Work.FTS.StrongEps.L12.L12_z_lipschitz`, with `C/√(1+z) ≤ C`) applied against the
zero profile. -/
theorem L12_abs_le_Xn : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn,
    Work.FTS.VocabO.HQo α 4 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hkey⟩ := Work.FTS.StrongEps.L12.L12_z_lipschitz
  refine ⟨C, hCpos, fun α hα f hf z hz => ?_⟩
  have hzero_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ _ : ℝ => (0 : ℝ)))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  have hzero : Work.FTS.VocabO.HQo α 4 (fun _ _ : ℝ => (0 : ℝ)) :=
    ⟨hzero_sm, Work.FTS.Galerkin.Inhabit.HkMem_zeroF α 4⟩
  have hdiff : (fun z θ : ℝ => f z θ - 0) = f := by
    funext z θ; rw [sub_zero]
  have h := hkey α hα f (fun _ _ : ℝ => (0 : ℝ)) hf hzero (by rw [hdiff]; exact hf) z hz
  rw [hdiff, Work.FTS.Galerkin.L12_zero_fun z, sub_zero] at h
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hden : 0 < Real.sqrt (1 + z) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + z) := by
    have h1 : (1 : ℝ) ≤ 1 + z := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + z) := Real.sqrt_le_sqrt h1
  have hle : C / Real.sqrt (1 + z) ≤ C := by
    rw [div_le_iff₀ hden]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.sqrt (1 + z) := mul_le_mul_of_nonneg_left hsqrt1 hCpos.le
  calc |Work.Construction.L12 f z| ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α f := h
    _ ≤ C * Work.FTS.Nonlin.Xn α f := mul_le_mul_of_nonneg_right hle hX

/-! ## The four scalar bounds of `epsWP_sup_le_of_classC` -/


/-! ## The sup bound on `epsWP`, from the interface data alone -/


end Work.FTS.StrongEps
end
end
