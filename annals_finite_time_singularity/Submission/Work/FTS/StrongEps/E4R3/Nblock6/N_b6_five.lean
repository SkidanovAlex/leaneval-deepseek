import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWP_semitame_proof
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.mul_WlInf6_HkSq
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.EpsWPSemitame =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/EpsWPSemitame.lean` — OPEN LEAF S2 (research **mid**, ~2–4K lines; RISK)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S2; REVIEW fix F4).
This is the whole level-6 algebra of the right-hand side (all four pieces + `μ` + the linear part)
plus the `HQo 6` honesty of `epsWP` — the `EpsWPBounds` header records it is missing.
**The tame structure is essential**: top order must enter LINEARLY with an `ℋ⁴`-priced
coefficient.  A coefficient like `C(|x|₆)·|x|₇` leaves no `ε` (`ε|x|₇ ≲ |g|₆`) and breaks the
Grönwall.  In the Leibniz terms `D^jA·D^{7−j}x`:
* `j = 0, 1`: sup of the coefficient priced by `M` (`EllPkgGo` + Agmon);
* `2 ≤ j ≤ 3`: Agmon on `A` gives `|A|₅ ≤ Ce|x|₆`;
* `j ≥ 4`: Agmon on `x` gives a quadratic term.
Reuse `H6Row6.pcs` / `NSplit6` / `nsum_split6`, `RowNAgmon`, `coefDataSharp`, `muBdd_of_zeroModes`,
`SupOpenH2` / `ResidPtOfGo` (top-order coefficient).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.pairingBoundT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem pairingBoundT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ct Ce Cs : ℝ} (hCs : 0 < Cs) (hCe : 0 < Ce)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct)
    (hR : Work.FTS.StrongEps.E4R3.N4C.RowsT IP α₂ Ce Cs) :
    ∃ CcN α₄ : ℝ, 0 < CcN ∧ 0 < α₄ ∧ α₄ ≤ α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₄, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
        Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
        Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g) :=
  pairing_bound_of_rowsT IP hCs hCe hE hR

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

theorem N_b6_five : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({16, 17, 18, 19} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
  intro C₀ Ce Cs α hαmem
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  obtain ⟨Cfg, hCfgpos, hfg⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqHkSq
  obtain ⟨Cst, hCstpos, hst⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
  obtain ⟨Cmul, hCmulpos, hmul⟩ := aux.mul_WlInf6_HkSq
  obtain ⟨Kj, hKjpos, hKj⟩ := aux.Fstar_jet_rel
  obtain ⟨CS, hCSpos, hSrad⟩ := aux.SlotSum_Fstar_sq_le
  obtain ⟨Cks, hCkspos, hks⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksDat
  obtain ⟨Bang, hBangpos, hBangint, hBangle⟩ := aux.angBlk_sinSqGam α hαmem
  set K16 : ℝ := Cfg * (C₀ * α ^ 2) ^ 2 + 1 with hK16
  set K17 : ℝ := Cst * α ^ (-(2 : ℝ)) + 1 with hK17
  set K18 : ℝ := Cmul * Cks ^ 2 * α + 1 with hK18
  set K19 : ℝ := Bang * (CS * Kj ^ 4 * α ^ 4) + 1 with hK19
  have hK16nn : 0 < K16 := by rw [hK16]; positivity
  have hK17nn : 0 < K17 := by rw [hK17]; positivity
  have hK18nn : 0 < K18 := by rw [hK18]; positivity
  have hK19nn : 0 < K19 := by rw [hK19]; positivity
  refine ⟨max (max K16 K17) (max K18 K19) + 1, by positivity, ?_⟩
  intro Φs w Φg hw hXw hzero hell hK6 hstar k hk
  have hK16le : K16 ≤ max (max K16 K17) (max K18 K19) + 1 := by
    have h1 : K16 ≤ max K16 K17 := le_max_left _ _
    have h2 : max K16 K17 ≤ max (max K16 K17) (max K18 K19) := le_max_left _ _
    linarith
  have hK17le : K17 ≤ max (max K16 K17) (max K18 K19) + 1 := by
    have h1 : K17 ≤ max K16 K17 := le_max_right _ _
    have h2 : max K16 K17 ≤ max (max K16 K17) (max K18 K19) := le_max_left _ _
    linarith
  have hK18le : K18 ≤ max (max K16 K17) (max K18 K19) + 1 := by
    have h1 : K18 ≤ max K18 K19 := le_max_left _ _
    have h2 : max K18 K19 ≤ max (max K16 K17) (max K18 K19) := le_max_right _ _
    linarith
  have hK19le : K19 ≤ max (max K16 K17) (max K18 K19) + 1 := by
    have h1 : K19 ≤ max K18 K19 := le_max_right _ _
    have h2 : max K18 K19 ≤ max (max K16 K17) (max K18 K19) := le_max_right _ _
    linarith
  have finish : ∀ (k : ℕ) (Kk C : ℝ), 0 < Kk → Kk ≤ max (max K16 K17) (max K18 K19) + 1 →
      C ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ Kk * C →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 7 w)
          + (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    intro k Kk C hKkpos hKkle hC hbound
    have h7nn : 0 ≤ 1 + Work.Spaces.HkSq α 7 w := by
      have := Work.Spaces.HkSq_nonneg α 7 w; linarith
    have hKnn : (0 : ℝ) < max (max K16 K17) (max K18 K19) + 1 := by positivity
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ Kk * C := hbound
      _ ≤ Kk * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := mul_le_mul_of_nonneg_left hC hKkpos.le
      _ ≤ (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          mul_le_mul_of_nonneg_right hKkle (sq_nonneg _)
      _ ≤ (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 7 w)
            + (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
          have h1 : 0 ≤ (max (max K16 K17) (max K18 K19) + 1) * (1 + Work.Spaces.HkSq α 7 w) :=
            mul_nonneg hKnn.le h7nn
          linarith
  have hw6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α w (C₀ * α ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm
      (Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hw hzero) hw.mem hXw
  have key16 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
      ≤ K16 * Work.Spaces.HkSq α 6 w := by
    have h1 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
        = Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2
            * Work.Construction.FK w z * w z θ) := by
      have ha : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
          = Work.Spaces.HkSq α 6 (fun z θ => -((Real.sin θ) ^ 2
              * (Work.Construction.FK w z * w z θ))) :=
        Work.FTS.GalBasis.HkSq_congr_all (a := Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 16)
          (b := fun z θ => -((Real.sin θ) ^ 2 * (Work.Construction.FK w z * w z θ)))
          (fun z θ => by simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; ring) α 6
      rw [ha, Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_neg]
      exact Work.FTS.GalBasis.HkSq_congr_all (a := fun z θ => (Real.sin θ) ^ 2
          * (Work.Construction.FK w z * w z θ))
        (b := fun z θ => Real.sin θ ^ 2 * Work.Construction.FK w z * w z θ)
        (fun z θ => by ring) α 6
    rw [h1, hK16]
    have h2 := hfg α hαmem w (C₀ * α ^ 2) hdat
    refine le_trans h2 ?_
    have hSnn : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have hbase : (0 : ℝ) ≤ (C₀ * α ^ 2) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hCfgpos.le hbase) hSnn, hCfgpos]
  have key17 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
      ≤ K17 * Work.Spaces.HkSq α 6 w := by
    have h1 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
        = Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2
            * Work.Construction.FK w z * Work.Construction.Fstar α z θ) := by
      have ha : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
          = Work.Spaces.HkSq α 6 (fun z θ => -((Real.sin θ) ^ 2
              * (Work.Construction.Fstar α z θ * Work.Construction.FK w z))) :=
        Work.FTS.GalBasis.HkSq_congr_all (a := Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
          (b := fun z θ => -((Real.sin θ) ^ 2 * (Work.Construction.Fstar α z θ
              * Work.Construction.FK w z)))
          (fun z θ => by simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; ring) α 6
      rw [ha, Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_neg]
      exact Work.FTS.GalBasis.HkSq_congr_all (a := fun z θ => (Real.sin θ) ^ 2
          * (Work.Construction.Fstar α z θ * Work.Construction.FK w z))
        (b := fun z θ => Real.sin θ ^ 2 * Work.Construction.FK w z
          * Work.Construction.Fstar α z θ)
        (fun z θ => by ring) α 6
    rw [h1, hK17]
    have h2 := (hst α hαmem w (C₀ * α ^ 2) hdat).2.2.2
    refine le_trans h2 ?_
    have hSnn : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have hp1 : (0 : ℝ) < α ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hα0 _
    nlinarith [mul_nonneg (mul_nonneg hCstpos.le hp1.le) hSnn, hCstpos]
  have key18 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
      ≤ K18 * Work.Spaces.HkSq α 6 w := by
    obtain ⟨-, hYsmooth, -, -, hYWmem, hYWle, -⟩ := hks α hαmem
    have h1 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
        = Work.Spaces.HkSq α 6 (fun z θ => ((Real.sin θ) ^ 2
            * Work.Construction.FK (Work.Construction.Fstar α) z) * w z θ) := by
      have ha : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
          = Work.Spaces.HkSq α 6 (fun z θ => -(((Real.sin θ) ^ 2
              * Work.Construction.FK (Work.Construction.Fstar α) z) * w z θ)) :=
        Work.FTS.GalBasis.HkSq_congr_all (a := Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
          (b := fun z θ => -(((Real.sin θ) ^ 2
              * Work.Construction.FK (Work.Construction.Fstar α) z) * w z θ))
          (fun z θ => by simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]; ring) α 6
      rw [ha, Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_neg]
    rw [h1, hK18]
    have h2 := hmul α hαmem (fun z θ => (Real.sin θ) ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) z) w Cks
        hYsmooth hYWmem hYWle hCkspos.le hw.reg hw6
    refine le_trans h2 ?_
    have hSnn : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have h3 : 0 ≤ Cmul * Cks ^ 2 * α := by positivity
    nlinarith [mul_nonneg h3 hSnn]
  have key19 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 19)
      ≤ K19 := by
    obtain ⟨hSradint, hSradle⟩ := hSrad Kj hKjpos hKj α hαmem
    have hid : ∀ z θ : ℝ, Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 19 z θ
        = (-(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * (α ^ 2 * (Work.FM.Fstar z) ^ 2) := by
      intro z θ
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
      rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα0 hα1]
      simp only [Work.FM.Fstar, Work.Construction.Fstar]
      ring
    have heq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 19)
        = Work.Spaces.HkSq α 6 (fun z θ => (-(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ
            / Work.Spaces.c α) * (α ^ 2 * (Work.FM.Fstar z) ^ 2)) :=
      Work.FTS.GalBasis.HkSq_congr_all hid α 6
    rw [heq, hK19]
    have hsep := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le
      (α := α) (C := fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      (B := fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) hBangint hSradint
    refine le_trans hsep ?_
    have hSlotnn : 0 ≤ (∫ z in Work.Spaces.Iz,
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) :=
      integral_nonneg (fun z => Work.FTS.StrongPersist.SlotSum_nonneg _ z)
    calc (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α
            (fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) θ)
          * (∫ z in Work.Spaces.Iz,
              Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z)
        ≤ Bang * (∫ z in Work.Spaces.Iz,
              Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) :=
          mul_le_mul_of_nonneg_right hBangle hSlotnn
      _ ≤ Bang * (CS * Kj ^ 4 * α ^ 4) := mul_le_mul_of_nonneg_left hSradle hBangpos.le
      _ ≤ Bang * (CS * Kj ^ 4 * α ^ 4) + 1 := by linarith
  have hsix : Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h := Work.Spaces.HkSq_nonneg α 6 w; nlinarith
  have hone : (1 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h := Work.Spaces.HkSq_nonneg α 6 w; nlinarith
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact finish 16 K16 (Work.Spaces.HkSq α 6 w) hK16nn hK16le hsix key16
  · exact finish 17 K17 (Work.Spaces.HkSq α 6 w) hK17nn hK17le hsix key17
  · exact finish 18 K18 (Work.Spaces.HkSq α 6 w) hK18nn hK18le hsix key18
  · exact finish 19 K19 1 hK19nn hK19le hone (by simpa using key19)

end Work.FTS.StrongEps.E4R3.Nblock6
end
