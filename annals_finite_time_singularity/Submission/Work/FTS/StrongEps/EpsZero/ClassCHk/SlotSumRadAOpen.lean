import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

set_option maxHeartbeats 3200000

-- Level-four `HkSq` bounds for the two pieces
-- `NP5b α w = (-1)·(c2m θ · L₁₂(w) z · D_z w z θ)` and
-- `NP6 α w = (-1)·(c2m θ · L₁₂(F_* α) z · D_z w z θ)`
-- of the `N₀`-row (`Work.FTS.StrongPersist.H6Pair6Aux`), priced by `HkSq α 5 w`.
-- Route: verbatim the route of the level-six sibling
-- `...blocks.N0Aux.NP5b_NP6_HkSq6`, with the level-six radial engine `radialMaj6_split`
-- replaced by the level-four `Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4`.
-- Write `NP5b α w = L₁₂(w) z · g z θ` with `g := fun z θ => -c2m θ * D_z w z θ`
-- (transfer by `HkSq_congr_open`), then
-- * `L3Rhs.ang_mul_HkSq_le 4` with `a := c2m`, `B := Cc` (hypotheses: `c2mJets`) gives
--   `HkMem α 4 g` and `HkSq α 4 g ≤ Cang·Cc²·HkSq α 4 (Dz w) ≤ Cang·Cc²·HkSq α 5 w`
--   (`H6Aux.HkSq_Dz_le_succ'`; `HkMem α 5 w` from `ClassC`);
-- * `radialMaj4` with `X := L₁₂w`, `B := CL·Xn α w` (`H6Pair6Aux.L12Sup4`,
--   `ContDiffOn ℝ 6 (L₁₂w) (Ioi 0)` from `UopHk.contDiffOn_L12_k`) gives
--   `HkSq α 4 (NP5b α w) ≤ (Maj4C+1)·(CL·Xn α w)²·HkSq α 4 g ≤ (Maj4C+1)CL²C₀²α⁴·Cang Cc²·HkSq α 5 w`.
-- * For `NP6`: the same `g`, but `X := fun z => L₁₂(F_* α) z`, whose `D_z`-jets of order `≤ 4`
--   are bounded either by the `α`-free constant `Kφ` of
--   `...blocks.N0Aux.NP5b_NP6_HkSq6.l12Fstar_dzdIter_uniform` (import that module) or by
--   `H6Pair6Aux.L12Sup4` with `B := CL·Xn α w`; `ContDiffOn ℝ 6 (L₁₂(F_* α)) (Ioi 0)` follows
--   from `Construction.L12_Fstar_eq` (`L₁₂(F_*) y = 2α/(1+y)` for `y > -1`) by
--   `ContDiffOn.congr`.
-- The "w vanishes off the open quadrant" hypothesis is NOT needed here.
theorem NP5b_NP6_HkSq4 (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 5 w) ∧
    Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Cc, hCcpos, hCcsm, hCcabs, hCcjet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨Kφ, hKφpos, hKφ⟩ := l12Fstar_dzdIter_uniform
  have hMajpos : 0 < Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1 := by
    have := Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C_pos
    linarith
  have hK1pos : 0 < (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1 := by positivity
  have hK2pos : 0 < (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * Kφ ^ 2 * Cang * Cc ^ 2 + 1 := by positivity
  refine ⟨max ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1)
      ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
        * Kφ ^ 2 * Cang * Cc ^ 2 + 1), lt_max_of_lt_left hK1pos, ?_⟩
  intro α hαI w hcls hXw
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsmw.Dz
  have hm4Dz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  have hDz4 : Work.Spaces.HkSq α 4 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 4 hsmw hm5
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hH : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ hα0.le hα1
  -- ## the angular multiplier `c₂ₘ` at level `4`
  have hCcjet4 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi4 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  obtain ⟨hfa_mem, hfa_bd⟩ := hCang α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet4 (Work.Spaces.Dz w) hsmDz hm4Dz
  -- ## the honest field `f = -c₂ₘ · D_z w`
  set f : ℝ → ℝ → ℝ := fun z θ => (-1) * (Work.Construction.c2m θ * Work.Spaces.Dz w z θ)
    with hfdef
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hfdef]
    exact Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
          Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m) hsmDz)
  have hfmem : Work.Spaces.HkMem α 4 f := by
    rw [hfdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1) hfa_mem
  have hS4f : Work.Spaces.HkSq α 4 f ≤ Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w := by
    have hval : Work.Spaces.HkSq α 4 f
        = Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfa_bd.trans (mul_le_mul_of_nonneg_left hDz4 (by positivity))
  -- ## the radial data of `radialMaj4`
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h10 : ContDiffOn ℝ 10 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
      have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 10 w hα0 hα1 hsmw hcls.mem10
        (by norm_num)
      refine h.congr (fun z _ => ?_)
      exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) z
    exact h10.of_le (by exact_mod_cast (by norm_num : 6 ≤ 10))
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hCL α w hα0 hα1 hsmw hm6 hcls.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCLpos.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  -- ## `NP5b`
  have heq5b : Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w
      = fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ := by
    rw [hfdef]
    funext z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
    ring
  have hmain5b :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4 (α := α)
      (B := CL * Work.FTS.Nonlin.Xn α w) (X := fun z => Work.Construction.L12 w z)
      (f := f) hCB hLcd hfsm hfmem hjet
  have hbnd5b : Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
      ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
          * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [heq5b]
    calc Work.Spaces.HkSq α 4 (fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ)
        ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * (CL * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 4 f := hmain5b
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqCL hMajpos.le) hS4f
            (Work.Spaces.HkSq_nonneg α 4 f) (by positivity)
      _ = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by ring
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : α ^ 4 * Work.Spaces.HkSq α 5 w ≤ 1 * Work.Spaces.HkSq α 5 w :=
            mul_le_mul_of_nonneg_right hα4le h5w
          linarith
      _ ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
          have hc : (0 : ℝ) ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
              * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 := by positivity
          nlinarith [hc, hH]
  -- ## `NP6`
  have hL12Fcd : ContDiffOn ℝ 6
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ 6 (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
    have hden : ContDiffOn ℝ 6 (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add contDiffOn_id
    have hbase : ContDiffOn ℝ 6 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) :=
      hnum.div hden (fun z hz => by
        have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
    exact hbase.congr (fun z hz =>
      Work.Construction.L12_Fstar_eq hα0 hα1 (le_of_lt (Set.mem_Ioi.mp hz)))
  have hFjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j
        (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
    fun j hj z hz => hKφ α hαI j (by omega) z hz
  have heq6 : Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w
      = fun z θ => (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          * f z θ := by
    rw [hfdef]
    funext z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6, Work.FTS.StrongPersist.H6Pair6Aux.NA6]
    ring
  have hmain6 :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4 (α := α) (B := Kφ)
      (X := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (f := f) hKφpos.le hL12Fcd hfsm hfmem hFjet
  have hbnd6 : Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
      ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
          * Kφ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [heq6]
    calc Work.Spaces.HkSq α 4 (fun z θ =>
            (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ)
        ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Work.Spaces.HkSq α 4 f := hmain6
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left hS4f (by positivity)
      _ = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w := by ring
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
          have hc : (0 : ℝ) ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
              * Kφ ^ 2 * Cang * Cc ^ 2 := by positivity
          nlinarith [hc, hH]
  exact ⟨hbnd5b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH),
    hbnd6.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.AesmRestrict =====
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

set_option autoImplicit false

/-! ## Clamping turns restricted measurability into full measurability -/


/-! ## The horizon-restricted diagonal-energy derivative -/



end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem N0Mem {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {w Φg : Work.FTS.Galerkin.Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) := by
  -- `N₀` only involves `w` and `F_*`; the elliptic package `hell` is not needed.
  have _hell := hell
  -- ## the universal constants of the product rules
  obtain ⟨Cp, _hCppos, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, _hCwpos, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cang, _hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨C1, _hC1pos, hl12⟩ := Work.FTS.OpenPkg.l12H_field
  obtain ⟨_CF, _hCFpos, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨_Cdz, _hCdzpos, hDzFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨_Cw0, _hCw0pos, hc2mL12FstarW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  -- ## the class-`C` data
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := w) hsmw 4 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := w) hsmw 5 (by norm_num) hm7
  have hQw : Work.FTS.VocabO.HQo α 4 w := ⟨hsmw, hm4⟩
  -- ## `L₁₂(w)`
  have hL12 := hl12 α hα hα1 w hQw hw.l12
  have hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) := hL12.1
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hw
  -- ## `D_z w`, `D_θ w`
  have hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  have hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w) :=
    Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hsmw hm5
  -- ## the factor `A = (3/(2α))·L₁₂(w)`
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  -- ## the factor `B = c2m·L₁₂(w)` (via the angular multiplication rule)
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
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 w z) 1000 hc2msm hc2mb hc2mIt hL12sm hL12mem).1
  have hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  have hnegBmem : Work.Spaces.HkMem α 4
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) hBmem
  have hnegBsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt
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
  have hp0sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  -- ## row 1: `N₀₃ᵍ = (1/α)·L₁₂(w)·w`
  have h1eq : Work.FTS.Nonlin.N03g α w
      = fun z θ => (1 / α) * (Work.Construction.L12 w z * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hp1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α)
      (hprod α hα hα1 (fun z θ => Work.Construction.L12 w z) w
        ⟨hL12sm, hL12mem⟩ ⟨hsmw, hm4⟩).1
  have hp1sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  -- ## row 2: `N₀₄ᵃ = D_θF_* · A`
  have h2eq : Work.FTS.Nonlin.N04aF α w
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      hDthFsm (hFstarW α hα hα1).1 ⟨hAsm, hAmem⟩).1
  have hp2sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDthFsm hAsm
  -- ## row 3: `N₀₄ᵇ = D_θw · A`
  have h3eq : Work.FTS.Nonlin.N04bF α w
      = fun z θ => Work.Spaces.Dth w z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact (hprod α hα hα1 (Work.Spaces.Dth w)
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩).1
  have hp3sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hAsm
  -- ## row 4: `N₀₅ᵃ = D_zF_* · (-B)`
  have h4eq : Work.FTS.Nonlin.N05aF α w
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * ((-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hp4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z))
      hDzFsm (hDzFstarW α hα hα1).1 ⟨hnegBsm, hnegBmem⟩).1
  have hp4sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDzFsm hnegBsm
  -- ## row 5: `N₀₅ᵇ = -B·D_zw`
  have h5eq : Work.FTS.Nonlin.N05bF α w
      = fun z θ => (-1) * ((Work.Construction.c2m θ * Work.Construction.L12 w z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hp5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hprod α hα hα1
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)
        (Work.Spaces.Dz w) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩).1
  have hp5sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hBsmt hsmw.Dz)
  -- ## row 6: `N₀₆ = -c2m·L₁₂(F_*)·D_zw`
  have h6eq : Work.FTS.Nonlin.N06F α w
      = fun z θ => (-1) * ((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hp6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hwprod α hα hα1
        (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
        (Work.Spaces.Dz w) hc2mL12Fsm (hc2mL12FstarW α hα hα1).1
        ⟨hsmw.Dz, hDzw_mem⟩).1
  have hp6sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mL12Fsm hsmw.Dz)
  -- ## the additive closure of `ℋ⁴`-honesty
  have hadd : ∀ (u v : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 4 u →
      Work.Spaces.HkMem α 4 v → Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) := by
    intro u v hu hv hum hvm
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (hu.forall 4) (hv.forall 4) hum hvm
  have haddsm : ∀ (u v : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen u →
      Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ + v z θ) := by
    intro u v hu hv
    exact Work.FTS.NonlinRows.smoothOpen_add hu hv
  -- ## the nested assembly
  have h56 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N05bF α w z θ
      + Work.FTS.Nonlin.N06F α w z θ) :=
    hadd (Work.FTS.Nonlin.N05bF α w) (Work.FTS.Nonlin.N06F α w) hp5sm hp6sm hp5 hp6
  have h56sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.Nonlin.N05bF α w z θ
      + Work.FTS.Nonlin.N06F α w z θ) :=
    haddsm (Work.FTS.Nonlin.N05bF α w) (Work.FTS.Nonlin.N06F α w) hp5sm hp6sm
  have h456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    hadd (Work.FTS.Nonlin.N05aF α w)
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
      hp4sm h56sm hp4 h56
  have h456sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    haddsm (Work.FTS.Nonlin.N05aF α w)
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
      hp4sm h56sm
  have h3456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
      + (Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    hadd (Work.FTS.Nonlin.N04bF α w)
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
      hp3sm h456sm hp3 h456
  have h3456sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    haddsm (Work.FTS.Nonlin.N04bF α w)
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
      hp3sm h456sm
  have h23456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
      + (Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    hadd (Work.FTS.Nonlin.N04aF α w)
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
      hp2sm h3456sm hp2 h3456
  have h23456sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    haddsm (Work.FTS.Nonlin.N04aF α w)
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
      hp2sm h3456sm
  have h123456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N03g α w z θ
      + (Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) :=
    hadd (Work.FTS.Nonlin.N03g α w)
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
      hp1sm h23456sm hp1 h23456
  have hsum : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N0fix α z θ
      + (Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ
                + Work.FTS.Nonlin.N06F α w z θ)))))) :=
    hadd (Work.FTS.Nonlin.N0fix α)
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))
      hp0sm
      (haddsm (Work.FTS.Nonlin.N03g α w)
        (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
        hp1sm h23456sm)
      hp0 h123456
  -- ## transfer from the open quadrant to the domain
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsum ?_
  intro z hz θ hθ
  exact (Work.FTS.StrongEps.ClassCRHS.N0_split_open hα hsmw z θ ⟨hz, hθ⟩).symm

end Work.FTS.StrongEps.EpsZero.ClassCHk
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open Work.Spaces (HkMem HkSq HkNorm)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The projector constant at level six, without the `H6Adm` package.**
`C₀f = L₁₂(Transport f)(0) = L12f (Transport f) 0` is bounded by `HkNorm α 4 f`
(`L3Aux.Transport_L12_zero_le`, which needs only `HkMem α 4 f` — no smoothness, no vanishing),
hence by `HkSq α 6 f` for data with order-seven honesty.  This is
`H6Aux.Alt_C0_sq_le_HkSq6` with the `H6Adm` hypothesis replaced by its `SmoothOpen` field, which
is the only part of `H6Adm` that that proof uses. -/
theorem WeakC0_sq_le_HkSq6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₀, _hC₀, hb⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro α hαIoc f hsm hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have habs : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0|
      ≤ C₀ * Work.Spaces.HkNorm α 4 f := hb α f hα hα1 hmem4
  have hmono : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 6 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6
  have h4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      = |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ^ 2 := by rw [sq_abs]
    _ ≤ (C₀ * Work.Spaces.HkNorm α 4 f) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C₀ ^ 2 * Work.Spaces.HkSq α 4 f := by
        rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt h4]
    _ ≤ C₀ ^ 2 * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

theorem SlotSumRadAOpen :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Construction.L12 f 0 = 0 →
        MeasureTheory.IntegrableOn
          (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Czop, hCzop, hzopb⟩ := Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  obtain ⟨Cc0, hCc0pos, hC0b⟩ := WeakC0_sq_le_HkSq6
  obtain ⟨Cb, hCbpos, hBb⟩ := Work.FTS.StrongPersist.H6Aux.Alt_slotSum_ampB_div_le
  obtain ⟨KA, hKA, hKAb⟩ := Work.FTS.StrongPersist.H6Aux.Alt_ampA_dzdIter_bound6
  refine ⟨2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb), ?_, ?_⟩
  · have h1 : 0 < Czop * (1 + KA) ^ 2 * C₁ := by
      have hK1 : 0 < 1 + KA := by linarith
      exact mul_pos (mul_pos hCzop (pow_pos hK1 2)) hC₁pos
    have h2 : 0 < Cc0 * Cb := mul_pos hCc0pos hCbpos
    linarith
  intro α hαIoc f hsm hmem7 hl12
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z')
        = fun z' => Work.Construction.L12 f z' := rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).mul hu6
  -- abbreviations
  set u : ℝ → ℝ := fun z' => Work.Coercivity.L12f f z' with hu
  set C0 : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hC0
  set S1 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * u z') z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS1
  set S2 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS2
  set Su : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2 with hSu
  set S3 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS3
  -- `L₁₂f`-slots: integrability and bound
  have hL12i := hC₁b α hα hα1 f hsm hmem6 hl12
  have hExp_eq : (fun z => ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2) = Su := by
    rw [hSu, hu]
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
    rfl
  have hIzIoi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hIoiIz : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))
  have hUint : MeasureTheory.IntegrableOn Su (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hL12i.1
    rw [hExp_eq] at h2
    exact h2.congr_set_ae hIoiIz
  have hUbd : (∫ z in Set.Ioi (0 : ℝ), Su z) ≤ C₁ * Work.Spaces.HkSq α 6 f := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 6 f := hL12i.2
    rw [hExp_eq] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the z-multiplier bound
  have hZp : ∀ z ∈ Set.Ioi (0 : ℝ), S1 z ≤ Czop * (1 + KA) ^ 2 * Su z := by
    intro z hz
    have h := hzopb (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z') u KA hKA
      (fun j hj z' hz' => hKAb α hαIoc j hj z' hz')
      (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1) hu6 z hz
    rwa [hS1, hSu]
  have hS1nn : ∀ z, 0 ≤ S1 z := by
    intro z
    rw [hS1]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : ∀ z, 0 ≤ S2 z := by
    intro z
    rw [hS2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS3nn : ∀ z, 0 ≤ S3 z := by
    intro z
    rw [hS3]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS1int : MeasureTheory.IntegrableOn S1 (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (hUint.const_mul (Czop * (1 + KA) ^ 2)) ?_ ?_
    · rw [hS1]
      exact (Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 6)
        hA6).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hS1nn z)]
      exact hZp z hz
  have hS1bd : (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ (Czop * (1 + KA) ^ 2) * (∫ z in Set.Ioi (0 : ℝ), Su z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hS1nn) (hUint.const_mul (Czop * (1 + KA) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hZp)
    rwa [MeasureTheory.integral_const_mul] at h
  have hS2int : MeasureTheory.IntegrableOn S2 (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := (hBb α hαIoc).1
    rw [← hS2] at h2
    exact h2.congr_set_ae hIoiIz
  have hS2bd : (∫ z in Set.Ioi (0 : ℝ), S2 z) ≤ Cb := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ Cb := (hBb α hαIoc).2
    rw [← hS2] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the pointwise majorant
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), S3 z ≤ 2 * S1 z + (2 * C0 ^ 2) * S2 z := by
    intro z hz
    rw [hS3, hS1, hS2, hC0]
    simp only
    rw [← Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq
      (Work.FTS.CoercivityFix.Transfer.radA α f) z]
    exact Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_radA_ptwise hα hα1 f hsm hmem7 hz
  have hMono : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hS3nn)
      ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hSplit : (∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
        + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := by
    rw [MeasureTheory.integral_add (hS1int.const_mul 2) (hS2int.const_mul (2 * C0 ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hC0sq : C0 ^ 2 ≤ Cc0 * Work.Spaces.HkSq α 6 f := by
    rw [hC0]
    exact hC0b α hαIoc f hsm hmem7
  have hCz : 0 ≤ Czop * (1 + KA) ^ 2 := mul_nonneg hCzop.le (sq_nonneg _)
  have hS2nnint : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S2 z := integral_nonneg hS2nn
  have hstep1 : 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact hS1bd.trans (mul_le_mul_of_nonneg_left hUbd hCz)
  have hstep2 : (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z)
      ≤ (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := by
    have hb0 : 0 ≤ 2 * (Cc0 * Work.Spaces.HkSq α 6 f) :=
      le_trans (by positivity)
        (mul_le_mul_of_nonneg_left hC0sq (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) hS2bd
      hS2nnint hb0
  have hchain : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
    calc (∫ z in Set.Ioi (0 : ℝ), S3 z)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) := hMono
      _ = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
            + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := hSplit
      _ ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f))
            + (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := add_le_add hstep1 hstep2
      _ = (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
          ring
  have hS3_eq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f)
      = S3 := by
    rw [hS3]
    funext z
    exact Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq _ z
  refine ⟨?_, ?_⟩
  · have h2 : MeasureTheory.IntegrableOn S3 (Set.Ioi (0 : ℝ)) := by
      refine Integrable.mono' ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2))) ?_ ?_
      · rw [hS3]
        exact (Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 6)
          (Work.FTS.StrongPersist.H6Aux.contDiffOn_six_radA hα hα1 hsm hmem7)
          ).aestronglyMeasurable measurableSet_Ioi
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hS3nn z)]
        exact hpt z hz
    have h3 : MeasureTheory.IntegrableOn S3 Work.Spaces.Iz := h2.congr_set_ae hIzIoi
    rwa [← hS3_eq] at h3
  · have h2 : (∫ z in Work.Spaces.Iz, S3 z)
        ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
      rw [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm]
      exact hchain
    rwa [← hS3_eq] at h2

end Work.FTS.StrongEps.EpsZero.ClassCHk
end
end
