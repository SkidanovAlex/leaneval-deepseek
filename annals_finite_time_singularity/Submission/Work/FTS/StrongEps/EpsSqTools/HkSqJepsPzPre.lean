import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero
import Submission.Work.FTS.StrongEps.H5.HkMemXnLGammaT5
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.radA_slotSum_le_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The radial slot sums

For a function `u : ℝ → ℝ` of the radial variable put

  `slotSumN m u = ∑_{j = 0}^{m} (D_z^j u)² w²`,

the `(m+1)`-term radial slot sum of `u`.  The lemma proved below controls
`slotSumN n (radA α f)` for `n ≤ 3` by the `n`-slot sum of `L₁₂ f` (a hypothesis) and the
five-slot sum of `ampB α` (a fixed constant). -/

/-- The `(m+1)`-term radial slot sum `∑_{j ≤ m} (D_z^j u)² w²`. -/
private abbrev slotSumN (m : ℕ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∑ j ∈ Finset.range (m + 1),
    (Work.Elliptic.DzdIter j u z) ^ 2 * (Work.Spaces.w z) ^ 2

private lemma slotSumN_eq (m : ℕ) (u : ℝ → ℝ) :
    slotSumN m u = fun z => ∑ j ∈ Finset.range (m + 1),
      (Work.Elliptic.DzdIter j u z) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

private lemma slotSumN_apply (m : ℕ) (u : ℝ → ℝ) (z : ℝ) :
    slotSumN m u z = ∑ j ∈ Finset.range (m + 1),
      (Work.Elliptic.DzdIter j u z) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

private lemma slotSumN_nonneg (m : ℕ) (u : ℝ → ℝ) (z : ℝ) : 0 ≤ slotSumN m u z := by
  rw [slotSumN_apply]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The numerical coefficient of the `q`-th slot, summed over `q ≤ n ≤ 3`, is at most
`2048 K²`. -/
private lemma coeff_sum_le (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (hn : n ≤ 3) :
    (∑ q ∈ Finset.range (n + 1), 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1))
      ≤ 2048 * K ^ 2 := by
  have hterm : ∀ q ∈ Finset.range (n + 1),
      2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) ≤ 512 * K ^ 2 := by
    intro q hq
    have hq3 : q ≤ 3 := by
      have := Finset.mem_range.mp hq
      omega
    have h2 : (2 : ℝ) ^ q ≤ 8 := by
      calc (2 : ℝ) ^ q ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hq3
        _ = 8 := by norm_num
    have hKq0 : 0 ≤ K * 2 ^ q := mul_nonneg hK (by positivity)
    have hKq : K * 2 ^ q ≤ K * 8 := mul_le_mul_of_nonneg_left h2 hK
    have hsq : (K * 2 ^ q) ^ 2 ≤ (K * 8) ^ 2 := pow_le_pow_left₀ hKq0 hKq 2
    have hq4 : (q : ℝ) + 1 ≤ 4 := by
      have hq3' : (q : ℝ) ≤ 3 := by exact_mod_cast hq3
      linarith
    calc 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1)
        ≤ 2 * (K * 8) ^ 2 * 4 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hq4
            (by positivity) (by positivity)
      _ = 512 * K ^ 2 := by ring
  calc (∑ q ∈ Finset.range (n + 1), 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1))
      ≤ (Finset.range (n + 1)).card • (512 * K ^ 2) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((n : ℝ) + 1) * (512 * K ^ 2) := by
        rw [Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2048 * K ^ 2 := by
        have hn4 : ((n : ℝ) + 1) ≤ 4 := by
          have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast hn
          linarith
        nlinarith [sq_nonneg K]

theorem radA_slotSum_le_O
    (hL12 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α n f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨C1, hC1pos, hL12b⟩ := hL12
  obtain ⟨K, hKnn, hKbd6⟩ := Work.FTS.StrongPersist.H6Aux.Alt_ampA_dzdIter_bound6
  obtain ⟨Kb, hKbpos, hKbBd⟩ := Work.FTS.GalFields.Norm.RadA4.ampB_slotSum5_bound
  refine ⟨2048 * K ^ 2 * C1 + 12800 * Kb + 1, ?_, ?_⟩
  · have h1 : 0 ≤ 2048 * K ^ 2 * C1 := by positivity
    have h2 : 0 < 12800 * Kb := by positivity
    linarith
  intro α hα hα1 f hcoer n hn
  -- ### unpacking the class
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hcoer.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hcoer.1.2.1
  have h0 : Work.Construction.L12 f 0 = 0 := hcoer.2.2.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm n (by omega) hmem5
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  -- ### regularity of the `z∂_z`-iterates of `L₁₂ f`
  obtain ⟨hL12cont, hL12diff⟩ :=
    Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open α hα hα1 f hsm hmem4 h0
  have hAdiff :=
    Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open α hα hα1 f hL12diff
  have hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
    fun b hb z hz => hKbd6 α hαIoc b (by omega) z hz
  -- ### the hypothesis `hL12` at `(α, f, n)`
  obtain ⟨hSu_int, hSu_bd⟩ := hL12b α hαIoc f hsm hmem4 h0 n hn
  have hSu_int' : MeasureTheory.IntegrableOn (slotSumN n (Work.Coercivity.L12f f))
      Work.Spaces.Iz := by
    simpa only [slotSumN_eq] using hSu_int
  have hSu_bd' : (∫ z in Work.Spaces.Iz, slotSumN n (Work.Coercivity.L12f f) z)
      ≤ C1 * Work.Spaces.HkSq α n f := by
    simpa only [slotSumN_eq] using hSu_bd
  -- ### the `ampB`-slot sum: integrability and bound
  have hSb_int : MeasureTheory.IntegrableOn (slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α))
      Work.Spaces.Iz := by
    have hcoeff : ∀ j ≤ 4, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2
    show MeasureTheory.Integrable (fun z : ℝ => ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz)
    exact MeasureTheory.integrable_finsetSum _ (fun j hj =>
      hcoeff j (by have := Finset.mem_range.mp hj; omega))
  have hSb_bd : (∫ z in Work.Spaces.Iz,
      slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z) ≤ Kb := by
    simpa only [slotSumN_apply] using hKbBd α hα hα1
  -- ### the projector constant `L₁₂(Transport f)(0)`
  have hreg2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_mono (by norm_num) hcoer.1
  have hC0sq : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ 64 * Work.Spaces.HkSq α n f := by
    have h1 : (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Coercivity.Ef f :=
      Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_Ef_O α hα hα1 hsm hreg2
        (Work.FTS.StrongEps.EpsE4Thr.IntPkg_O hα hreg2)
    have h2 : Work.Coercivity.Ef f ≤ Work.Spaces.HkSq α n f :=
      Work.FTS.CoercivityFix.Transfer.E1Norm.Ef_le_HkSq α n hmemn
    have h3 : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        = (Work.Coercivity.C0 f) ^ 2 := rfl
    rw [h3]
    linarith
  -- ### the pointwise estimate
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f) z
        ≤ (2048 * K ^ 2) * slotSumN n (Work.Coercivity.L12f f) z
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
    intro z hz
    have hper : ∀ q ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2
          ≤ 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1)
              * slotSumN n (Work.Coercivity.L12f f) z
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := by
      intro q hq
      have hqn : q ≤ n := by
        have := Finset.mem_range.mp hq
        omega
      have hq4 : q ≤ 4 := by omega
      have hraw := Work.FTS.StrongEps.EpsRLX.RadBound.radA_iter_sq_le α hα hα1 f hL12diff
        hAdiff hKnn hKbd q hq4 z hz
      have hSL : (∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) ≤ slotSumN n (Work.Coercivity.L12f f) z := by
        rw [slotSumN_apply]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (by
            have := Finset.mem_range.mp hx
            omega))
          (fun x _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hcoef : 0 ≤ 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) := by positivity
      calc (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2
          ≤ 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1), (Work.Elliptic.DzdIter c
                  (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := hraw
        _ ≤ 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1)
              * slotSumN n (Work.Coercivity.L12f f) z
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hSL hcoef) le_rfl
    calc slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = ∑ q ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter q
            (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2 := slotSumN_apply n _ z
      _ ≤ ∑ q ∈ Finset.range (n + 1), (2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1)
              * slotSumN n (Work.Coercivity.L12f f) z
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)) := Finset.sum_le_sum hper
      _ = (∑ q ∈ Finset.range (n + 1), 2 * (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1))
              * slotSumN n (Work.Coercivity.L12f f) z
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * (∑ q ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter q
                  (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (2048 * K ^ 2) * slotSumN n (Work.Coercivity.L12f f) z
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right (coeff_sum_le K hKnn n hn)
              (slotSumN_nonneg n _ z)
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [slotSumN_apply]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun x hx => Finset.mem_range.mpr (by
                have := Finset.mem_range.mp hx
                omega))
              (fun x _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- ### a.e. strong measurability of the target slot sum
  have hIzIoi : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  have hradA_C : ContDiffOn ℝ (n : WithTop ℕ∞)
      (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
    have hL12_C4 : ContDiffOn ℝ (4 : WithTop ℕ∞) (Work.Coercivity.L12f f)
        (Set.Ioi (0 : ℝ)) := by
      have hfun : Work.Coercivity.L12f f = Work.Elliptic.L12 f := by
        funext z
        show Work.FM.L12 Work.Spaces.K f z = Work.Elliptic.L12 f z
        rw [Work.Elliptic.L12_eq_FM]
        rfl
      rw [hfun]
      exact Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem4 (by norm_num)
    have hAB4 : ContDiffOn ℝ (4 : WithTop ℕ∞)
        (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi 0) :=
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α).of_le (by norm_num)
    have hBB4 : ContDiffOn ℝ (4 : WithTop ℕ∞)
        (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi 0) :=
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α).of_le (by norm_num)
    have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
        = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * Work.FTS.CoercivityFix.Transfer.ampB α z
          + -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) := by
      funext z
      simp only [Work.FTS.CoercivityFix.Transfer.radA, Work.FTS.CoercivityFix.Transfer.ampA,
        Work.FTS.CoercivityFix.Transfer.ampB]
      ring
    rw [hfun]
    exact ((ContDiffOn.mul (contDiffOn_const (c := Work.Coercivity.L12f
        (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) (s := Set.Ioi (0 : ℝ))
        (𝕜 := ℝ) (n := (4 : WithTop ℕ∞))) hBB4).add
        ((hAB4.mul hL12_C4).neg)).of_le (by exact_mod_cast (show n ≤ 4 by omega))
  have hT_aesm : AEStronglyMeasurable
      (slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hIzIoi]
    have hcont := Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum hradA_C
    simpa only [slotSumN_eq] using hcont.aestronglyMeasurable measurableSet_Ioi
  have hpt_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f) z
        ≤ (2048 * K ^ 2) * slotSumN n (Work.Coercivity.L12f f) z
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    exact hpt z (lt_of_le_of_ne hzI (Ne.symm hz0))
  -- ### integrability of the majorant and of the target
  have hmaj_int : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (2048 * K ^ 2) * slotSumN n (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z) Work.Spaces.Iz :=
    (hSu_int'.const_mul _).add (hSb_int.const_mul _)
  have hT_int : MeasureTheory.IntegrableOn
      (slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f)) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hmaj_int hT_aesm ?_
    filter_upwards [hpt_ae] with z hz
    rw [Real.norm_of_nonneg (slotSumN_nonneg n _ z)]
    exact hz
  -- ### the integral estimate
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => slotSumN_nonneg n _ z) hmaj_int hpt_ae
  rw [MeasureTheory.integral_add (hSu_int'.const_mul _) (hSb_int.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  have hSb_bd' : (∫ z in Work.Spaces.Iz,
      slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z) ≤ Kb := hSb_bd
  have hB_le : 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) ^ 2) ≤ 12800 * Work.Spaces.HkSq α n f := by
    have hc : 1 / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hc2 : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
      rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
      nlinarith
    calc 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
            / Work.Spaces.c α) ^ 2)
        = 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
            * (1 / Work.Spaces.c α) ^ 2) := by ring
      _ ≤ 2 * ((64 * Work.Spaces.HkSq α n f) * 100) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul hC0sq hc2
            (by positivity : (0:ℝ) ≤ (1 / Work.Spaces.c α) ^ 2)
            (by
              have := Work.Spaces.HkSq_nonneg α n f
              positivity)
      _ = 12800 * Work.Spaces.HkSq α n f := by ring
  have hstep1 : (2048 * K ^ 2) * (∫ z in Work.Spaces.Iz,
        slotSumN n (Work.Coercivity.L12f f) z)
      ≤ (2048 * K ^ 2) * (C1 * Work.Spaces.HkSq α n f) :=
    mul_le_mul_of_nonneg_left hSu_bd' (by positivity)
  have hstep2 : 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
        slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      ≤ (12800 * Work.Spaces.HkSq α n f) * Kb :=
    mul_le_mul hB_le hSb_bd' (MeasureTheory.integral_nonneg fun z => slotSumN_nonneg 4 _ z)
      (by
        have := Work.Spaces.HkSq_nonneg α n f
        positivity)
  have hfinal : (2048 * K ^ 2) * (C1 * Work.Spaces.HkSq α n f)
        + (12800 * Work.Spaces.HkSq α n f) * Kb
      ≤ (2048 * K ^ 2 * C1 + 12800 * Kb + 1)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hH : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
    have hD : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
      Work.Spaces.HkSq_nonneg α n _
    have e1 : 0 ≤ (2048 * K ^ 2) * C1 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
      mul_nonneg (mul_nonneg (by positivity) (le_of_lt hC1pos)) hD
    have e2 : 0 ≤ (12800 * Kb) * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hKbpos)) hD
    have e3 : (2048 * K ^ 2 * C1 + 12800 * Kb + 1)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        = (2048 * K ^ 2) * (C1 * Work.Spaces.HkSq α n f)
          + (12800 * Work.Spaces.HkSq α n f) * Kb
          + ((2048 * K ^ 2) * C1 * Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + (12800 * Kb) * Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
      ring
    linarith
  refine ⟨?_, ?_⟩
  · simpa only [slotSumN_eq] using hT_int
  · have hbound : (∫ z in Work.Spaces.Iz,
        slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ (2048 * K ^ 2 * C1 + 12800 * Kb + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
      calc (∫ z in Work.Spaces.Iz,
            slotSumN n (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ (2048 * K ^ 2) * (∫ z in Work.Spaces.Iz,
                slotSumN n (Work.Coercivity.L12f f) z)
              + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                  / Work.Spaces.c α) ^ 2)
                * (∫ z in Work.Spaces.Iz,
                    slotSumN 4 (Work.FTS.CoercivityFix.Transfer.ampB α) z) := hmono
        _ ≤ (2048 * K ^ 2) * (C1 * Work.Spaces.HkSq α n f)
              + (12800 * Work.Spaces.HkSq α n f) * Kb := add_le_add hstep1 hstep2
        _ ≤ (2048 * K ^ 2 * C1 + 12800 * Kb + 1)
              * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := hfinal
    simpa only [slotSumN_eq] using hbound

end

end Work.FTS.StrongEps.EpsE4Thr.E1Open
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.MuBlockBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false

/-! ## The two modulation constants of the block -/

/-- The modulation constant `μ` of the block at a single profile `W`:
`mufunS α (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W)) W`. -/
noncomputable def muOf (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
    (Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + E W z θ)) W

/-- The modulation constant `μ̄` of the block at a single profile `W`:
`mubar (N₀ α (F_*+W) W) (N α (F_*+W) (Φ_s + E W))`. -/
noncomputable def mubarOf (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : ℝ :=
  Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
    (Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + E W z θ))

/-! ## Identification with the family-level constants -/

/-- `muOf` at a profile `W` *is* `muDyn` at the constant family `famOf (fun _ => W)` and `τ = 0`
(definitionally: `Ftau`, `slice`, `Ftot` and `PsiCan` all reduce). -/
theorem muOf_eq_muDyn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) :
    muOf α Φs E W = Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ : ℝ => W))) (famOf (fun _ => W)) 0 := rfl

/-- The companion of `muOf_eq_muDyn` for the second modulation constant `λ = lamfun μ`. -/
theorem lamfun_muOf_eq_lamDyn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) :
    Work.Construction.lamfun (muOf α Φs E W) = Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ : ℝ => W))) (famOf (fun _ => W)) 0 := rfl

/-- The block, with its two constants named. -/
theorem muBlock_apply (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) (z θ : ℝ) :
    muBlock α Φs E W z θ = -(mubarOf α Φs E W) * Work.Construction.AK α z θ
      + Work.Construction.Nstar (muOf α Φs E W)
          (Work.Construction.lamfun (muOf α Φs E W)) W z θ := rfl


/-- **`MuLamOK` bounds the block's modulation constants on the class-`C` small ball** (the
statement of `MuLamOK` is exactly about `muDyn`/`lamDyn` at the constant family). -/
theorem MuLamOK_muOf {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) {W : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hXn : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2) :
    |muOf α Φs E W| ≤ 1 / 2 ∧ |Work.Construction.lamfun (muOf α Φs E W)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hml W hW hXn
  exact ⟨by rw [muOf_eq_muDyn]; exact h1, by rw [lamfun_muOf_eq_lamDyn]; exact h2⟩

/-! ## Two elementary tools -/

/-- `N_* μ (lamfun μ) g = μ·(D_z g - g)` pointwise, for `μ ≠ -1` (`Apriori.Nstar_lamfun`,
pointwise). -/
theorem Nstar_lamfun_eq {μ : ℝ} (hμ : μ ≠ -1) (g : Fn) (z θ : ℝ) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
      = μ * (Work.Spaces.Dz g z θ - g z θ) := by
  have h := congrFun (congrFun (Work.FTS.Apriori.Nstar_lamfun hμ g) z) θ
  simpa using h

/-- **`D_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k`.** -/
theorem Dz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ + Work.Spaces.Dz k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := f)
    (G := fun z θ => f' z θ + k z θ) (fun z θ _ _ _ => h z θ) 1 z θ hz hθ0 hθ1
  have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf' hk 1 z θ hz hθ0 hθ1
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-! ## The telescoping identity -/

/-- **The block telescopes along a difference.**  With `μᵢ = μ(Wᵢ)`, `μ̄ᵢ = μ̄(Wᵢ)` and
`μᵢ ≠ -1`, on the open quadrant

  `muBlock α Φs E W₁ - muBlock α Φs E W₂
     = -(μ̄₁-μ̄₂)·AK α + μ₁·(D_z(W₁-W₂) - (W₁-W₂)) + (μ₁-μ₂)·(D_z W₂ - W₂)`.

Proof: rewrite both `N_*`-blocks with the collapse `N_* μ (lamfun μ) g = μ(D_z g - g)`, rewrite
`D_z(W₁-W₂) = D_z W₁ - D_z W₂` with `Dz_add_of_smoothOpen`, `ring`. -/
theorem muBlock_sub_eq {α : ℝ} {Φs : Fn} {E : Fn → Fn} {W₁ W₂ : Fn}
    (hW₁ : Work.FTS.EllipticEst.SmoothOpen W₁) (hW₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hμ₁ : muOf α Φs E W₁ ≠ -1) (hμ₂ : muOf α Φs E W₂ ≠ -1) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ
        = -(mubarOf α Φs E W₁ - mubarOf α Φs E W₂) * Work.Construction.AK α z θ
          + muOf α Φs E W₁ * (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
              - (W₁ z θ - W₂ z θ))
          + (muOf α Φs E W₁ - muOf α Φs E W₂) * (Work.Spaces.Dz W₂ z θ - W₂ z θ) := by
  intro z θ hz hθ0 hθ1
  have hDz : Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
      = Work.Spaces.Dz W₁ z θ - Work.Spaces.Dz W₂ z θ := by
    have h := Dz_add_of_smoothOpen (f := W₁) (f' := fun z θ => W₁ z θ - W₂ z θ) (k := W₂)
      (Work.FTS.NonlinRows.smoothOpen_sub hW₁ hW₂) hW₂ (fun z θ => by ring)
    have h' := h z θ hz hθ0 hθ1
    linarith
  rw [muBlock_apply, muBlock_apply, hDz, Nstar_lamfun_eq hμ₁ W₁ z θ,
    Nstar_lamfun_eq hμ₂ W₂ z θ]
  ring

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.HkSqJepsPzPre =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. Elementary facts about the two weights -/

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem gam_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem eta_le_gam_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- The pure-`z` slot weight `w z / sin(2θ)^{η/2}` is nonnegative on `Iθ`. -/
theorem wdiv_eta_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
  div_nonneg (Work.FTS.StrongEps.w_nonneg z)
    (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The pure-`z` slot weight is dominated by `epsW`** (the mixed-slot weight): both share the
radial factor `w z`, and `sin(2θ)^{γ/2} ≤ sin(2θ)^{η/2}` because `η ≤ γ` and `sin(2θ) ≤ 1`
on `Iθ`. -/
theorem wdiv_eta_le_epsW {α z θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ epsW α z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hgam : 0 < Work.Spaces.gam α := gam_pos_of_pos hα
  rcases eq_or_lt_of_le hsin with h0 | hpos
  · have h1 : Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
    have h2 : epsW α z θ = 0 := by
      have h3 : epsW α z θ
          = Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := rfl
      rw [h3, ← h0, Real.zero_rpow (by positivity), div_zero]
    rw [h1, h2]
  · have hle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)
        ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _)
        (by linarith [eta_le_gam_of_pos hα])
    have hpos' : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hpos _
    calc Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) :=
          div_le_div_of_nonneg_left (Work.FTS.StrongEps.w_nonneg z) hpos' hle
      _ = epsW α z θ := rfl

/-- `ContinuousOn` of the pointwise square, in the `fun`-form used by the measurability
route (`ContinuousOn.pow` produces the `Pi`-form `f ^ 2`). -/
theorem continuousOn_sq' {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X}
    (hc : ContinuousOn f s) : ContinuousOn (fun q => (f q) ^ 2) s := by
  have h : (fun q => (f q) ^ 2) = f ^ 2 := by funext q; rw [Pi.pow_apply]
  rw [h]; exact hc.pow 2

/-! ## 2. The `epsW`-slot sum dominating the `ℋᵏ`-integrand -/

/-- The level-`k` slot sum of `g` with the *mixed-slot* weight `epsW α` replacing every weight of
`HkIntegrand`. -/
noncomputable def EpsSlotSum (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ a ∈ Finset.range (k + 1), (Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * epsW α z θ) ^ 2 else 0

/-- **The `ℋᵏ`-integrand is dominated by the `epsW`-slot sum** on `Iθ`. -/
theorem HkIntegrand_le_EpsSlotSum {α : ℝ} (hα : 0 < α) (k : ℕ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k g z θ ≤ EpsSlotSum α k g z θ := by
  have hle := wdiv_eta_le_epsW (α := α) (z := z) (θ := θ) hα hθ
  have h0 := wdiv_eta_nonneg (z := z) (θ := θ) hθ
  rw [Work.Spaces.HkIntegrand, EpsSlotSum]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun a _ => ?_
    have hsq : (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        ≤ (epsW α z θ) ^ 2 := pow_le_pow_left₀ h0 hle 2
    calc (Work.Spaces.DzIter a g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter a g z θ) ^ 2
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
      _ ≤ (Work.Spaces.DzIter a g z θ) ^ 2 * (epsW α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2 := by ring
  · refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, ← epsW_eq_Wt_of_mem_Iθ (α := α) (z := z) hθ]
    · rw [if_neg hc, if_neg hc]

/-- The `ofReal` of the slot sum is the sum of the `ofReal`s of its slots. -/
theorem ofReal_EpsSlotSum {α : ℝ} (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    ENNReal.ofReal (EpsSlotSum α k g z θ)
      = (∑ a ∈ Finset.range (k + 1),
          ENNReal.ofReal ((Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2))
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * epsW α z θ) ^ 2 else 0) := by
  rw [EpsSlotSum]
  rw [ENNReal.ofReal_add
    (Finset.sum_nonneg fun a _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity)]
  congr 1
  · exact ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)
  · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity)]
    exact Finset.sum_congr rfl fun i _ =>
      ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)

/-! ## 3. The product measure of the two domains, and the `ofReal` bridge -/

/-- The product of the two restricted measures, i.e. Lebesgue measure restricted to `Iz × Iθ`. -/
noncomputable abbrev nu : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

theorem nu_eq : (nu : Measure (ℝ × ℝ)) = (volume.prod volume).restrict
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Measure.prod_restrict _ _

/-- The iterated `lintegral` over `Iz`, `Iθ` equals the product-measure `lintegral`. -/
theorem iter_eq_nu {F : ℝ × ℝ → ℝ≥0∞} (hF : AEMeasurable F nu) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, F (z, θ))
      = ∫⁻ q, F q ∂nu := by
  rw [nu_eq]
  refine (MeasureTheory.setLIntegral_prod F ?_).symm
  rw [← Measure.prod_restrict (μ := volume) (ν := volume)
    (Work.Spaces.Iz) (Work.Spaces.Iθ)]
  exact hF

/-- The joint `ℋᵏ`-integrand of a profile smooth on the open quadrant is a.e. strongly
measurable for the product measure. -/
theorem aesm_HkIntegrand_nu {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k g q.1 q.2) nu :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k hsm)

/-- **`ofReal (HkSq α k g)` is bounded by the product-measure `lintegral` of `ofReal` of the
`ℋᵏ`-integrand.**  No integrability hypothesis is needed. -/
theorem ofReal_HkSq_le_nuLint {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k g)
      ≤ ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
    fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k g)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :=
    Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal hψ
  have h2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    lintegral_mono fun z => Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal
      (fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
  have hAe : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2))
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aesm_HkIntegrand_nu hsm).aemeasurable
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
    rw [nu_eq]
    exact (MeasureTheory.setLIntegral_prod
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2)) hAe).symm
  exact h1.trans (h2.trans (le_of_eq h3))

/-- **The same, as an equality, when the profile is in `ℋᵏ`.** -/
theorem ofReal_HkSq_eq_nuLint {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α k g)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k g)
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
    fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k g)
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 (Eventually.of_forall hψ)
  have h2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
  have hAe : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2))
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aesm_HkIntegrand_nu hsm).aemeasurable
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
    rw [nu_eq]
    exact (MeasureTheory.setLIntegral_prod
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2)) hAe).symm
  exact h1.trans (h2.trans h3)

/-! ## 4. Additivity of the `lintegral` over finite sums of a.e. measurable terms -/

theorem lintegral_finset_sum_aemeasurable {ι α : Type*} [DecidableEq ι] {m : MeasurableSpace α}
    {μ : Measure α} (s : Finset ι) {f : ι → α → ℝ≥0∞} (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hi' : AEMeasurable (f i) μ := h i (Finset.mem_insert_self _ _)
      have hs' : ∀ j ∈ s, AEMeasurable (f j) μ := fun j hj => h j (Finset.mem_insert_of_mem hj)
      calc ∫⁻ a, ∑ x ∈ insert i s, f x a ∂μ
          = ∫⁻ a, (f i a + ∑ x ∈ s, f x a) ∂μ := by
              refine lintegral_congr fun a => ?_
              exact Finset.sum_insert hi
        _ = ∫⁻ a, f i a ∂μ + ∫⁻ a, (∑ x ∈ s, f x a) ∂μ :=
              MeasureTheory.lintegral_add_left' hi' _
        _ = ∫⁻ a, f i a ∂μ + ∑ x ∈ s, ∫⁻ a, f x a ∂μ := by rw [ih hs']
        _ = ∑ x ∈ insert i s, ∫⁻ a, f x a ∂μ := by rw [Finset.sum_insert hi]


end Work.FTS.StrongEps.EpsSqTools
end
