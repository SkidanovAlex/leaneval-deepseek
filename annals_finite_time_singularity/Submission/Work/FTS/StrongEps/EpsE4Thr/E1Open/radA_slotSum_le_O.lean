import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_slot5_le_classC_of
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.slot5_radA_pointwise_le
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_Ef_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkg_O
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.C0_sq_le_HkSq

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
