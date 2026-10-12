import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1P.tBwordBInd_slotSwap_nosupp
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
import Submission.Work.Sector.tensor_kinFormB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseFixB1

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Bookkeeping about `kcInsN` and the slot fibre -/

lemma kinHalf_slotFun1_slotState1 {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : Submission.BoseGases.X n) :
    Work.BSKinetic.slotFun1 (Work.BSKinetic.slotState1 i Φ r)
      = fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r)) := rfl

lemma kinHalf_fibre_kcInsN {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (y : E3) (r : Submission.BoseGases.X n) :
    Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (y, r))
      = fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r)) := by
  funext z
  simp only [Work.BoseKinLoc.fibre]
  rw [Work.SmallBoxBridge.Fourier.update_kcInsN]

/-! ## 1. The one-body collapse -/

lemma kinHalf_kinFormBOne {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (φ : Submission.BoseGases.X 1 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BSKinetic.slotFun1 φ) := by
  have hψ : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.slotFun1 φ) := hφ.comp (by fun_prop)
  have h := Work.Sector.tensor_kinFormB (m := 1) (ℓ := ℓ) (d := d) (s := s) (εT := εT)
    (b := b) hℓ hψ
  have hprod : (fun z : Submission.BoseGases.X 1 =>
      ∏ i : Fin 1, Work.BSKinetic.slotFun1 φ (z i)) = φ := by
    funext z
    have hz : (fun _ : Fin 1 => z 0) = z := by funext j; fin_cases j; rfl
    simp [Work.BSKinetic.slotFun1, hz]
  have hmain : Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ
      = 1 * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BSKinetic.slotFun1 φ)
        * (∫ x in Submission.BoseGases.acube ℓ, (Work.BSKinetic.slotFun1 φ x) ^ 2) ^ (1 - 1) := by
    rw [hprod] at h
    simpa using h
  rw [hmain]
  simp

/-! ## 2. The slot decomposition of the anchored kinetic word -/

lemma kinHalf_inner_aux {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n) :
    (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN n i (y, r)) i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (y, r))))
      = ℓ ^ 3 * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  set C : ℝ := Work.BoseKinLoc.fsT ℓ d s εT b 0
    (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))) with hC
  have hpt : ∀ y : E3,
      Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN n i (y, r)) i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (y, r)))
        = Work.BoseKinLoc.indU ℓ 0 y * C := by
    intro y
    rw [Submission.BoseGases.kc_insN_apply_same, kinHalf_fibre_kcInsN, hC]
  rw [setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun y _ => hpt y)]
  rw [show (fun y : E3 => Work.BoseKinLoc.indU ℓ 0 y * C)
      = (fun y : E3 => C * Work.BoseKinLoc.indU ℓ 0 y) from by funext y; ring]
  rw [MeasureTheory.integral_const_mul, Work.Sector.integral_indU_zero_restrict_acube hℓ]
  ring

/-- The same inner integral in the shape produced by `Integrable.integral_prod_right`
(the pair components are not beta-reduced). -/
lemma kinHalf_inner_aux' {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n) :
    (∫ x in Submission.BoseGases.acube ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x, r).1 *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, (x, r).2))))
      = ℓ ^ 3 * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  rw [← kinHalf_inner_aux (d := d) (s := s) (εT := εT) (b := b) hℓ i Φ r]
  refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun y _ => ?_)
  rw [Submission.BoseGases.kc_insN_apply_same, kinHalf_fibre_kcInsN]

lemma kinHalf_zpow_neg3_mul (ℓ : ℝ) (hℓ : 0 < ℓ) : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
  rw [zpow_neg]
  exact inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))

lemma kinHalf_kinFormB_succ {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.BoseKinLoc.kinFormB (n + 1) ℓ d s εT b Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.kinFormB 1 ℓ d s εT b (Work.BSKinetic.slotState1 i Φ r) := by
  rw [Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre (n + 1) i Φ x)) (Submission.BoseGases.abox (n + 1) ℓ) :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT) (b := b)
      hℓ i hΦ
  rw [Submission.BoseGases.abox_integral_peel (i := i)
    (F := fun x : Submission.BoseGases.X (n + 1) =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre (n + 1) i Φ x)) hInt]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => kinHalf_inner_aux hℓ i Φ r))]
  rw [MeasureTheory.integral_const_mul, ← mul_assoc, kinHalf_zpow_neg3_mul ℓ hℓ, one_mul]
  refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) (fun r _ => ?_)
  rw [← kinHalf_slotFun1_slotState1 (i := i) (Φ := Φ) (r := r),
    ← kinHalf_kinFormBOne (d := d) (s := s) (εT := εT) (b := b) hℓ
      (Work.BSKinetic.slotState1 i Φ r) (Work.BSKinetic.contDiff_slotState1 hΦ i r)]

/-! ## 3. Integrability of the `1`-particle word of a slot fibre -/

lemma kinHalf_integrable_kinFormB_slotState1 {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.kinFormB 1 ℓ d s εT b (Work.BSKinetic.slotState1 i Φ r))
      (Work.BSKinetic.boxMu n ℓ) := by
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre (n + 1) i Φ x)) (Submission.BoseGases.abox (n + 1) ℓ) :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT) (b := b)
      hℓ i hΦ
  have hpre : (Submission.BoseGases.kcInsN n i) ⁻¹' (Submission.BoseGases.abox (n + 1) ℓ)
      = Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox n ℓ := by
    ext p
    obtain ⟨y, r⟩ := p
    simp only [Set.mem_preimage, Set.mem_prod, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro hp
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using hp i,
        fun j => by simpa [Submission.BoseGases.kc_insN_apply_succ] using hp (i.succAbove j)⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · rcases Fin.exists_succAbove_eq hj with ⟨j', hj'⟩
        rw [← hj']
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 j'
  have hvol : (MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox n ℓ)
      = (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod (Submission.BoseGases.kcE3)
        (Submission.BoseGases.X n),
      ← MeasureTheory.Measure.prod_restrict]
  have hjoint : MeasureTheory.Integrable
      (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 q.1 *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) := by
    have h := ((Submission.BoseGases.kc_mp_insN n i).integrableOn_comp_preimage
      (Submission.BoseGases.kcInsN n i).measurableEmbedding).mpr hInt
    rw [hpre] at h
    simp only [MeasureTheory.IntegrableOn] at h
    rw [hvol] at h
    refine h.congr (Filter.Eventually.of_forall (fun q => ?_))
    obtain ⟨y, r⟩ := q
    simp only [Function.comp_apply]
    rw [Submission.BoseGases.kc_insN_apply_same, kinHalf_fibre_kcInsN]
  have h2 := hjoint.integral_prod_right
  rw [Work.BSKinetic.boxMu]
  have h4 : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        ℓ ^ 3 * Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    refine h2.congr (Filter.Eventually.of_forall (fun r => ?_))
    dsimp only
    exact kinHalf_inner_aux' (d := d) (s := s) (εT := εT) (b := b) hℓ i Φ r
  have h5 : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    refine (h4.const_mul (((ℓ : ℝ) ^ 3)⁻¹)).congr
      (Filter.Eventually.of_forall (fun r => ?_))
    dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  refine h5.congr (Filter.Eventually.of_forall (fun r => ?_))
  dsimp only
  rw [← kinHalf_slotFun1_slotState1 (i := i) (Φ := Φ) (r := r),
    ← kinHalf_kinFormBOne (d := d) (s := s) (εT := εT) (b := b) hℓ
      (Work.BSKinetic.slotState1 i Φ r) (Work.BSKinetic.contDiff_slotState1 hΦ i r)]

/-! ## 4. `cnPlus` as a slot sum -/

lemma kinHalf_cnPlus_slotSum {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Submission.BoseGases.cnPlus ℓ Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.cnPlus ℓ (Work.BSKinetic.slotState1 i Φ r) := by
  rw [Work.BSKinetic.cnPlus_eq_slotSum hℓ n Φ hΦ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => (Work.BSKinetic.cnPlus_slotState1_eq hℓ n Φ i r).symm)

/-! ## 5. The one-body reduction -/

theorem kinHalf_kineticSplit_slotSum {ℓ d s εT b c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (h1 : ∀ (φ : Submission.BoseGases.X 1 → ℝ), ContDiff ℝ (⊤ : ENat) φ →
        (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ φ
          + (∫ u : E3, Work.UBBInputs8.tBwordBInd 1 ℓ d εT c u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ) :
    ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ), ContDiff ℝ (⊤ : ENat) Φ →
      (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ
        + (∫ u : E3, Work.UBBInputs8.tBwordBInd n ℓ d εT c u Φ)
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ := by
  intro n
  rcases n with _ | m
  · intro Φ hΦ
    have hzero : (fun u : E3 => Work.UBBInputs8.tBwordBInd 0 ℓ d εT c u Φ) = fun _ => (0 : ℝ) := by
      funext u
      simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
        Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBdiagFormInd]
      simp
    rw [show Submission.BoseGases.cnPlus ℓ Φ = 0 by simp [Submission.BoseGases.cnPlus],
      show (∫ u : E3, Work.UBBInputs8.tBwordBInd 0 ℓ d εT c u Φ) = 0 by
        rw [hzero, MeasureTheory.integral_zero],
      show Work.BoseKinLoc.kinFormB 0 ℓ d s εT b Φ = 0 by
        simp [Work.BoseKinLoc.kinFormB]]
    norm_num
  · intro Φ hΦ
    obtain ⟨hK, hKi⟩ :=
      Work.BoseFixB1P.tBwordBInd_slotSwap_nosupp (ℓ := ℓ) (d := d) (ε := εT) (c := c)
        hℓ hd m Φ hΦ
    have hF := kinHalf_kinFormB_succ (d := d) (s := s) (εT := εT) (b := b) hℓ m Φ hΦ
    have hA : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : Submission.BoseGases.X m =>
          (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
            (Work.BSKinetic.slotState1 i Φ r)) (Submission.BoseGases.abox m ℓ) :=
      fun i => (Work.BSKinetic.integrable_cnPlus_slotState1 hℓ m Φ hΦ i).const_mul _
    have hB : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : Submission.BoseGases.X m =>
          ∫ u : E3, Work.BSKinetic.smallBoxWord1 ℓ d εT c u
            (Work.BSKinetic.slotState1 i Φ r)) (Submission.BoseGases.abox m ℓ) :=
      fun i => hKi i
    have hC : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : Submission.BoseGases.X m =>
          Work.BoseKinLoc.kinFormB 1 ℓ d s εT b (Work.BSKinetic.slotState1 i Φ r))
        (Submission.BoseGases.abox m ℓ) :=
      fun i => kinHalf_integrable_kinFormB_slotState1 (d := d) (s := s) (εT := εT) (b := b) hℓ m Φ hΦ i
    have hLHS : (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ
        + (∫ u : E3, Work.UBBInputs8.tBwordBInd (m + 1) ℓ d εT c u Φ)
        = ∑ i : Fin (m + 1),
            ((∫ r in Submission.BoseGases.abox m ℓ,
                (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
                  (Work.BSKinetic.slotState1 i Φ r))
              + ∫ r in Submission.BoseGases.abox m ℓ,
                  ∫ u : E3, Work.BSKinetic.smallBoxWord1 ℓ d εT c u
                    (Work.BSKinetic.slotState1 i Φ r)) := by
      rw [kinHalf_cnPlus_slotSum hℓ m Φ hΦ, hK, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    have hper : ∀ i : Fin (m + 1),
        ((∫ r in Submission.BoseGases.abox m ℓ,
            (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
              (Work.BSKinetic.slotState1 i Φ r))
          + ∫ r in Submission.BoseGases.abox m ℓ,
              ∫ u : E3, Work.BSKinetic.smallBoxWord1 ℓ d εT c u
                (Work.BSKinetic.slotState1 i Φ r))
        ≤ ∫ r in Submission.BoseGases.abox m ℓ,
            Work.BoseKinLoc.kinFormB 1 ℓ d s εT b (Work.BSKinetic.slotState1 i Φ r) := by
      intro i
      rw [← MeasureTheory.integral_add (hA i) (hB i)]
      refine MeasureTheory.integral_mono ((hA i).add (hB i)) (hC i) fun r => ?_
      exact h1 (Work.BSKinetic.slotState1 i Φ r)
        (Work.BSKinetic.contDiff_slotState1 hΦ i r)
    rw [hLHS, hF]
    exact Finset.sum_le_sum fun i _ => hper i

/-! ## 6. The target at FS's parameters -/

theorem kineticHalf_of_oneBody {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (h1 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2)
            * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ
          + (∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ)
    (hI : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
            (Φ : Submission.BoseGases.X n → ℝ))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
            (Φ : Submission.BoseGases.X n → ℝ)) ∧
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2)
            * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ)
          + (∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
                (Φ : Submission.BoseGases.X n → ℝ))
        ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε₁, hε₁, H1⟩ := h1
  obtain ⟨ε₂, hε₂, HI⟩ := hI
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun μ hAdm n Φ => ⟨?_, ?_⟩⟩
  · exact HI μ (Adm.mono hAdm (min_le_right _ _)) n Φ
  · have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ := Adm.mono hAdm (min_le_left _ _)
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm1
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm1
    have h1' : ∀ (φ : Submission.BoseGases.X 1 → ℝ), ContDiff ℝ (⊤ : ENat) φ →
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
              / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
            * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) φ
          + (∫ u : EuclideanSpace ℝ (Fin 3),
              Work.UBBInputs8.tBwordBInd 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (sbCut μ (_root_.BoseGases.a v)) u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ := by
      intro φ hφ
      simpa only [Work.BoseFixB1.sbKin] using H1 μ hAdm1 φ hφ
    exact kinHalf_kineticSplit_slotSum hℓ hd h1' n (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff

end Work.BoseFixB1
