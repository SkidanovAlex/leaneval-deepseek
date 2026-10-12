import ChallengeDeps
import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_sq_integral_le
import Submission.Work.BoseBoxFock.PCFU.abox_integral_slot_collapse
import Submission.Work.BoseBoxFock.PCFU.lowSlot_L2_le
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_abs_le_of_box_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The type of the coordinates other than the slots `i` and `j`. -/
abbrev ChRest {n : ℕ} (i j : Fin n) : Type := {k : Fin n // k ≠ i ∧ k ≠ j} → E3

lemma chiLam_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : z ∉ Submission.BoseGases.acube ℓ) :
    Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
  have hval : Work.BoseK15.corpusBox.chiLam ℓ z
      = Submission.BoseGases.chiBase (ℓ⁻¹ • z) / Real.sqrt Submission.BoseGases.chiNormSq := by
    simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi, Submission.BoseGases.chi]
  have hk : ∃ k : Fin 3, ℓ / 2 < |z k| := by
    by_contra hcon
    push Not at hcon
    refine hz ?_
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    exact ⟨by linarith [(abs_le.mp (hcon m)).1], by linarith [(abs_le.mp (hcon m)).2]⟩
  obtain ⟨k, hk⟩ := hk
  have hnorm : 1 / 2 < ‖(ℓ⁻¹ : ℝ) • z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
    have h1 : |z k| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z k
    have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    calc (1 : ℝ) / 2 = ℓ⁻¹ * (ℓ / 2) := h2.symm
      _ < ℓ⁻¹ * |z k| := mul_lt_mul_of_pos_left hk (inv_pos.mpr hℓ)
      _ ≤ ℓ⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hℓ))
  rw [hval, Submission.BoseGases.chiBase_eq_zero_of_norm_gt _ hnorm, zero_div]

lemma lowSlot_aQ_aP_update_i {n : ℕ} {i j : Fin n} (hij : i ≠ j) {fc : Work.BoseBoxFix.LowCut}
    {κ ℓ : ℝ} {Θ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x := by
  have h1 : ∀ z' : E3,
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
          (Function.update (Function.update x i z) j z')
        = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
          (Function.update x j z') := by
    intro z'
    rw [Function.update_comm hij]
    exact aQ_aP_update_invariant hij (Function.update x j z') z
  have h2 : (Function.update x i z) j = x j := by
    rw [Function.update_apply, if_neg (Ne.symm hij)]
  simp only [Work.BoseBoxFix.lowSlot, h2]
  congr 1
  exact funext h1

lemma chKappa_pos {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    0 < chKappa v μ := by
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  have hKl : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBox.sideAt]
    exact Work.BoseBox.boxSide_pos hμ hav hKl
  rw [chKappa]
  exact inv_pos.mpr (mul_pos (pow_pos hd 2) hside)

lemma sideAt_pos' {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
  have hKl : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  rw [Work.BoseBox.sideAt]
  exact Work.BoseBox.boxSide_pos hμ hav hKl

lemma chCcfg_update_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (z : E3) :
    Function.update (chCcfg i j w w' x') j z = chCcfg i j w z x' := by
  funext k
  rw [Function.update_apply]
  by_cases hkj : k = j
  · rw [if_pos hkj, hkj, chCcfg_j hij]
  · rw [if_neg hkj]
    by_cases hki : k = i
    · rw [hki, chCcfg_i, chCcfg_i]
    · rw [chCcfg_other w w' x' hki hkj, chCcfg_other w z x' hki hkj]

lemma chCcfg_update_i {n : ℕ} {i j : Fin n} (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) (z : E3) :
    Function.update (chCcfg i j w w' x') i z = chCcfg i j z w' x' := by
  funext k
  rw [Function.update_apply]
  by_cases hki : k = i
  · rw [if_pos hki, hki]
    rw [chCcfg_i]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · have hij : i ≠ j := fun hh => hki (by rw [hkj, hh])
      rw [hkj, chCcfg_j hij, chCcfg_j hij]
    · rw [chCcfg_other w w' x' hki hkj, chCcfg_other z w' x' hki hkj]

lemma measurable_chCcfg_xw {n : ℕ} (i j : Fin n) :
    Measurable (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
      chCcfg i j p.1.2 p.2 p.1.1) := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · simp only [chCcfg, dif_pos hki]
    exact measurable_snd.comp measurable_fst
  · by_cases hkj : k = j
    · simp only [chCcfg, dif_neg hki, dif_pos hkj]; exact measurable_snd
    · simp only [chCcfg, dif_neg hki, dif_neg hkj]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)

lemma measurable_chCcfg_xz {n : ℕ} (i j : Fin n) :
    Measurable (fun p : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 =>
      chCcfg i j 0 p.2 p.1) := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · simp only [chCcfg, dif_pos hki]; exact measurable_const
  · by_cases hkj : k = j
    · simp only [chCcfg, dif_neg hki, dif_pos hkj]; exact measurable_snd
    · simp only [chCcfg, dif_neg hki, dif_neg hkj]
      exact (measurable_pi_apply _).comp measurable_fst

/-- `z ↦ chCcfg i j w z x'` is measurable (the varying slot is the second one). -/
lemma measurable_chCcfg_second {n : ℕ} (i j : Fin n) (w : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    Measurable (fun z : E3 => chCcfg i j w z x') := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · simp only [chCcfg, dif_pos hki]; exact measurable_const
  · by_cases hkj : k = j
    · simp only [chCcfg, dif_neg hki, dif_pos hkj]; exact measurable_id
    · simp only [chCcfg, dif_neg hki, dif_neg hkj]; exact measurable_const

/-- The two-term AM–GM in the form used by the slot estimate:
`√a·√b ≤ ½(a/ℓ³ + ℓ³b)`, the sharp form (equality iff `a/ℓ³ = ℓ³b`). -/
lemma sqrt_mul_sqrt_le_half {a b ℓ : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ 2⁻¹ * (a / ℓ ^ 3 + ℓ ^ 3 * b) := by
  have h1 : 0 ≤ a / ℓ ^ 3 := div_nonneg ha (by positivity)
  have h2 : 0 ≤ ℓ ^ 3 * b := mul_nonneg (by positivity) hb
  have hsq : Real.sqrt (a / ℓ ^ 3) * Real.sqrt (ℓ ^ 3 * b) = Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul h1, ← Real.sqrt_mul ha]
    congr 1
    field_simp
  have hkey : 2 * Real.sqrt (a / ℓ ^ 3) * Real.sqrt (ℓ ^ 3 * b) ≤ a / ℓ ^ 3 + ℓ ^ 3 * b := by
    nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2,
      sq_nonneg (Real.sqrt (a / ℓ ^ 3) - Real.sqrt (ℓ ^ 3 * b))]
  have hkey' : 2 * (Real.sqrt (a / ℓ ^ 3) * Real.sqrt (ℓ ^ 3 * b)) ≤ a / ℓ ^ 3 + ℓ ^ 3 * b := by
    linarith [hkey]
  rw [hsq] at hkey'
  linarith

/-- A bounded, a.e.-strongly-measurable function supported in a set of finite measure is in
`L²` (the general-space companion of `memLp_of_support_bound`). -/
lemma memLp_two_of_support_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {f : α → E} {s : Set α}
    (hs : MeasurableSet s) (hsf : ∀ x, x ∉ s → f x = 0) (hsfin : μ s < ⊤)
    (C : ℝ) (hm : AEStronglyMeasurable f μ) (hb : ∀ x, ‖f x‖ ≤ C) :
    MemLp f 2 μ := by
  haveI : IsFiniteMeasure (μ.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hsfin⟩
  have hbase : MemLp f 2 (μ.restrict s) :=
    MemLp.of_bound hm.restrict C (Filter.Eventually.of_forall fun x => hb x)
  have heq : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsf x hx]
  rw [heq]
  exact (memLp_indicator_iff_restrict hs).mpr hbase

theorem chCslot_le_of_pairing (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {μ : ℝ}, 0 < μ → ∀ {N n : ℕ} {i j : Fin n}, i ≠ j →
      ∀ (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (P : ℝ),
        Work.BoseBoxFock.PCFU.ChKerPair v h μ fu N P →
        ‖Work.BoseBoxFock.PCFU.chCslot v h fc fu μ N i j
            (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ C * (P * (1 + Work.BoseBoxFock.ellH v μ ^ 3))
              * Work.BoseBoxFix.normB v μ n Φ := by
  refine ⟨1, zero_le_one, ?_⟩
  intro μ hμ N n i j hij Φ P hP
  rcases n with _ | _ | m
  · exact i.elim0
  · exact absurd (Fin.ext (by omega)) hij
  set ℓ : ℝ := ellH v μ with hℓdef
  have hℓ : 0 < ℓ := ellH_pos v μ
  set κ : ℝ := chKappa v μ with hκdef
  have hκ : 0 < κ := chKappa_pos hμ hav
  set χ : E3 → ℝ := Work.BoseK15.corpusBox.chiLam ℓ with hχdef
  have hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ → χ z = 0 := fun z hz => by
    rw [hχdef]; exact chiLam_eq_zero_of_notMem_acube hℓ hz
  set Θ : Submission.BoseGases.X (m+2) → ℝ :=
    boxRestrictR ℓ (Φ : Submission.BoseGases.X (m+2) → ℝ) with hΘdef
  set Ψ : Submission.BoseGases.X (m+2) → ℝ :=
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hΨdef
  set G : Submission.BoseGases.X (m+2) → ℝ := Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ with hGdef
  have hΦc : Continuous (Φ : Submission.BoseGases.X (m+2) → ℝ) := Φ.contDiff.continuous
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (m+2) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (m+2) ℓ) (f := (Φ : Submission.BoseGases.X (m+2) → ℝ))
    hΦc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg ((Φ : Submission.BoseGases.X (m+2) → ℝ) 0))
    (hB 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hΘzero : ∀ x : Submission.BoseGases.X (m+2),
      x ∉ Submission.BoseGases.abox (m+2) ℓ → Θ x = 0 := by
    intro x hx
    rw [hΘdef]; unfold boxRestrictR
    rw [Set.indicator_of_notMem hx, mul_zero]
  have hΘglob : ∀ x : Submission.BoseGases.X (m+2), |Θ x| ≤ B := by
    intro x
    by_cases hx : x ∈ Submission.BoseGases.abox (m+2) ℓ
    · rw [hΘdef]; unfold boxRestrictR
      rw [Set.indicator_of_mem hx, mul_one]
      exact hB x hx
    · rw [hΘzero x hx, abs_zero]; exact hB0
  have hΘm : Measurable Θ := by
    rw [hΘdef]; unfold boxRestrictR
    exact hΦc.measurable.mul
      (measurable_const.indicator (Submission.BoseGases.abox_measurable (m+2) ℓ))
  have hΘbox : ∀ x ∈ Submission.BoseGases.abox (m+2) ℓ,
      Θ x = (Φ : Submission.BoseGases.X (m+2) → ℝ) x := by
    intro x hx
    rw [hΘdef]; unfold boxRestrictR
    rw [Set.indicator_of_mem hx, mul_one]
  have hΘL2 : MemLp Θ 2 (volume.restrict (Submission.BoseGases.abox (m+2) ℓ)) := by
    haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X (m+2))).restrict
        (Submission.BoseGases.abox (m+2) ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ];
          exact Submission.BoseGases.abox_lt_top (m+2) ℓ hℓ.le⟩
    refine MemLp.of_bound (hΘm.aestronglyMeasurable.restrict) B ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Submission.BoseGases.abox_measurable (m+2) ℓ)] with x hx
    rw [Real.norm_eq_abs]
    exact hΘglob x
  have hΨm : Measurable Ψ := by
    rw [hΨdef]
    exact Weak.aQ_measurable j (Weak.aP_measurable i hΘm)
  have hΨglob : ∀ x : Submission.BoseGases.X (m+2), |Ψ x| ≤ 2 * B := by
    intro x
    rw [hΨdef]
    exact Weak.aQ_abs_le hℓ j hB0 (Weak.aP_abs_le hℓ i hB0 hΘglob) x
  have hΨi : ∀ (x : Submission.BoseGases.X (m+2)) (z : E3), Ψ (Function.update x i z) = Ψ x := by
    intro x z
    rw [hΨdef]
    exact aQ_aP_update_invariant hij x z
  have hGm : Measurable G := by
    rw [hGdef]
    exact lowSlotMeasurableOfMeasurable fc j hΨm
  have hGinv : ∀ (x : Submission.BoseGases.X (m+2)) (z : E3), G (Function.update x i z) = G x := by
    intro x z
    rw [hGdef, hΨdef]
    exact lowSlot_aQ_aP_update_i hij x z
  set Kg : ℝ := (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, |fc.f (‖p‖ / κ)|)) * (2 * B * ℓ ^ 3)
    with hKgdef
  have hKg0 : 0 ≤ Kg := by
    rw [hKgdef]
    have h2 : 0 ≤ (∫ p : E3, |fc.f (‖p‖ / κ)|) := integral_nonneg fun p => abs_nonneg _
    have h3 : 0 ≤ (2 * B * ℓ ^ 3) := by positivity
    positivity
  have hGbound : ∀ y : Submission.BoseGases.X (m+2), |G y| ≤ Kg := by
    intro y
    have hfib : Measurable (fun z : E3 => Ψ (Function.update y j z)) := by
      have hcont : Continuous (Function.update y j : E3 → Submission.BoseGases.X (m+2)) := by
        fun_prop
      exact hΨm.comp hcont.measurable
    have h1 := Work.BoseFixB3.CS.Pieces.lowMult_abs_le_of_box_bound (fc := fc) (κ := κ) (ℓ := ℓ)
      (D := 2 * B) hκ hℓ (by positivity) hfib (fun z _ => hΨglob _) (y j)
    rw [hKgdef]
    exact h1
  set H : Submission.BoseGases.X (m+2) → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * ((χ (x i) : ℝ) : ℂ)
      * (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (x i - z)
          * ((G (Function.update x j z) : ℝ) : ℂ)) with hHdef
  have hchC : chCslot v h fc fu μ N i j Θ = ∫ x : Submission.BoseGases.X (m+2), H x := rfl
  have hnormBnn : 0 ≤ Work.BoseBoxFix.normB v μ (m+2) Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => by positivity)
  by_cases hP0 : 0 ≤ P
  · by_cases hInt : Integrable H (volume : Measure (Submission.BoseGases.X (m+2)))
    · -- ======================= the main branch =======================
      have hpeel : (∫ x : Submission.BoseGases.X (m+2), H x)
          = ∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x') :=
        chCcfg_integral_peel (i := i) (j := j) hij hInt
      set A : E3 → ChRest i j → ℂ :=
        fun w x' => ∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) with hAdef
      set gfun : E3 → ChRest i j → ℂ := fun z x' =>
        (Submission.BoseGases.acube ℓ).indicator
          (fun z => ((G (chCcfg i j 0 z x') : ℝ) : ℂ)) z with hgdef
      set box' : Set (ChRest i j) :=
        Set.univ.pi (fun _ : {k : Fin (m+2) // k ≠ i ∧ k ≠ j} =>
          Submission.BoseGases.acube ℓ) with hboxdef
      have hbox'meas : MeasurableSet box' := by
        rw [hboxdef]
        exact MeasurableSet.pi Set.countable_univ fun k _ =>
          Submission.BoseGases.acube_measurable ℓ
      have hbox'fin : (volume : Measure (ChRest i j)) box' < ⊤ := by
        rw [hboxdef]
        rw [show (volume : Measure (ChRest i j))
            = Measure.pi (fun _ : {k : Fin (m+2) // k ≠ i ∧ k ≠ j} => (volume : Measure E3))
            from rfl]
        rw [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun k _ => Submission.BoseGases.acube_lt_top ℓ hℓ.le
      set φ : ChRest i j → ℝ :=
        box'.indicator (fun x' => ∫ w : E3, ‖A w x'‖ ^ 2) with hφdef
      set ψ : ChRest i j → ℝ :=
        box'.indicator (fun x' => ∫ z : E3, ‖gfun z x'‖ ^ 2) with hψdef
      set Nn : ℝ := ∫ x in Submission.BoseGases.abox (m+2) ℓ, (Θ x) ^ 2 with hNndef
      have hφnn : ∀ x' : ChRest i j, 0 ≤ φ x' := by
        intro x'
        rw [hφdef]
        by_cases hx : x' ∈ box'
        · rw [Set.indicator_of_mem hx]
          exact integral_nonneg fun w => by positivity
        · rw [Set.indicator_of_notMem hx]
      have hψnn : ∀ x' : ChRest i j, 0 ≤ ψ x' := by
        intro x'
        rw [hψdef]
        by_cases hx : x' ∈ box'
        · rw [Set.indicator_of_mem hx]
          exact integral_nonneg fun z => by positivity
        · rw [Set.indicator_of_notMem hx]
      -- ### the pointwise collapse of the state
      have hHpt : ∀ (w w' : E3) (x' : ChRest i j),
          H (chCcfg i j w w' x')
            = ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) * (((χ w : ℝ) : ℂ) *
                (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
                  * ((G (chCcfg i j w z x') : ℝ) : ℂ))) := by
        intro w w' x'
        show ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) * ((χ ((chCcfg i j w w' x') i) : ℝ) : ℂ)
            * (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N ((chCcfg i j w w' x') i - z)
                * ((G (Function.update (chCcfg i j w w' x') j z) : ℝ) : ℂ))
          = ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) * (((χ w : ℝ) : ℂ) *
              (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
                * ((G (chCcfg i j w z x') : ℝ) : ℂ)))
        rw [chCcfg_i]
        have hz : (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
              * ((G (Function.update (chCcfg i j w w' x') j z) : ℝ) : ℂ))
            = ∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
                * ((G (chCcfg i j w z x') : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [chCcfg_update_j (i := i) (j := j) hij w w' x' z]
        rw [hz]
        ring
      have hcollapse : ∀ (w : E3) (x' : ChRest i j),
          (∫ w' : E3, H (chCcfg i j w w' x'))
            = A w x' * ((χ w : ℝ) : ℂ)
                * (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z) * (gfun z x')) := by
        intro w x'
        have hz : (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
              * ((G (chCcfg i j w z x') : ℝ) : ℂ))
            = ∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z) * (gfun z x') := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [hgdef]
          by_cases hzc : z ∈ Submission.BoseGases.acube ℓ
          · rw [Set.indicator_of_mem hzc]
            have hupd : chCcfg i j w z x' = Function.update (chCcfg i j 0 z x') i w :=
              (chCcfg_update_i (i := i) (j := j) (0 : E3) z x' w).symm
            rw [hupd, hGinv]
          · rw [Set.indicator_of_notMem hzc, hχ0 z hzc]
            simp only [Complex.ofReal_zero, zero_mul]
        rw [show (∫ w' : E3, H (chCcfg i j w w' x'))
            = ∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) * (((χ w : ℝ) : ℂ) *
                (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z)
                  * ((G (chCcfg i j w z x') : ℝ) : ℂ)))
            from integral_congr_ae (Filter.Eventually.of_forall (hHpt w · x'))]
        rw [MeasureTheory.integral_mul_const, hz]
        rw [show (∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ)) = A w x' from by
          simp only [hAdef]]
        ring
      have hpull : ∀ (w : E3) (x' : ChRest i j),
          A w x' * ((χ w : ℝ) : ℂ)
              * (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N (w - z) * (gfun z x'))
            = ∫ z : E3, A w x' * ((χ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
                * ((χ z : ℝ) : ℂ) * (gfun z x') := by
        intro w x'
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with z
        ring
      -- ### bounds on `A`
      have hAcore : ∀ (w : E3) (x' : ChRest i j), ‖A w x'‖ ≤ B * ℓ ^ 3 := by
        intro w x'
        have htri : ‖A w x'‖ ≤ ∫ w' : E3, |Θ (chCcfg i j w w' x')| := by
          have h0 : A w x' = ∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) := by
            simp only [hAdef]
          rw [h0]
          refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
          apply integral_congr_ae
          filter_upwards with w'
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hmaj : Integrable (fun w' : E3 =>
            B * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w')
            (volume : Measure E3) :=
          ((integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr
            (IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
              aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp))).const_mul B
        have hle : (∫ w' : E3, |Θ (chCcfg i j w w' x')|)
            ≤ ∫ w' : E3, B * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w' := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w' => abs_nonneg _) hmaj
            (Filter.Eventually.of_forall fun w' => ?_)
          beta_reduce
          by_cases hw : w' ∈ Submission.BoseGases.acube ℓ
          · rw [Set.indicator_of_mem hw, mul_one]
            exact hΘglob _
          · rw [Set.indicator_of_notMem hw, mul_zero]
            have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
              rw [chCcfg_mem_abox_iff hij]
              rintro ⟨-, hw', -⟩
              exact hw hw'
            rw [hΘzero _ hnot, abs_zero]
        refine le_trans htri (le_trans hle (le_of_eq ?_))
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
          (Submission.BoseGases.acube_measurable ℓ), MeasureTheory.setIntegral_const,
          Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
          ENNReal.toReal_ofReal (by positivity)]
        simp [smul_eq_mul]
      have hAacube : ∀ (w : E3) (x' : ChRest i j),
          w ∉ Submission.BoseGases.acube ℓ → A w x' = 0 := by
        intro w x' hw
        have h0 : (∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ)) = 0 := by
          rw [show (∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ)) = ∫ _ : E3, (0 : ℂ) from
            integral_congr_ae (Filter.Eventually.of_forall fun w' => by
              beta_reduce
              have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                rw [chCcfg_mem_abox_iff hij]
                rintro ⟨hw', -, -⟩
                exact hw hw'
              rw [hΘzero _ hnot]; simp), integral_zero]
        simpa only [hAdef] using h0
      have hAbox' : ∀ (w : E3) (x' : ChRest i j),
          (∃ k : {k : Fin (m+2) // k ≠ i ∧ k ≠ j}, x' k ∉ Submission.BoseGases.acube ℓ) →
          A w x' = 0 := by
        intro w x' hx
        have h0 : (∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ)) = 0 := by
          rw [show (∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ)) = ∫ _ : E3, (0 : ℂ) from
            integral_congr_ae (Filter.Eventually.of_forall fun w' => by
              beta_reduce
              have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                rw [chCcfg_mem_abox_iff hij]
                rintro ⟨-, -, hx'⟩
                exact hx.elim fun k hk => hk (hx' k)
              rw [hΘzero _ hnot]; simp), integral_zero]
        simpa only [hAdef] using h0
      have hAcs : ∀ (w : E3) (x' : ChRest i j),
          ‖A w x'‖ ^ 2 ≤ ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 := by
        intro w x'
        have hsupp : ∀ w' : E3, w' ∉ Submission.BoseGases.acube ℓ →
            |Θ (chCcfg i j w w' x')| = 0 := by
          intro w' hw'
          have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
            rw [chCcfg_mem_abox_iff hij]
            rintro ⟨-, hw'', -⟩
            exact hw' hw''
          rw [hΘzero _ hnot, abs_zero]
        have hasm : AEStronglyMeasurable (fun w' : E3 => |Θ (chCcfg i j w w' x')|)
            (volume : Measure E3) :=
          ((hΘm.comp (measurable_chCcfg_second (i := i) (j := j) w x')).abs).aestronglyMeasurable
        have hfm : MemLp (fun w' : E3 => |Θ (chCcfg i j w w' x')|) 2 (volume : Measure E3) :=
          memLp_of_support_bound (f := fun w' : E3 => |Θ (chCcfg i j w w' x')|)
            (Submission.BoseGases.acube_measurable ℓ) hsupp
            (Submission.BoseGases.acube_lt_top ℓ hℓ.le) B hasm
            (fun w' => by simp only [Real.norm_eq_abs, abs_abs]; exact hΘglob _)
        have hcs := Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
          (s := Submission.BoseGases.acube ℓ) (Submission.BoseGases.acube_measurable ℓ)
          (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)) hfm hsupp
        have hvol : (volume (Submission.BoseGases.acube ℓ)).toReal = ℓ ^ 3 := by
          rw [Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
        rw [hvol] at hcs
        have htri : ‖A w x'‖ ≤ ∫ w' : E3, |Θ (chCcfg i j w w' x')| := by
          have h0 : A w x' = ∫ w' : E3, ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) := by
            simp only [hAdef]
          rw [h0]
          refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
          apply integral_congr_ae
          filter_upwards with w'
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hsq : (∫ w' : E3, |Θ (chCcfg i j w w' x')| ^ 2)
            = ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with w'
          rw [sq_abs]
        calc ‖A w x'‖ ^ 2 ≤ (∫ w' : E3, |Θ (chCcfg i j w w' x')|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ ≤ (∫ w' : E3, |Θ (chCcfg i j w w' x')| ^ 2) * ℓ ^ 3 := hcs
          _ = ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 := by rw [hsq, mul_comm]
      -- ### the pairing bound per `x'`
      have hAasmj : AEStronglyMeasurable (fun p : ChRest i j × E3 => A p.2 p.1)
          ((volume : Measure (ChRest i j)).prod (volume : Measure E3)) := by
        have hjoint : AEStronglyMeasurable
            (fun p : (ChRest i j × E3) × E3 =>
              ((Θ (chCcfg i j p.1.2 p.2 p.1.1) : ℝ) : ℂ))
            (((volume : Measure (ChRest i j)).prod (volume : Measure E3)).prod
              (volume : Measure E3)) :=
          (Complex.continuous_ofReal.measurable.comp
            (hΘm.comp (measurable_chCcfg_xw (i := i) (j := j)))).aestronglyMeasurable
        have h2 := hjoint.integral_prod_right'
          (μ := (volume : Measure (ChRest i j)).prod (volume : Measure E3))
          (ν := (volume : Measure E3))
        exact h2
      have hpair0 : ∀ x' : ChRest i j,
          ‖∫ w : E3, ∫ z : E3, A w x' * ((χ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
              * ((χ z : ℝ) : ℂ) * (gfun z x')‖
            ≤ P * (Real.sqrt (∫ w, ‖(fun w : E3 => A w x') w‖ ^ 2)
                * Real.sqrt (∫ z, ‖(fun z : E3 => gfun z x') z‖ ^ 2)) := by
        intro x'
        have hmem1 : MemLp (fun w : E3 => A w x') 2 (volume : Measure E3) := by
          have hsupp : ∀ w : E3, w ∉ Submission.BoseGases.acube ℓ →
              (fun w : E3 => A w x') w = 0 := fun w hw => hAacube w x' hw
          have hasm : AEStronglyMeasurable (fun w : E3 => A w x') (volume : Measure E3) := by
            have hjoint : AEStronglyMeasurable
                (fun q : E3 × E3 => ((Θ (chCcfg i j q.1 q.2 x') : ℝ) : ℂ))
                ((volume : Measure E3).prod (volume : Measure E3)) :=
              (Complex.continuous_ofReal.measurable.comp
                (hΘm.comp (measurable_chCcfg_pair (i := i) (j := j) x'))).aestronglyMeasurable
            have h2 := hjoint.integral_prod_right'
              (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
            simpa only [hAdef] using h2
          exact memLp_of_support_bound (f := fun w : E3 => A w x')
            (Submission.BoseGases.acube_measurable ℓ) hsupp
            (Submission.BoseGases.acube_lt_top ℓ hℓ.le) (B * ℓ ^ 3) hasm (fun w => hAcore w x')
        have hmem2 : MemLp (fun z : E3 => gfun z x') 2 (volume : Measure E3) := by
          haveI : IsFiniteMeasure
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
            ⟨by rw [Measure.restrict_apply_univ];
                exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
          have hbase : MemLp (fun z : E3 => ((G (chCcfg i j 0 z x') : ℝ) : ℂ)) 2
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
            refine MemLp.of_bound ?_ Kg (Filter.Eventually.of_forall fun z => ?_)
            · exact (Complex.continuous_ofReal.measurable.comp
                (hGm.comp (measurable_chCcfg_second (i := i) (j := j) 0 x'))).aestronglyMeasurable
            · simpa only [Complex.norm_real, Real.norm_eq_abs] using hGbound (chCcfg i j 0 z x')
          rw [show (fun z : E3 => gfun z x') = (Submission.BoseGases.acube ℓ).indicator
              (fun z => ((G (chCcfg i j 0 z x') : ℝ) : ℂ)) from by simp only [hgdef]]
          exact (memLp_indicator_iff_restrict (Submission.BoseGases.acube_measurable ℓ)).mpr hbase
        have hb := hP (fun w : E3 => A w x') (fun z : E3 => gfun z x') hmem1 hmem2
        simpa only [hℓdef, hχdef, mul_assoc] using hb
      have hperx : ∀ x' : ChRest i j,
          ‖∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x')‖
            ≤ P * (Real.sqrt (φ x') * Real.sqrt (ψ x')) := by
        intro x'
        by_cases hx : x' ∈ box'
        · have hbridge : (∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x'))
              = ∫ w : E3, ∫ z : E3, A w x' * ((χ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
                  * ((χ z : ℝ) : ℂ) * (gfun z x') := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            beta_reduce
            rw [hcollapse w x', hpull w x']
          have e1 : (∫ w : E3, ‖(fun w : E3 => A w x') w‖ ^ 2) = φ x' := by
            rw [hφdef, Set.indicator_of_mem hx]
          have e2 : (∫ z : E3, ‖(fun z : E3 => gfun z x') z‖ ^ 2) = ψ x' := by
            rw [hψdef, Set.indicator_of_mem hx]
          rw [hbridge]
          have h := hpair0 x'
          rw [e1, e2] at h
          simpa using h
        · have hH0 : ∀ (w w' : E3), H (chCcfg i j w w' x') = 0 := by
            intro w w'
            have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
              rw [chCcfg_mem_abox_iff hij]
              rintro ⟨-, -, hx'⟩
              exact hx (by
                rw [hboxdef, Set.mem_univ_pi]
                exact hx')
            show ((Θ (chCcfg i j w w' x') : ℝ) : ℂ) * ((χ ((chCcfg i j w w' x') i) : ℝ) : ℂ)
                * (∫ z : E3, ((χ z : ℝ) : ℂ) * chD v h μ fu N ((chCcfg i j w w' x') i - z)
                    * ((G (Function.update (chCcfg i j w w' x') j z) : ℝ) : ℂ)) = 0
            rw [hΘzero _ hnot]
            simp
          have hzero : (∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x')) = 0 := by
            simp only [hH0, integral_zero]
          rw [hzero, norm_zero]
          exact mul_nonneg hP0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      -- ### the peel identity for `Θ`
      have hThetaId : (∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3,
          (Θ (chCcfg i j w w' x')) ^ 2) = Nn := by
        have hInt1 : Integrable (fun x : Submission.BoseGases.X (m+2) =>
            (Submission.BoseGases.abox (m+2) ℓ).indicator (fun x => (Θ x) ^ 2) x)
            (volume : Measure (Submission.BoseGases.X (m+2))) := by
          rw [integrable_indicator_iff (Submission.BoseGases.abox_measurable (m+2) ℓ)]
          refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (m+2) ℓ hℓ.le) ?_
            (B ^ 2) ?_
          · exact ((hΘm.pow_const 2).aestronglyMeasurable).restrict
          · filter_upwards [MeasureTheory.ae_restrict_mem
              (Submission.BoseGases.abox_measurable (m+2) ℓ)] with x hx
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hΘglob x, abs_nonneg (Θ x), sq_abs (Θ x)]
        have hpeel1 := chCcfg_integral_peel_real (i := i) (j := j) hij hInt1
        have hpt2 : ∀ (x' : ChRest i j) (w w' : E3),
            (Submission.BoseGases.abox (m+2) ℓ).indicator (fun x => (Θ x) ^ 2)
                (chCcfg i j w w' x') = (Θ (chCcfg i j w w' x')) ^ 2 := by
          intro x' w w'
          rw [Set.indicator]
          by_cases hmem : chCcfg i j w w' x' ∈ Submission.BoseGases.abox (m+2) ℓ
          · rw [if_pos hmem]
          · rw [if_neg hmem, hΘzero _ hmem]; ring
        calc (∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            = ∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3,
                (Submission.BoseGases.abox (m+2) ℓ).indicator (fun x => (Θ x) ^ 2)
                  (chCcfg i j w w' x') := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
              refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
              refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
              beta_reduce
              rw [hpt2 x' w w']
          _ = ∫ x, (Submission.BoseGases.abox (m+2) ℓ).indicator (fun x => (Θ x) ^ 2) x :=
              hpeel1.symm
          _ = Nn := by
              rw [hNndef, MeasureTheory.integral_indicator
                (Submission.BoseGases.abox_measurable (m+2) ℓ)]
      -- ### the mass bound for `φ`
      have hmajw : ∀ x' : ChRest i j, Integrable (fun w : E3 =>
          ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) (volume : Measure E3) := by
        intro x'
        have hsupp : ∀ w : E3, w ∉ Submission.BoseGases.acube ℓ →
            ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 = 0 := by
          intro w hw
          have h0 : (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = 0 := by
            rw [show (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = ∫ _ : E3, (0 : ℝ) from
              integral_congr_ae (Filter.Eventually.of_forall fun w' => by
                beta_reduce
                have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                  rw [chCcfg_mem_abox_iff hij]
                  rintro ⟨hw', -, -⟩
                  exact hw hw'
                rw [hΘzero _ hnot]; ring), integral_zero]
          rw [h0, mul_zero]
        have hasm : AEStronglyMeasurable (fun w : E3 =>
            ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) (volume : Measure E3) := by
          have hjoint : AEStronglyMeasurable
              (fun q : E3 × E3 => (Θ (chCcfg i j q.1 q.2 x')) ^ 2)
              ((volume : Measure E3).prod (volume : Measure E3)) :=
            ((hΘm.comp (measurable_chCcfg_pair (i := i) (j := j) x')).pow_const 2).aestronglyMeasurable
          exact (hjoint.integral_prod_right').const_mul _
        have hstep : IntegrableOn (fun w : E3 =>
            ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            (Submission.BoseGases.acube ℓ) (volume : Measure E3) := by
          refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hasm.restrict
            (ℓ ^ 3 * (B ^ 2 * ℓ ^ 3)) ?_
          filter_upwards with w
          show ‖ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2‖ ≤ ℓ ^ 3 * (B ^ 2 * ℓ ^ 3)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (pow_pos hℓ 3))
            (integral_nonneg fun w' => by positivity))]
          have h1 : (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) ≤ B ^ 2 * ℓ ^ 3 := by
            have hmaj2 : Integrable (fun w' : E3 =>
                B ^ 2 * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w')
                (volume : Measure E3) :=
              ((integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr
                (IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
                  aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp))).const_mul
                (B ^ 2)
            have hle2 : (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
                ≤ ∫ w' : E3, B ^ 2 * (Submission.BoseGases.acube ℓ).indicator
                    (fun _ => (1 : ℝ)) w' := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w' => by positivity)
                hmaj2 (Filter.Eventually.of_forall fun w' => ?_)
              beta_reduce
              by_cases hw : w' ∈ Submission.BoseGases.acube ℓ
              · rw [Set.indicator_of_mem hw, mul_one]
                nlinarith [hΘglob (chCcfg i j w w' x'), abs_nonneg (Θ (chCcfg i j w w' x')),
                  sq_abs (Θ (chCcfg i j w w' x'))]
              · rw [Set.indicator_of_notMem hw, mul_zero]
                have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                  rw [chCcfg_mem_abox_iff hij]
                  rintro ⟨-, hw', -⟩
                  exact hw hw'
                rw [hΘzero _ hnot]; norm_num
            refine le_trans hle2 (le_of_eq ?_)
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
              (Submission.BoseGases.acube_measurable ℓ), MeasureTheory.setIntegral_const,
              Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
              ENNReal.toReal_ofReal (by positivity)]
            simp [smul_eq_mul]
          nlinarith [h1, pow_pos hℓ 3, sq_nonneg B]
        rw [show (fun w : E3 => ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            = (Submission.BoseGases.acube ℓ).indicator
                (fun w : E3 => ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) from by
          funext w
          by_cases hw : w ∈ Submission.BoseGases.acube ℓ
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hsupp w hw]]
        exact (integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr hstep
      have hmajbox : Integrable (fun x' : ChRest i j =>
          ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
          (volume : Measure (ChRest i j)) := by
        have hsupp : ∀ x' : ChRest i j, x' ∉ box' →
            ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 = 0 := by
          intro x' hx
          have h0 : (∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = 0 := by
            have hinner : ∀ w : E3, (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = 0 := by
              intro w
              rw [show (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = ∫ _ : E3, (0 : ℝ) from
                integral_congr_ae (Filter.Eventually.of_forall fun w' => by
                  beta_reduce
                  have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                    rw [chCcfg_mem_abox_iff hij]
                    rintro ⟨-, -, hx'⟩
                    exact hx (by rw [hboxdef, Set.mem_univ_pi]; exact hx')
                  rw [hΘzero _ hnot]; ring), integral_zero]
            simp only [hinner, integral_zero]
          rw [h0, mul_zero]
        have hasm : AEStronglyMeasurable (fun x' : ChRest i j =>
            ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            (volume : Measure (ChRest i j)) := by
          have hM : AEStronglyMeasurable
              (fun p : ChRest i j × E3 => ∫ w' : E3, (Θ (chCcfg i j p.2 w' p.1)) ^ 2)
              ((volume : Measure (ChRest i j)).prod (volume : Measure E3)) := by
            have hjoint : AEStronglyMeasurable
                (fun q : (ChRest i j × E3) × E3 => (Θ (chCcfg i j q.1.2 q.2 q.1.1)) ^ 2)
                (((volume : Measure (ChRest i j)).prod (volume : Measure E3)).prod
                  (volume : Measure E3)) :=
              ((hΘm.comp (measurable_chCcfg_xw (i := i) (j := j))).pow_const 2).aestronglyMeasurable
            exact hjoint.integral_prod_right'
          have h := hM.integral_prod_right'
            (μ := (volume : Measure (ChRest i j))) (ν := (volume : Measure E3))
          exact h.const_mul _
        have hstep : IntegrableOn (fun x' : ChRest i j =>
            ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            box' (volume : Measure (ChRest i j)) := by
          refine IntegrableOn.of_bound hbox'fin hasm.restrict
            (ℓ ^ 3 * (B ^ 2 * ℓ ^ 3 * ℓ ^ 3)) ?_
          filter_upwards with x'
          show ‖ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2‖
            ≤ ℓ ^ 3 * (B ^ 2 * ℓ ^ 3 * ℓ ^ 3)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (pow_pos hℓ 3))
            (integral_nonneg fun w => integral_nonneg fun w' => by positivity))]
          have h1 : (∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) ≤ B ^ 2 * ℓ ^ 3 * ℓ ^ 3 := by
            have h2 : ∀ w : E3, (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) ≤ B ^ 2 * ℓ ^ 3 := by
              intro w
              have hmaj2 : Integrable (fun w' : E3 =>
                  B ^ 2 * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w')
                  (volume : Measure E3) :=
                ((integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr
                  (IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
                    aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp))).const_mul
                  (B ^ 2)
              have hle2 : (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
                  ≤ ∫ w' : E3, B ^ 2 * (Submission.BoseGases.acube ℓ).indicator
                      (fun _ => (1 : ℝ)) w' := by
                refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w' => by positivity)
                  hmaj2 (Filter.Eventually.of_forall fun w' => ?_)
                beta_reduce
                by_cases hw : w' ∈ Submission.BoseGases.acube ℓ
                · rw [Set.indicator_of_mem hw, mul_one]
                  nlinarith [hΘglob (chCcfg i j w w' x'), abs_nonneg (Θ (chCcfg i j w w' x')),
                    sq_abs (Θ (chCcfg i j w w' x'))]
                · rw [Set.indicator_of_notMem hw, mul_zero]
                  have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                    rw [chCcfg_mem_abox_iff hij]
                    rintro ⟨-, hw', -⟩
                    exact hw hw'
                  rw [hΘzero _ hnot]; norm_num
              refine le_trans hle2 (le_of_eq ?_)
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
                (Submission.BoseGases.acube_measurable ℓ), MeasureTheory.setIntegral_const,
                Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
                ENNReal.toReal_ofReal (by positivity)]
              simp [smul_eq_mul]
            have hmaj3 : Integrable (fun w : E3 =>
                B ^ 2 * ℓ ^ 3 * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w)
                (volume : Measure E3) :=
              ((integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr
                (IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
                  aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp))).const_mul
                (B ^ 2 * ℓ ^ 3)
            have hle3 : (∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
                ≤ ∫ w : E3, B ^ 2 * ℓ ^ 3 * (Submission.BoseGases.acube ℓ).indicator
                    (fun _ => (1 : ℝ)) w := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
                integral_nonneg fun w' => by positivity) hmaj3
                (Filter.Eventually.of_forall fun w => ?_)
              beta_reduce
              by_cases hw : w ∈ Submission.BoseGases.acube ℓ
              · rw [Set.indicator_of_mem hw, mul_one]
                exact h2 w
              · rw [Set.indicator_of_notMem hw, mul_zero]
                have h0 : (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = 0 := by
                  rw [show (∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) = ∫ _ : E3, (0 : ℝ) from
                    integral_congr_ae (Filter.Eventually.of_forall fun w' => by
                      beta_reduce
                      have hnot : chCcfg i j w w' x' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                        rw [chCcfg_mem_abox_iff hij]
                        rintro ⟨hw', -, -⟩
                        exact hw hw'
                      rw [hΘzero _ hnot]; ring), integral_zero]
                rw [h0]
            refine le_trans hle3 (le_of_eq ?_)
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
              (Submission.BoseGases.acube_measurable ℓ), MeasureTheory.setIntegral_const,
              Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
              ENNReal.toReal_ofReal (by positivity)]
            simp [smul_eq_mul]
          nlinarith [h1, pow_pos hℓ 3, sq_nonneg B]
        rw [show (fun x' : ChRest i j =>
              ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2)
            = box'.indicator (fun x' : ChRest i j =>
                ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2) from by
          funext x'
          by_cases hx : x' ∈ box'
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx, hsupp x' hx]]
        exact (integrable_indicator_iff hbox'meas).mpr hstep
      have hAmass : (∫ x' : ChRest i j, φ x') ≤ ℓ ^ 3 * Nn := by
        have hpt : ∀ x' : ChRest i j,
            φ x' ≤ ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 := by
          intro x'
          rw [hφdef]
          by_cases hx : x' ∈ box'
          · rw [Set.indicator_of_mem hx]
            calc (∫ w : E3, ‖A w x'‖ ^ 2)
                ≤ ∫ w : E3, ℓ ^ 3 * ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 :=
                  integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => by positivity)
                    (hmajw x') (Filter.Eventually.of_forall fun w => hAcs w x')
              _ = ℓ ^ 3 * ∫ w : E3, ∫ w' : E3, (Θ (chCcfg i j w w' x')) ^ 2 :=
                  MeasureTheory.integral_const_mul _ _
          · rw [Set.indicator_of_notMem hx]
            exact mul_nonneg (by positivity)
              (integral_nonneg fun w => integral_nonneg fun w' => by positivity)
        calc (∫ x' : ChRest i j, φ x')
            ≤ ∫ x' : ChRest i j, ℓ ^ 3 * ∫ w : E3, ∫ w' : E3,
                (Θ (chCcfg i j w w' x')) ^ 2 :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall hφnn) hmajbox
                (Filter.Eventually.of_forall hpt)
          _ = ℓ ^ 3 * ∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3,
                (Θ (chCcfg i j w w' x')) ^ 2 := MeasureTheory.integral_const_mul _ _
          _ = ℓ ^ 3 * Nn := by rw [hThetaId]
      -- ### integrability of `φ`
      have hA_w_asm : AEStronglyMeasurable (fun x' : ChRest i j => ∫ w : E3, ‖A w x'‖ ^ 2)
          (volume : Measure (ChRest i j)) := by
        have h1 : AEStronglyMeasurable (fun p : ChRest i j × E3 => ‖A p.2 p.1‖ ^ 2)
            ((volume : Measure (ChRest i j)).prod (volume : Measure E3)) :=
          (hAasmj.norm.pow 2)
        exact h1.integral_prod_right'
      have hφint : Integrable φ (volume : Measure (ChRest i j)) := by
        rw [hφdef, integrable_indicator_iff hbox'meas]
        refine IntegrableOn.of_bound hbox'fin hA_w_asm.restrict ((B * ℓ ^ 3) ^ 2 * ℓ ^ 3) ?_
        filter_upwards with x'
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w => by positivity)]
        have hmaj4 : Integrable (fun w : E3 => (B * ℓ ^ 3) ^ 2 *
            (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) w)
            (volume : Measure E3) :=
          ((integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr
            (IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
              aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp))).const_mul
            ((B * ℓ ^ 3) ^ 2)
        have hle4 : (∫ w : E3, ‖A w x'‖ ^ 2)
            ≤ ∫ w : E3, (B * ℓ ^ 3) ^ 2 * (Submission.BoseGases.acube ℓ).indicator
                (fun _ => (1 : ℝ)) w := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => by positivity) hmaj4
            (Filter.Eventually.of_forall fun w => ?_)
          beta_reduce
          by_cases hw : w ∈ Submission.BoseGases.acube ℓ
          · rw [Set.indicator_of_mem hw, mul_one]
            nlinarith [hAcore w x', norm_nonneg (A w x')]
          · rw [Set.indicator_of_notMem hw, mul_zero, hAacube w x' hw]; simp
        refine le_trans hle4 (le_of_eq ?_)
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
          (Submission.BoseGases.acube_measurable ℓ), MeasureTheory.setIntegral_const,
          Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
          ENNReal.toReal_ofReal (by positivity)]
        simp [smul_eq_mul]
      -- ### the mass bound for `ψ`
      have hpsipoint : ∀ x' : ChRest i j,
          ψ x' ≤ (box'.indicator (fun _ => (1 : ℝ))) x' *
            ∫ z in Submission.BoseGases.acube ℓ, (Ψ (chCcfg i j 0 z x')) ^ 2 := by
        intro x'
        rw [hψdef]
        by_cases hx : x' ∈ box'
        · have hL : (box'.indicator (fun x' => ∫ z : E3, ‖gfun z x'‖ ^ 2)) x'
              = ∫ z : E3, ‖gfun z x'‖ ^ 2 := Set.indicator_of_mem hx _
          have hR : (box'.indicator (fun _ => (1 : ℝ))) x' = 1 := by
            rw [Set.indicator_of_mem hx]
          rw [hL, hR, one_mul]
          have hfib : Measurable (fun u : E3 => Ψ (chCcfg i j 0 u x')) :=
            hΨm.comp (measurable_chCcfg_second (i := i) (j := j) 0 x')
          have h1 := oneSlot_lowMult_sq_integral_le (fc := fc) (κ := κ) (ℓ := ℓ) (C := 2 * B)
            hκ hℓ (by positivity) hfib (fun u _ => hΨglob _)
          have h2 : (∫ z : E3, ‖gfun z x'‖ ^ 2)
              = ∫ z in Submission.BoseGases.acube ℓ,
                  (Work.BoseBoxFix.lowMult fc κ ℓ
                    (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2 := by
            have hpt : ∀ z : E3, ‖gfun z x'‖ ^ 2
                = (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Work.BoseBoxFix.lowMult fc κ ℓ
                      (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2) z := by
              intro z
              by_cases hz : z ∈ Submission.BoseGases.acube ℓ
              · have hL : gfun z x' = ((G (chCcfg i j 0 z x') : ℝ) : ℂ) := by
                  rw [hgdef]
                  exact Set.indicator_of_mem hz _
                have hR : (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Work.BoseBoxFix.lowMult fc κ ℓ
                      (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2) z
                    = (Work.BoseBoxFix.lowMult fc κ ℓ
                        (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2 :=
                  Set.indicator_of_mem hz _
                have hG : G (chCcfg i j 0 z x')
                    = Work.BoseBoxFix.lowMult fc κ ℓ (fun u : E3 => Ψ (chCcfg i j 0 u x')) z := by
                  rw [hGdef]
                  simp only [Work.BoseBoxFix.lowSlot, chCcfg_j hij]
                  congr 1
                  funext u
                  rw [chCcfg_update_j hij]
                rw [hL, hR, Complex.norm_real, Real.norm_eq_abs, sq_abs, hG]
              · have hL : gfun z x' = 0 := by
                  rw [hgdef]
                  exact Set.indicator_of_notMem hz _
                have hR : (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Work.BoseBoxFix.lowMult fc κ ℓ
                      (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2) z = 0 :=
                  Set.indicator_of_notMem hz _
                rw [hL, hR]
                simp
            rw [show (∫ z : E3, ‖gfun z x'‖ ^ 2)
                = ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Work.BoseBoxFix.lowMult fc κ ℓ
                      (fun u : E3 => Ψ (chCcfg i j 0 u x')) z) ^ 2) z from
              integral_congr_ae (Filter.Eventually.of_forall hpt)]
            rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
          rw [h2]
          exact h1
        · have hL : (box'.indicator (fun x' => ∫ z : E3, ‖gfun z x'‖ ^ 2)) x' = 0 :=
            Set.indicator_of_notMem hx _
          have hR : (box'.indicator (fun _ => (1 : ℝ))) x' = 0 :=
            Set.indicator_of_notMem hx _
          rw [hL, hR, zero_mul]
      have hVle : ∀ x' : ChRest i j,
          (∫ z in Submission.BoseGases.acube ℓ, (Ψ (chCcfg i j 0 z x')) ^ 2) ≤ (2 * B) ^ 2 * ℓ ^ 3 := by
        intro x'
        haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
          ⟨by rw [Measure.restrict_apply_univ];
              exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
        calc (∫ z in Submission.BoseGases.acube ℓ, (Ψ (chCcfg i j 0 z x')) ^ 2)
            ≤ ∫ z in Submission.BoseGases.acube ℓ, (2 * B) ^ 2 := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
                (integrable_const _) (Filter.Eventually.of_forall fun z => ?_)
              beta_reduce
              nlinarith [hΨglob (chCcfg i j 0 z x'), abs_nonneg (Ψ (chCcfg i j 0 z x')),
                sq_abs (Ψ (chCcfg i j 0 z x'))]
          _ = (2 * B) ^ 2 * ℓ ^ 3 := by
              rw [MeasureTheory.setIntegral_const, Measure.real_def,
                Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
              simp [smul_eq_mul]
              ring
      have hψle : ∀ x' : ChRest i j,
          ψ x' ≤ (box'.indicator (fun _ => (1 : ℝ))) x' * ((2 * B) ^ 2 * ℓ ^ 3) := by
        intro x'
        exact le_trans (hpsipoint x') (mul_le_mul_of_nonneg_left (hVle x')
          (Set.indicator_nonneg (fun _ _ => zero_le_one) x'))
      -- ### measurability of `ψ`
      have hψ_asm : AEStronglyMeasurable ψ (volume : Measure (ChRest i j)) := by
        rw [hψdef]
        refine AEStronglyMeasurable.indicator ?_ hbox'meas
        have hgm : Measurable (fun p : ChRest i j × E3 => gfun p.2 p.1) := by
          change Measurable (fun p : ChRest i j × E3 =>
            (Submission.BoseGases.acube ℓ).indicator
              (fun z => ((G (chCcfg i j 0 z p.1) : ℝ) : ℂ)) p.2)
          have hsetm : MeasurableSet
              {p : ChRest i j × E3 | p.2 ∈ Submission.BoseGases.acube ℓ} :=
            MeasurableSet.preimage (f := fun p : ChRest i j × E3 => p.2)
              (Submission.BoseGases.acube_measurable ℓ) measurable_snd
          have hbase : Measurable (fun p : ChRest i j × E3 =>
              ((G (chCcfg i j 0 p.2 p.1) : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.measurable.comp
              (hGm.comp (measurable_chCcfg_xz (i := i) (j := j)))
          exact hbase.indicator hsetm
        have hjoint : AEStronglyMeasurable (fun p : ChRest i j × E3 => ‖gfun p.2 p.1‖ ^ 2)
            ((volume : Measure (ChRest i j)).prod (volume : Measure E3)) :=
          ((hgm.norm).pow_const 2).aestronglyMeasurable
        exact hjoint.integral_prod_right'
      have hψint : Integrable ψ (volume : Measure (ChRest i j)) := by
        refine Integrable.mono'
          (f := ψ)
          (g := fun x' : ChRest i j =>
            (box'.indicator (fun _ => (1 : ℝ))) x' * ((2 * B) ^ 2 * ℓ ^ 3)) ?_ hψ_asm ?_
        · refine ((integrable_indicator_iff hbox'meas).mpr
            (IntegrableOn.of_bound hbox'fin aestronglyMeasurable_const (1 : ℝ)
              (Filter.Eventually.of_forall fun x => by simp))).mul_const ((2 * B) ^ 2 * ℓ ^ 3)
        · filter_upwards with x'
          rw [Real.norm_eq_abs, abs_of_nonneg (hψnn x')]
          exact hψle x'
      -- ### the mass bound for `ψ`, via the collapse of the `i`-slot
      have hψmass : (∫ x' : ChRest i j, ψ x') ≤ Nn / ℓ ^ 3 := by
        have hΨint : Integrable (fun x : Submission.BoseGases.X (m+2) =>
            (Submission.BoseGases.abox (m+2) ℓ).indicator (fun x => (Ψ x) ^ 2) x)
            (volume : Measure (Submission.BoseGases.X (m+2))) := by
          rw [integrable_indicator_iff (Submission.BoseGases.abox_measurable (m+2) ℓ)]
          refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (m+2) ℓ hℓ.le) ?_
            ((2 * B) ^ 2) ?_
          · exact ((hΨm.pow_const 2).aestronglyMeasurable).restrict
          · filter_upwards [MeasureTheory.ae_restrict_mem
              (Submission.BoseGases.abox_measurable (m+2) ℓ)] with x hx
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hΨglob x, abs_nonneg (Ψ x), sq_abs (Ψ x)]
        have hPsi2 : (∫ x in Submission.BoseGases.abox (m+2) ℓ, (Ψ x) ^ 2) ≤ Nn := by
          rw [hNndef]
          exact aQ_aP_sq_integral_le hℓ hij hΘL2
        have hcoll := abox_integral_slot_collapse (i := i) (j := j) hij hℓ hΨm hΨi hΨint
        have hΨzero : ∀ y : Submission.BoseGases.X (m+2),
            (∃ k : Fin (m+2), k ≠ i ∧ k ≠ j ∧ y k ∉ Submission.BoseGases.acube ℓ) → Ψ y = 0 := by
          intro y hy
          obtain ⟨k, hki, hkj, hky⟩ := hy
          have hPz : ∀ x : Submission.BoseGases.X (m+2),
              (∃ k : Fin (m+2), k ≠ i ∧ k ≠ j ∧ x k ∉ Submission.BoseGases.acube ℓ) →
              Submission.BoseGases.aP ℓ i Θ x = 0 := by
            intro x hx
            obtain ⟨k, hki, hkj, hkx⟩ := hx
            rw [Submission.BoseGases.aP]
            have h0 : (∫ y' in Submission.BoseGases.acube ℓ, Θ (Function.update x i y')) = 0 := by
              rw [show (∫ y' in Submission.BoseGases.acube ℓ, Θ (Function.update x i y'))
                  = ∫ _ in Submission.BoseGases.acube ℓ, (0 : ℝ) from
                MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
                  (fun y' _ => by
                    have hmem : Function.update x i y' ∉ Submission.BoseGases.abox (m+2) ℓ := by
                      intro hcon
                      exact hkx (by
                        have h1 : (Function.update x i y') k ∈ Submission.BoseGases.acube ℓ := hcon k
                        rwa [Function.update_apply, if_neg hki] at h1)
                    rw [hΘzero _ hmem])]
              simp
            rw [h0, mul_zero]
          have hP : Submission.BoseGases.aP ℓ i Θ y = 0 := hPz y ⟨k, hki, hkj, hky⟩
          have hQ : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) y = 0 := by
            rw [Submission.BoseGases.aP]
            have h0 : (∫ y' in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.aP ℓ i Θ (Function.update y j y')) = 0 := by
              rw [show (∫ y' in Submission.BoseGases.acube ℓ,
                  Submission.BoseGases.aP ℓ i Θ (Function.update y j y'))
                  = ∫ _ in Submission.BoseGases.acube ℓ, (0 : ℝ) from
                MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
                  (fun y' _ => hPz (Function.update y j y') ⟨k, hki, hkj, by
                    intro hcon
                    exact hky (by
                      have h1 : (Function.update y j y') k ∈ Submission.BoseGases.acube ℓ := hcon
                      rwa [Function.update_apply, if_neg hkj] at h1)⟩)]
              simp
            rw [h0, mul_zero]
          rw [hΨdef, Submission.BoseGases.aQ, hP, hQ]
          ring
        have hVzero : ∀ x' : ChRest i j, x' ∉ box' →
            (∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
              (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) = 0 := by
          intro x' hx'
          have hx'2 : ∃ k : {k : Fin (m+2) // k ≠ i ∧ k ≠ j},
              x' k ∉ Submission.BoseGases.acube ℓ := by
            by_contra hcon
            push Not at hcon
            exact hx' (by rw [hboxdef, Set.mem_univ_pi]; exact hcon)
          obtain ⟨k, hk⟩ := hx'2
          have hz : ∀ z : E3, (Submission.BoseGases.acube ℓ).indicator
              (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z = 0 := by
            intro z
            by_cases hz' : z ∈ Submission.BoseGases.acube ℓ
            · rw [Set.indicator_of_mem hz']
              rw [hΨzero (chCcfg i j 0 z x') ⟨k.1, k.2.1, k.2.2, by
                rw [chCcfg_other (i := i) (j := j) (0 : E3) z x' k.2.1 k.2.2]
                exact hk⟩]
              ring
            · rw [Set.indicator_of_notMem hz']
          rw [show (∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) = ∫ _ : E3, (0 : ℝ) from
              integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero]
        have hVasm : AEStronglyMeasurable (fun x' : ChRest i j =>
              ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) (volume : Measure (ChRest i j)) := by
          have hjoint : AEStronglyMeasurable
              (fun p : ChRest i j × E3 => (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z p.1)) ^ 2) p.2)
              ((volume : Measure (ChRest i j)).prod (volume : Measure E3)) := by
            have hsetm : MeasurableSet
                {p : ChRest i j × E3 | p.2 ∈ Submission.BoseGases.acube ℓ} :=
              MeasurableSet.preimage (f := fun p : ChRest i j × E3 => p.2)
                (Submission.BoseGases.acube_measurable ℓ) measurable_snd
            have hbase : Measurable (fun p : ChRest i j × E3 =>
                (Ψ (chCcfg i j 0 p.2 p.1)) ^ 2) :=
              (hΨm.comp (measurable_chCcfg_xz (i := i) (j := j))).pow_const 2
            exact (hbase.indicator hsetm).aestronglyMeasurable
          exact hjoint.integral_prod_right'
        have hVint : Integrable (fun x' : ChRest i j =>
              ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) (volume : Measure (ChRest i j)) := by
          refine Integrable.mono'
            (f := fun x' : ChRest i j => ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z)
            (g := fun x' : ChRest i j =>
              (box'.indicator (fun _ => (1 : ℝ))) x' * ((2 * B) ^ 2 * ℓ ^ 3)) ?_ hVasm ?_
          · exact ((integrable_indicator_iff hbox'meas).mpr
              (IntegrableOn.of_bound hbox'fin aestronglyMeasurable_const (1 : ℝ)
                (Filter.Eventually.of_forall fun x => by simp))).mul_const ((2 * B) ^ 2 * ℓ ^ 3)
          · filter_upwards with x'
            by_cases hx : x' ∈ box'
            · have hb : ‖(fun x' : ChRest i j => ∫ z : E3,
                  (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) x'‖ ≤ (2 * B) ^ 2 * ℓ ^ 3 := by
                have hnn : 0 ≤ ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z :=
                  integral_nonneg fun z =>
                    Set.indicator_nonneg (fun a _ => sq_nonneg (Ψ (chCcfg i j 0 a x'))) z
                beta_reduce
                rw [Real.norm_eq_abs, abs_of_nonneg hnn]
                rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
                exact hVle x'
              rw [Set.indicator_of_mem hx, one_mul]
              exact hb
            · rw [hVzero x' hx, norm_zero, Set.indicator_of_notMem hx, zero_mul]
        have hVint' : Integrable (fun x' : ChRest i j =>
              (box'.indicator (fun _ => (1 : ℝ))) x' * ∫ z : E3,
                (Submission.BoseGases.acube ℓ).indicator
                  (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z) (volume : Measure (ChRest i j)) := by
          refine hVint.congr (Filter.Eventually.of_forall fun x' => ?_)
          beta_reduce
          by_cases hx : x' ∈ box'
          · rw [Set.indicator_of_mem hx, one_mul]
          · rw [hVzero x' hx, Set.indicator_of_notMem hx, zero_mul]
        have hstep1 : (∫ x' : ChRest i j, ψ x') ≤ ∫ x' : ChRest i j,
            (box'.indicator (fun _ => (1 : ℝ))) x' * ∫ z : E3,
              (Submission.BoseGases.acube ℓ).indicator (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall hψnn) hVint'
            (Filter.Eventually.of_forall fun x' => ?_)
          beta_reduce
          exact le_trans (hpsipoint x') (mul_le_mul_of_nonneg_left (le_of_eq
            (MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)).symm)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) x'))
        have hstep2 : (∫ x' : ChRest i j, (box'.indicator (fun _ => (1 : ℝ))) x' *
              ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z)
            = (∫ x in Submission.BoseGases.abox (m+2) ℓ, (Ψ x) ^ 2) / ℓ ^ 3 := by
          have e1 : (∫ x' : ChRest i j, (box'.indicator (fun _ => (1 : ℝ))) x' *
                ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                  (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z)
              = ∫ x' : ChRest i j, (box'.indicator (fun _ => (1 : ℝ))) x' *
                  ∫ z in Submission.BoseGases.acube ℓ, (Ψ (chCcfg i j 0 z x')) ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
            beta_reduce
            rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
          rw [e1, hcoll, eq_div_iff (ne_of_gt (pow_pos hℓ 3))]
          ring
        calc (∫ x' : ChRest i j, ψ x')
              ≤ ∫ x' : ChRest i j, (box'.indicator (fun _ => (1 : ℝ))) x' *
                  ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator
                    (fun z => (Ψ (chCcfg i j 0 z x')) ^ 2) z := hstep1
            _ = (∫ x in Submission.BoseGases.abox (m+2) ℓ, (Ψ x) ^ 2) / ℓ ^ 3 := hstep2
            _ ≤ Nn / ℓ ^ 3 := div_le_div_of_nonneg_right hPsi2 (by positivity)
      -- ### the identification of `Nn` with `normB`
      have hell : ℓ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
        rw [hℓdef]
        unfold Work.BoseBoxFock.ellH
        rw [if_pos (sideAt_pos' hμ hav)]
      have hNn : Nn = Work.BoseBoxFix.normB v μ (m+2) Φ := by
        rw [hNndef, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hell]
        refine integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (Submission.BoseGases.abox_measurable (m+2)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] with x hx
        rw [hΘbox x (by rw [← hell] at hx; exact hx)]
      have hmaj : Integrable (fun x' : ChRest i j =>
          P * (2⁻¹ * (φ x' / ℓ ^ 3 + ℓ ^ 3 * ψ x')))
          (volume : Measure (ChRest i j)) := by
        have h1 : Integrable (fun x' : ChRest i j => φ x' / ℓ ^ 3 + ℓ ^ 3 * ψ x')
            (volume : Measure (ChRest i j)) :=
          (hφint.div_const (ℓ ^ 3)).add (hψint.const_mul (ℓ ^ 3))
        exact (h1.const_mul (2⁻¹)).const_mul P
      have hpt : ∀ x' : ChRest i j,
          ‖∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x')‖
            ≤ P * (2⁻¹ * (φ x' / ℓ ^ 3 + ℓ ^ 3 * ψ x')) := by
        intro x'
        refine le_trans (hperx x') (mul_le_mul_of_nonneg_left
          (sqrt_mul_sqrt_le_half hℓ (hφnn x') (hψnn x')) hP0)
      have hchC_le : ‖chCslot v h fc fu μ N i j Θ‖ ≤ P * Nn := by
        rw [hchC, hpeel]
        calc ‖∫ x' : ChRest i j, ∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x')‖
            ≤ ∫ x' : ChRest i j, ‖∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x')‖ := by
              simpa only [] using norm_integral_le_integral_norm
                (fun x' : ChRest i j => ∫ w : E3, ∫ w' : E3, H (chCcfg i j w w' x'))
          _ ≤ ∫ x' : ChRest i j, P * (2⁻¹ * (φ x' / ℓ ^ 3 + ℓ ^ 3 * ψ x')) :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun x' => norm_nonneg _)
                hmaj (Filter.Eventually.of_forall hpt)
          _ = P * 2⁻¹ * ((∫ x' : ChRest i j, φ x') / ℓ ^ 3
                + ℓ ^ 3 * ∫ x' : ChRest i j, ψ x') := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
                MeasureTheory.integral_add (hφint.div_const _) (hψint.const_mul _),
                MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
              ring
          _ ≤ P * Nn := by
              have hbow : (∫ x' : ChRest i j, φ x') / ℓ ^ 3 ≤ Nn := by
                rw [div_le_iff₀ (by positivity)]
                linarith [hAmass]
              have hbow2 : ℓ ^ 3 * (∫ x' : ChRest i j, ψ x') ≤ Nn := by
                have h3 := hψmass
                rw [le_div_iff₀ (by positivity)] at h3
                linarith [h3]
              nlinarith [hbow, hbow2, mul_nonneg hP0 (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      have hmain : ‖chCslot v h fc fu μ N i j Θ‖
          ≤ 1 * (P * (1 + ℓ ^ 3)) * Work.BoseBoxFix.normB v μ (m+2) Φ := by
        refine le_trans hchC_le ?_
        rw [hNn]
        have hPnn : 0 ≤ P * Work.BoseBoxFix.normB v μ (m+2) Φ := mul_nonneg hP0 hnormBnn
        nlinarith [hPnn, pow_pos hℓ 3]
      exact hmain
    · rw [hchC, MeasureTheory.integral_undef hInt, norm_zero]
      exact mul_nonneg (mul_nonneg zero_le_one (mul_nonneg hP0 (by positivity))) hnormBnn
  · push Not at hP0
    exfalso
    set f : E3 → ℂ := (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℂ)) with hfdef
    have hfm : MemLp f 2 (volume : Measure E3) := by
      rw [hfdef]
      exact MeasureTheory.memLp_indicator_const 2 (Submission.BoseGases.acube_measurable ℓ)
        (1 : ℂ) (Or.inr (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)))
    have hb := hP f f hfm hfm
    have hsq : (∫ w : E3, ‖f w‖ ^ 2) = ℓ ^ 3 := by
      have hfun : (fun w : E3 => ‖f w‖ ^ 2)
          = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) := by
        funext w
        rw [hfdef]
        by_cases hw : w ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]; simp
        · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]; simp
      rw [hfun, MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ),
        MeasureTheory.setIntegral_const, Measure.real_def,
        Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
      simp [smul_eq_mul]
    rw [hsq] at hb
    have hsqr : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 :=
      Real.mul_self_sqrt (by positivity)
    have hsqpos : 0 < Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) := by rw [hsqr]; positivity
    nlinarith [hb, norm_nonneg (∫ w : E3, ∫ z : E3, f w * ((χ w : ℝ) : ℂ)
        * chD v h μ fu N (w - z) * ((χ z : ℝ) : ℂ) * f z), hsqpos, hP0]

end Work.BoseBoxFock.PCFU
