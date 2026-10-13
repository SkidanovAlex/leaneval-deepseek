import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.MismatchSummand
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotProd
import Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option quotPrecheck false in
local notation "PM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

/-! ## Elementary facts about the open quadrant and the leaf weights -/

/-- A.e. point of the product measure `PM` lies in the open quadrant. -/
theorem ae_Qd_PM : ∀ᵐ p ∂PM, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))]
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)).symm
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    (fun p hp => hp)

theorem sin_pos_of_Qd {θ : ℝ} (h : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `CoefTh l V` is nonnegative on the honest class `CoefThMem l V`. -/
theorem coefTh_nonneg_of_mem {l : ℕ} {V : ℝ → ℝ → ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem l V) : 0 ≤ Work.FTS.VocabO.CoefTh l V := by
  rw [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  by_cases hbi : b + i ≤ l
  · rw [if_pos hbi]
    obtain ⟨M, hM⟩ := hmem b i hbi
    exact le_trans (abs_nonneg _) (Work.FTS.H2.le_supAbsO one_pos one_pos
      (by linarith [Real.pi_gt_three]) hM)
  · rw [if_neg hbi]

theorem leafEta_eq_canonW : Work.FTS.TransportS.leafEta
    = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta := rfl

theorem leafGam_eq_canonW (α : ℝ) : Work.FTS.TransportS.leafGam α
    = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl

theorem leafOne_eq_canonW_zero : Work.FTS.TransportS.leafOne
    = Work.FTS.TransportS.SlotT2.canonW 0 := by
  funext z θ
  simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, Real.rpow_zero]

/-- `leafOne = w²` is pointwise dominated by `leafEta = w² sin(2θ)^{-η}` on the open interval. -/
theorem leafOne_le_leafEta {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.TransportS.leafEta z θ := by
  have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
  simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.leafEta]
  exact le_mul_of_one_le_right (sq_nonneg _) h1

/-! ## Dominations of the `f`-slots by the `ℋ⁶`-integrand, at a reduced weight -/

/-- The pure slot with any weight `sin(2θ)^{-q}`, `q ≤ η`, of order `≤ 6`, is pointwise
dominated by `HkIntegrand α 6 f`. -/
theorem canonW_pure_le_Hk {α q : ℝ} {f : ℝ → ℝ → ℝ} {j : ℕ} (hq : q ≤ Work.Spaces.eta)
    (hj : j ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have h := Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int
    (α := α) (q := q) (h := f) (z := z) (θ := θ) hq hθ j hj
  simpa only [Work.FTS.TransportS.SlotT2.canonW] using h

/-- The mixed slot with any weight `sin(2θ)^{-q}`, `q ≤ γ`, of order `≤ 6`, is pointwise
dominated by `HkIntegrand α 6 f`. -/
theorem canonW_mixed_le_Hk {α q : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ} (hq : q ≤ Work.Spaces.gam α)
    (hi : 1 ≤ i) (hij : i + j ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have h := Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int
    (α := α) (q := q) (h := f) (z := z) (θ := θ) hq hθ j i hi hij
  simpa only [Work.FTS.TransportS.SlotT2.canonW] using h

/-- Measurability of a weighted slot square on `PM`. -/
theorem aesm_slot {q : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) PM := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.TransportS.SlotT2.continuousOn_canonW q
  have h2 := Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf j i
  exact Work.Spaces.aesm_of_continuousOn_Qd _ (h1.mul (h2.pow 2))

/-- Measurability of a `mixed` derivative on `PM`. -/
theorem aesm_mixed {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) PM :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf j i)

/-- Integrability of the `η`-weighted pure slots (from `HkMem`). -/
theorem integrable_canonW_eta_pure {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j : ℕ} (hj : j ≤ 6) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f p.1 p.2) ^ 2) PM :=
  (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hf hm).1 j hj

/-- Integrability of the `γ`-weighted mixed slots (from `HkMem`). -/
theorem integrable_canonW_gam_mixed {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j i : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) PM :=
  (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hf hm).2 j i hi hij

/-- Integrability of the `η`-weighted pure slots of order `≤ 7` (from `HkMem α 7`). -/
theorem integrable_canonW_eta_pure7 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 7 f) {j : ℕ} (hj : j ≤ 7) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f p.1 p.2) ^ 2) PM :=
  (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hf hm).1 j hj

/-- Integrability of the `γ`-weighted mixed slots of order `≤ 7` (from `HkMem α 7`). -/
theorem integrable_canonW_gam_mixed7 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 7 f) {j i : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ 7) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) PM :=
  (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hf hm).2 j i hi hij

/-- Integrability of a pure slot at a reduced weight `q ≤ η`. -/
theorem integrable_canonW_pure {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j : ℕ} (hj : j ≤ 6)
    (hq : q ≤ Work.Spaces.eta) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Work.Spaces.DzIter j f p.1 p.2) ^ 2) PM := by
  refine Integrable.mono' (integrable_canonW_eta_pure hf hm hj)
    (by simpa only [Work.Spaces.mixed_zero_right] using aesm_slot (q := q) (j := j) (i := 0) hf) ?_
  filter_upwards [ae_Qd_PM] with p hp
  have hs : 0 < Real.sin (2 * p.2) := sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩
  have h0 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg (le_of_lt hs) _
  have h2 : 0 ≤ (Work.Spaces.DzIter j f p.1 p.2) ^ 2 := sq_nonneg _
  have hw : (Real.sin (2 * p.2)) ^ (-q) ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_exponent_ge hs (sin_two_le_one p.2) (by linarith [hq])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h0 h1) h2)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw h0) h2

/-- Integrability of a mixed slot at a reduced weight `q ≤ γ`. -/
theorem integrable_canonW_mixed {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ 6) (hq : q ≤ Work.Spaces.gam α) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) PM := by
  refine Integrable.mono' (integrable_canonW_gam_mixed hf hm hi hij)
    (aesm_slot (q := q) (j := j) (i := i) hf) ?_
  filter_upwards [ae_Qd_PM] with p hp
  have hs : 0 < Real.sin (2 * p.2) := sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩
  have h0 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg (le_of_lt hs) _
  have h2 : 0 ≤ (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := sq_nonneg _
  have hw : (Real.sin (2 * p.2)) ^ (-q) ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_le_rpow_of_exponent_ge hs (sin_two_le_one p.2) (by linarith [hq])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h0 h1) h2)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw h0) h2

/-- Integrability of a pure slot of order `≤ 7` at a reduced weight `q ≤ η`. -/
theorem integrable_canonW_pure7 {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 7 f) {j : ℕ} (hj : j ≤ 7)
    (hq : q ≤ Work.Spaces.eta) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Work.Spaces.DzIter j f p.1 p.2) ^ 2) PM := by
  refine Integrable.mono' (integrable_canonW_eta_pure7 hf hm hj)
    (by simpa only [Work.Spaces.mixed_zero_right] using aesm_slot (q := q) (j := j) (i := 0) hf) ?_
  filter_upwards [ae_Qd_PM] with p hp
  have hs : 0 < Real.sin (2 * p.2) := sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩
  have h0 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg (le_of_lt hs) _
  have h2 : 0 ≤ (Work.Spaces.DzIter j f p.1 p.2) ^ 2 := sq_nonneg _
  have hw : (Real.sin (2 * p.2)) ^ (-q) ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_exponent_ge hs (sin_two_le_one p.2) (by linarith [hq])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h0 h1) h2)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw h0) h2

/-- Integrability of a mixed slot of order `≤ 7` at a reduced weight `q ≤ γ`. -/
theorem integrable_canonW_mixed7 {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 7 f) {j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ 7) (hq : q ≤ Work.Spaces.gam α) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) PM := by
  refine Integrable.mono' (integrable_canonW_gam_mixed7 hf hm hi hij)
    (aesm_slot (q := q) (j := j) (i := i) hf) ?_
  filter_upwards [ae_Qd_PM] with p hp
  have hs : 0 < Real.sin (2 * p.2) := sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩
  have h0 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg (le_of_lt hs) _
  have h2 : 0 ≤ (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := sq_nonneg _
  have hw : (Real.sin (2 * p.2)) ^ (-q) ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_le_rpow_of_exponent_ge hs (sin_two_le_one p.2) (by linarith [hq])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h0 h1) h2)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw h0) h2

/-- The `PM`-integral of a weighted pure slot of order `≤ 6` at a reduced weight `q ≤ η` is at
most `HkSq α 6 f`. -/
theorem integral_canonW_pure_le {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j : ℕ} (hj : j ≤ 6)
    (hq : q ≤ Work.Spaces.eta) :
    (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.DzIter j f p.1 p.2) ^ 2 ∂PM) ≤ Work.Spaces.HkSq α 6 f := by
  have hHk := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hf hm
  rw [← hHk.2]
  refine integral_mono_of_nonneg ?_ hHk.1 ?_
  · filter_upwards [ae_Qd_PM] with p hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (le_of_lt (sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩)) _)) (sq_nonneg _)
  · filter_upwards [ae_Qd_PM] with p hp
    exact canonW_pure_le_Hk hq hj ⟨hp.2.1, hp.2.2⟩

/-- The `PM`-integral of a weighted mixed slot of order `≤ 6` at a reduced weight `q ≤ γ` is at
most `HkSq α 6 f`. -/
theorem integral_canonW_mixed_le {α q : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f) {j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ 6) (hq : q ≤ Work.Spaces.gam α) :
    (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 ∂PM) ≤ Work.Spaces.HkSq α 6 f := by
  have hHk := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hf hm
  rw [← hHk.2]
  refine integral_mono_of_nonneg ?_ hHk.1 ?_
  · filter_upwards [ae_Qd_PM] with p hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (le_of_lt (sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩)) _)) (sq_nonneg _)
  · filter_upwards [ae_Qd_PM] with p hp
    exact canonW_mixed_le_Hk hq hi hij ⟨hp.2.1, hp.2.2⟩

/-- **Two-slot AM–GM at the `PM` level.**  If the `w² sin(2θ)^{-q}`-weighted squares of `Y` and
`Z` are integrable with integrals at most `A`, `B`, then any `F` that is pointwise dominated by
`C·(w² sin(2θ)^{-q})|Y||Z|` on the open quadrant is integrable, with `|∫F| ≤ C(A+B)/2`. -/
theorem integral_abs_le_const_mul {q C A B : ℝ} {Y Z F : ℝ → ℝ → ℝ} (hC : 0 ≤ C)
    (hY : Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Y p.1 p.2) ^ 2) PM)
    (hZ : Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Z p.1 p.2) ^ 2) PM)
    (hYA : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Y p.1 p.2) ^ 2 ∂PM) ≤ A)
    (hZA : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Z p.1 p.2) ^ 2 ∂PM) ≤ B)
    (hsmF : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ C * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * |Y z θ| * |Z z θ|)) :
    Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM ∧
      |∫ p, F p.1 p.2 ∂PM| ≤ C * ((A + B) / 2) := by
  have hMaj : Integrable (fun p : ℝ × ℝ => C / 2 * ((Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Y p.1 p.2) ^ 2 + (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Z p.1 p.2) ^ 2)) PM := by
    simpa only [Pi.add_apply] using ((hY.add hZ).const_mul (C / 2))
  have hpt2 : ∀ᵐ p ∂PM, ‖F p.1 p.2‖ ≤ C / 2 * ((Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Y p.1 p.2) ^ 2 + (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Z p.1 p.2) ^ 2) := by
    filter_upwards [ae_Qd_PM] with p hp
    have hs : 0 < Real.sin (2 * p.2) := sin_pos_of_Qd ⟨hp.2.1, hp.2.2⟩
    have h0 : 0 ≤ (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)
    have hAM : 2 * (|Y p.1 p.2| * |Z p.1 p.2|) ≤ (Y p.1 p.2) ^ 2 + (Z p.1 p.2) ^ 2 := by
      nlinarith [sq_abs (Y p.1 p.2), sq_abs (Z p.1 p.2), sq_nonneg (|Y p.1 p.2| - |Z p.1 p.2|)]
    have hAM2 : |Y p.1 p.2| * |Z p.1 p.2|
        ≤ (1 / 2) * ((Y p.1 p.2) ^ 2 + (Z p.1 p.2) ^ 2) := by linarith
    rw [Real.norm_eq_abs]
    calc |F p.1 p.2|
        ≤ C * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
            * |Y p.1 p.2| * |Z p.1 p.2|) := hpt p.1 p.2 hp.1 hp.2.1 hp.2.2
      _ = C * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
            * (|Y p.1 p.2| * |Z p.1 p.2|)) := by ring
      _ ≤ C * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
            * ((1 / 2) * ((Y p.1 p.2) ^ 2 + (Z p.1 p.2) ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM2 h0) hC
      _ = C / 2 * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
            * (Y p.1 p.2) ^ 2 + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
            * (Z p.1 p.2) ^ 2) := by ring
  have hFint : Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM :=
    Integrable.mono' hMaj hsmF hpt2
  refine ⟨hFint, ?_⟩
  have h1 : |∫ p, F p.1 p.2 ∂PM| ≤ ∫ p, C / 2 * ((Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Y p.1 p.2) ^ 2 + (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-q) * (Z p.1 p.2) ^ 2) ∂PM := by
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs (μ := PM)) ?_
    exact integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _) hMaj hpt2
  refine le_trans h1 ?_
  rw [integral_const_mul, integral_add hY hZ]
  have h2 : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Y p.1 p.2) ^ 2 ∂PM) + (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Z p.1 p.2) ^ 2 ∂PM) ≤ A + B := add_le_add hYA hZA
  calc C / 2 * ((∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
          * (Y p.1 p.2) ^ 2 ∂PM) + (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
          * (Z p.1 p.2) ^ 2 ∂PM))
      ≤ C / 2 * (A + B) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * ((A + B) / 2) := by ring


end

end Work.FTS.StrongPersist.H6Row6
