import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBogFS.CleanRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.CleanRiem` — the lattice cell tiling and the Riemann-excess lemma

This module contains the *elementary Riemann machinery* used by the clean row
`Work.BoseBogFS.cleanFun_tsum_le_integral` (FS `lem:BogIntegral`, the lattice-vs-integral
comparison for the clean summand `cleanFun`).

## The setting

For a mesh `h > 0` the dual lattice points are `lpt h n = h • n` (`n : Fin 3 → ℤ`) in
`EuclideanSpace ℝ (Fin 3)`; they are the centres of the half-open cubes

`cell h n = ∏_i [h n_i − h/2, h n_i + h/2)`,

which are pairwise disjoint, measurable, of volume `h³`, and cover the space.

## The excess lemma

`tsum_lpt_sub_integral_le` is the abstract Riemann comparison: if `f` is integrable, its lattice
sum is summable, and the *per-cell oscillation excess*

`f (lpt h n) − (h³)⁻¹ ∫_{cell h n} f`

is dominated by an explicit summable `b n`, then

`∑'_n f (lpt h n) ≤ (h³)⁻¹ ∫ f + ∑'_n b n`.

Its proof is the exact tiling `∫ f = ∑'_n ∫_{cell h n} f` (`MeasureTheory.hasSum_integral_iUnion`)
together with `tsum` arithmetic; the *analytic* content of the clean row is entirely in the
construction of `b`.

## The counting lemma

`card_mul_le` is the elementary lattice count used to sum majorants: `#S·h³` is at most the
volume of the cube of side `2R + h√3 + 2` containing the union of the corresponding cells.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "F3" => Fin 3 → ℝ

/-- The coordinate map `EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)`. -/
def ofE : E3 → F3 := WithLp.ofLp

lemma volume_preserving_ofE : MeasurePreserving ofE volume volume :=
  PiLp.volume_preserving_ofLp (Fin 3)

/-! ## 1. The lattice cubes -/

/-- The dual lattice point of the label `n` at mesh `h`: `h • n`. -/
def lpt (h : ℝ) (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 fun i => h * (n i : ℝ)

/-- The half-open cube of side `h` centred at `lpt h n`. -/
def cell (h : ℝ) (n : Fin 3 → ℤ) : Set E3 :=
  {x | ∀ i, h * (n i : ℝ) - h / 2 ≤ x i ∧ x i < h * (n i : ℝ) + h / 2}

/-- The same cube, described on the coordinate space `Fin 3 → ℝ`. -/
def cellF (h : ℝ) (n : Fin 3 → ℤ) : Set F3 :=
  Set.pi Set.univ fun i => Set.Ico (h * (n i : ℝ) - h / 2) (h * (n i : ℝ) + h / 2)

lemma cell_eq_preimage (h : ℝ) (n : Fin 3 → ℤ) :
    cell h n = ofE ⁻¹' (cellF h n) := by
  ext x
  simp only [ofE, cell, cellF, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    Set.mem_Ico, WithLp.ofLp_toLp, forall_const, true_implies]

lemma mem_cell {h : ℝ} {n : Fin 3 → ℤ} {x : E3} :
    x ∈ cell h n ↔ ∀ i, h * (n i : ℝ) - h / 2 ≤ x i ∧ x i < h * (n i : ℝ) + h / 2 :=
  Iff.rfl

@[simp] lemma lpt_ofLp (h : ℝ) (n : Fin 3 → ℤ) (i : Fin 3) :
    (lpt h n).ofLp i = h * (n i : ℝ) := rfl

lemma measurableSet_cellF (h : ℝ) (n : Fin 3 → ℤ) : MeasurableSet (cellF h n) := by
  rw [cellF]
  exact MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ico

lemma measurableSet_cell (h : ℝ) (n : Fin 3 → ℤ) : MeasurableSet (cell h n) := by
  rw [cell_eq_preimage]
  exact (measurableSet_cellF h n).preimage volume_preserving_ofE.measurable

lemma cell_pairwise_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (cell h)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  intro x hxn hxm
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
    by_contra h
    push_neg at h
    exact hnm (funext h)
  rw [mem_cell] at hxn hxm
  obtain ⟨h1, h2⟩ := hxn i
  obtain ⟨h3, h4⟩ := hxm i
  rcases lt_trichotomy (n i) (m i) with hlt | heq | hgt
  · have hm : (n i : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast hlt
    nlinarith
  · exact hi heq
  · have hm : (m i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast hgt
    nlinarith

lemma iUnion_cellF_eq_univ {h : ℝ} (hh : 0 < h) : (⋃ n, cellF h n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨fun i => ⌊x i / h + 1 / 2⌋, ?_⟩
  simp only [cellF, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_const, true_implies]
  intro i
  set n : ℤ := ⌊x i / h + 1 / 2⌋ with hn
  have h1 : (n : ℝ) ≤ x i / h + 1 / 2 := Int.floor_le _
  have h2 : x i / h + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have h3 : ((n : ℝ) - 1 / 2) * h ≤ (x i / h) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    rw [div_mul_cancel₀ _ (ne_of_gt hh)] at h3
    nlinarith
  · have h3 : (x i / h) * h < ((n : ℝ) + 1 / 2) * h :=
      mul_lt_mul_of_pos_right (by linarith) hh
    rw [div_mul_cancel₀ _ (ne_of_gt hh)] at h3
    nlinarith

lemma iUnion_cell_eq_univ {h : ℝ} (hh : 0 < h) : (⋃ n, cell h n) = Set.univ := by
  have h1 : (⋃ n, cell h n) = ofE ⁻¹' (⋃ n, cellF h n) := by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun n => cell_eq_preimage h n
  rw [h1, iUnion_cellF_eq_univ hh, Set.preimage_univ]

lemma volume_cellF {h : ℝ} (hh : 0 < h) (n : Fin 3 → ℤ) :
    volume (cellF h n) = ENNReal.ofReal (h ^ 3) := by
  rw [cellF, Real.volume_pi_Ico]
  have hstep : ∀ i : Fin 3,
      ENNReal.ofReal (h * (n i : ℝ) + h / 2 - (h * (n i : ℝ) - h / 2)) = ENNReal.ofReal h := by
    intro i
    ring_nf
  rw [Finset.prod_congr rfl fun i _ => hstep i]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hh.le 3]

lemma volume_cell {h : ℝ} (hh : 0 < h) (n : Fin 3 → ℤ) :
    volume (cell h n) = ENNReal.ofReal (h ^ 3) := by
  have h := volume_preserving_ofE.measure_preimage (s := cellF h n)
    (measurableSet_cellF h n).nullMeasurableSet
  rw [cell_eq_preimage, h]
  exact volume_cellF hh n

lemma volume_cell_toReal {h : ℝ} (hh : 0 < h) (n : Fin 3 → ℤ) :
    (volume (cell h n)).toReal = h ^ 3 := by
  rw [volume_cell hh n, ENNReal.toReal_ofReal (by positivity)]

lemma setIntegral_cell_const {h : ℝ} (hh : 0 < h) (n : Fin 3 → ℤ) (c : ℝ) :
    (∫ x in cell h n, c) = h ^ 3 * c := by
  rw [setIntegral_const, measureReal_def, volume_cell_toReal hh n, smul_eq_mul]

/-- The cube is contained in the ball of radius `h√3/2` about its centre. -/
lemma norm_sub_lpt_le {h : ℝ} (hh : 0 < h) {n : Fin 3 → ℤ} {x : E3} (hx : x ∈ cell h n) :
    ‖x - lpt h n‖ ≤ h * Real.sqrt 3 / 2 := by
  have h1 : ∀ i, |x i - h * (n i : ℝ)| ≤ h / 2 := by
    intro i
    obtain ⟨ha, hb⟩ := hx i
    rw [abs_le]
    constructor <;> linarith
  have h2 : ‖x - lpt h n‖ ^ 2 ≤ 3 * (h / 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖(x - lpt h n).ofLp i‖ ^ 2
        = ∑ i : Fin 3, (x i - h * (n i : ℝ)) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [PiLp.sub_apply, lpt_ofLp, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ _i : Fin 3, (h / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [sq_le_sq, abs_of_nonneg (by positivity : (0:ℝ) ≤ h/2)]
          exact h1 i
      _ = 3 * (h / 2) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : ‖x - lpt h n‖ ≤ h / 2 * Real.sqrt 3 := by
    have hnn : 0 ≤ ‖x - lpt h n‖ := norm_nonneg _
    have hle : ‖x - lpt h n‖ ≤ Real.sqrt (3 * (h / 2) ^ 2) := by
      rw [← Real.sqrt_sq hnn]
      exact Real.sqrt_le_sqrt h2
    have hsq : (h / 2 * Real.sqrt 3) ^ 2 = 3 * (h / 2) ^ 2 := by rw [mul_pow, hs3]; ring
    calc ‖x - lpt h n‖ ≤ Real.sqrt (3 * (h / 2) ^ 2) := hle
      _ = h / 2 * Real.sqrt 3 := by rw [← hsq, Real.sqrt_sq (by positivity)]
  nlinarith [key]

/-! ## 2. The Riemann excess lemma -/

/-- **The exact tiling of the integral by the lattice cubes.**
`∫ f = ∑'_n ∫_{cell h n} f`. -/
theorem hasSum_integral_cell {h : ℝ} (hh : 0 < h) {f : E3 → ℝ} (hf : Integrable f) :
    HasSum (fun n : Fin 3 → ℤ => ∫ x in cell h n, f x) (∫ x, f x) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := f) (s := cell h)
    (fun n => measurableSet_cell h n) (cell_pairwise_disjoint hh)
    (show IntegrableOn f (⋃ n, cell h n) volume from by
      rw [iUnion_cell_eq_univ hh]
      simpa only [IntegrableOn, Measure.restrict_univ] using hf)
  rwa [iUnion_cell_eq_univ hh, setIntegral_univ] at h

theorem tsum_integral_cell {h : ℝ} (hh : 0 < h) {f : E3 → ℝ} (hf : Integrable f) :
    (∑' n : Fin 3 → ℤ, ∫ x in cell h n, f x) = ∫ x, f x :=
  (hasSum_integral_cell hh hf).tsum_eq

/-- **The abstract Riemann excess bound.**

If `f` is integrable, its lattice sum is summable, and for every `n` the excess of `f` at the
cell centre over the cell average is dominated by `b n` with `b` summable, then the lattice sum
exceeds `(h³)⁻¹∫f` by at most `∑' b`. -/
theorem tsum_lpt_sub_integral_le {f : E3 → ℝ} {h : ℝ} (hh : 0 < h)
    (hfi : Integrable f) (hfs : Summable fun n : Fin 3 → ℤ => f (lpt h n))
    {b : (Fin 3 → ℤ) → ℝ} (hb_sum : Summable b)
    (hb : ∀ n, f (lpt h n) - (h ^ 3)⁻¹ * (∫ x in cell h n, f x) ≤ b n) :
    (∑' n, f (lpt h n)) ≤ (h ^ 3)⁻¹ * (∫ x, f x) + ∑' n, b n := by
  have hHas : HasSum (fun n : Fin 3 → ℤ => ∫ x in cell h n, f x) (∫ x, f x) :=
    hasSum_integral_cell hh hfi
  have hsum_int : Summable (fun n : Fin 3 → ℤ => ∫ x in cell h n, f x) := hHas.summable
  have hsum_c : Summable (fun n : Fin 3 → ℤ => (h ^ 3)⁻¹ * (∫ x in cell h n, f x)) :=
    hsum_int.mul_left _
  have hsumdiff : Summable (fun n : Fin 3 → ℤ =>
      f (lpt h n) - (h ^ 3)⁻¹ * (∫ x in cell h n, f x)) := hfs.sub hsum_c
  have hkey : (∑' n, (f (lpt h n) - (h ^ 3)⁻¹ * (∫ x in cell h n, f x))) ≤ ∑' n, b n :=
    Summable.tsum_le_tsum hb hsumdiff hb_sum
  have hexp : (∑' n, (f (lpt h n) - (h ^ 3)⁻¹ * (∫ x in cell h n, f x)))
      = (∑' n, f (lpt h n)) - (h ^ 3)⁻¹ * (∫ x, f x) := by
    rw [Summable.tsum_sub hfs hsum_c, tsum_mul_left, hHas.tsum_eq]
  linarith [hkey, hexp]

/-! ## 3. The lattice count -/

/-- The half-open cube `∏_i [-A, A)` of the coordinate space. -/
def boxF (A : ℝ) : Set F3 := Set.pi Set.univ fun _ : Fin 3 => Set.Ico (-A) A

/-- The half-open cube `{x | ∀ i, -A ≤ x i < A}`. -/
def box (A : ℝ) : Set E3 := {x | ∀ i, -A ≤ x i ∧ x i < A}

lemma box_eq_preimage (A : ℝ) :
    box A = ofE ⁻¹' (boxF A) := by
  ext x
  simp only [ofE, box, boxF, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    Set.mem_Ico, WithLp.ofLp_toLp, forall_const, true_implies]

lemma volume_boxF {A : ℝ} (hA : 0 < A) : volume (boxF A) = ENNReal.ofReal ((2 * A) ^ 3) := by
  rw [boxF, Real.volume_pi_Ico]
  have hstep : ∀ i : Fin 3, ENNReal.ofReal (A - -A) = ENNReal.ofReal (2 * A) := by
    intro i
    ring_nf
  rw [Finset.prod_congr rfl fun i _ => hstep i]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2*A) 3]

lemma volume_box {A : ℝ} (hA : 0 < A) : volume (box A) = ENNReal.ofReal ((2 * A) ^ 3) := by
  have hmeas : MeasurableSet (boxF A) := by
    rw [boxF]
    exact MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ico
  have h := volume_preserving_ofE.measure_preimage (s := boxF A) hmeas.nullMeasurableSet
  rw [box_eq_preimage, h]
  exact volume_boxF hA

/-- **The lattice count.**  A set of lattice points of norm `≤ R` has `#S·h³ ≤ (2R+h√3+2)³`. -/
lemma card_mul_le {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) {S : Finset (Fin 3 → ℤ)}
    (hS : ∀ n ∈ S, ‖lpt h n‖ ≤ R) :
    (S.card : ℝ) * h ^ 3 ≤ (2 * (R + h * Real.sqrt 3 / 2 + 1)) ^ 3 := by
  set A : ℝ := R + h * Real.sqrt 3 / 2 + 1 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hvol : volume (⋃ n ∈ S, cell h n) = ENNReal.ofReal ((S.card : ℝ) * h ^ 3) := by
    rw [measure_biUnion_finset]
    · rw [Finset.sum_congr rfl (fun n hn => volume_cell hh n), Finset.sum_const,
        nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    · intro n hn m hm hnm
      exact cell_pairwise_disjoint hh hnm
    · intro n _
      exact measurableSet_cell h n
  have hsub : (⋃ n ∈ S, cell h n) ⊆ box A := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hn, hx⟩ := hx
    have hnorm : ‖x‖ ≤ A - 1 := by
      have h1 : ‖x‖ ≤ ‖lpt h n‖ + ‖x - lpt h n‖ := by
        have h := norm_add_le (x - lpt h n) (lpt h n)
        rw [sub_add_cancel] at h
        linarith
      have h2 : ‖x - lpt h n‖ ≤ h * Real.sqrt 3 / 2 := norm_sub_lpt_le hh hx
      have h3 : ‖lpt h n‖ ≤ R := hS n hn
      linarith [h1, h2, h3, hA]
    intro i
    have hle : |x i| ≤ A - 1 :=
      le_trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i) hnorm
    rw [abs_le] at hle
    exact ⟨by linarith [hle.1], by linarith [hle.2]⟩
  have hmono : volume (⋃ n ∈ S, cell h n) ≤ volume (box A) := measure_mono hsub
  rw [hvol, volume_box hApos] at hmono
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ (2*A)^3)).mp hmono
  rw [hA] at this
  calc (S.card : ℝ) * h ^ 3 ≤ (2 * (R + h * Real.sqrt 3 / 2 + 1)) ^ 3 := this

/-- A nonzero label has a nonzero lattice point. -/
lemma lpt_ne_zero {h : ℝ} (hh : 0 < h) {n : Fin 3 → ℤ} (hn : n ≠ 0) : lpt h n ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  intro hc
  have h2 : (lpt h n).ofLp i = 0 := by rw [hc]; rfl
  rw [lpt_ofLp] at h2
  rcases mul_eq_zero.mp h2 with h1 | h3
  · exact absurd h1 (ne_of_gt hh)
  · exact hi (Int.cast_eq_zero.mp h3)

lemma norm_lpt_pos_of_ne_zero {h : ℝ} (hh : 0 < h) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    0 < ‖lpt h n‖ := norm_pos_iff.mpr (lpt_ne_zero hh hn)

end Work.BoseBogFS
