import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGBounds` — finiteness of the slice vocabulary

The slice masses and slice Dirichlet contents `memX13, dirX13, memY13, memX23, dirX23, memX21,
memY21, dirY21` (and `pinL2`) are integrals of continuous functions over *compact* boxes, so they
are bounded on the box.  These boundedness statements are what makes the majorants of the D2
estimate integrable.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- A continuous function is bounded on the `n`-particle box. -/
theorem exists_bound_on_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Xn n → ℂ}
    (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, ‖f x‖ ≤ M := by
  have hc : IsCompact (Submission.BoseGases.abox n ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx => le_trans (hM x hx) (le_max_left _ _)⟩

/-- An integral over a compact box of a nonnegative function bounded by `C` is at most
`C * vol(box)`. -/
theorem setIntegral_boxPiSet_le_const {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {φ : (ι → E3) → ℝ} {C : ℝ} (hφ0 : ∀ z ∈ boxPiSet ι ℓ, 0 ≤ φ z)
    (hφC : ∀ z ∈ boxPiSet ι ℓ, φ z ≤ C) :
    (∫ z in boxPiSet ι ℓ, φ z) ≤ C * (volume (boxPiSet ι ℓ)).toReal := by
  have hcomp : IsCompact (boxPiSet ι ℓ) := isCompact_boxPiSet hℓ
  have hfin : (volume (boxPiSet ι ℓ)) < ⊤ := lt_top_iff_ne_top.mpr hcomp.measure_ne_top
  have h1 : |∫ z in boxPiSet ι ℓ, φ z| ≤ C * (volume (boxPiSet ι ℓ)).toReal := by
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (f := φ) hfin fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 z hz)]
    exact hφC z hz
  exact (abs_le.mp h1).2

/-- The same for the one-particle box. -/
theorem setIntegral_boxL_le_const {ℓ : ℝ} (hℓ : 0 < ℓ) {φ : E3 → ℝ} {C : ℝ}
    (hφ0 : ∀ z ∈ boxL ℓ, 0 ≤ φ z) (hφC : ∀ z ∈ boxL ℓ, φ z ≤ C) :
    (∫ z in boxL ℓ, φ z) ≤ C * (volume (boxL ℓ)).toReal := by
  have hcomp : IsCompact (boxL ℓ) := Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  have hfin : (volume (boxL ℓ)) < ⊤ := lt_top_iff_ne_top.mpr hcomp.measure_ne_top
  have h1 : |∫ z in boxL ℓ, φ z| ≤ C * (volume (boxL ℓ)).toReal := by
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (f := φ) hfin fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 z hz)]
    exact hφC z hz
  exact (abs_le.mp h1).2

/-- The `Y`-configuration of `pairG13` lies in the box when `y`, `u` and `x'` do. -/
theorem confY13_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} {y u : E3}
    (hy : y ∈ boxL ℓ) (hu : u ∈ boxL ℓ)
    {x' : {k : Fin n // k ≠ p.2} → E3} (hx : x' ∈ boxPiSet _ ℓ) :
    confY13 p y u x' ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
  intro i
  by_cases h1 : i = p.1
  · simp only [confY13, dif_pos h1]; exact hy
  · simp only [confY13, dif_neg h1]
    by_cases h2 : i = p.2
    · simp only [dif_pos h2]; exact hu
    · simp only [dif_neg h2]
      exact (mem_boxPiSet.mp hx) ⟨i, h2⟩

/-- A bound for `‖∂_dir Θ₀‖` on the box. -/
theorem direction_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (dir : Xn n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ‖fderiv ℝ Θ₀ x dir‖ ≤ M :=
  exists_bound_on_abox hℓ ((hΘ₀.continuous_fderiv (by simp)).clm_apply continuous_const)

/-! ## Bounds for the slice vocabulary -/

theorem memX13_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ boxL ℓ, memX13 ℓ p Θ₀ w ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ)).toReal, by positivity,
    fun w hw => ?_⟩
  refine setIntegral_boxPiSet_le_const hℓ (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord_mem_abox_iff hℓ hw z).mpr hz)) 2)

theorem dirX13_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ boxL ℓ, dirX13 ℓ p Θ₀ w ≤ C := by
  choose M hM0 hM using fun j : Fin 3 =>
    direction_bound (n := n) (ℓ := ℓ) hℓ hΘ₀ (slotDirVec p.2 j)
  refine ⟨∑ j : Fin 3, M j ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ)).toReal,
    by positivity, fun w hw => ?_⟩
  rw [dirX13]
  exact Finset.sum_le_sum fun j _ => setIntegral_boxPiSet_le_const hℓ
    (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM j _ ((insertCoord_mem_abox_iff hℓ hw z).mpr hz)) 2)

theorem memY13_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ boxL ℓ, memY13 ℓ p Θ₀ y ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨(M ^ 2 * (volume (boxL ℓ)).toReal)
      * (volume (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ)).toReal, by positivity, fun y hy => ?_⟩
  have hinner : ∀ x' ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
      (∫ u in boxL ℓ, ‖Θ₀ (confY13 p y u x')‖ ^ 2) ≤ M ^ 2 * (volume (boxL ℓ)).toReal :=
    fun x' hx' => setIntegral_boxL_le_const hℓ (fun u _ => by positivity)
      (fun u hu => pow_le_pow_left₀ (norm_nonneg _)
        (hM _ (confY13_mem_abox hℓ hy hu hx')) 2)
  exact setIntegral_boxPiSet_le_const hℓ
    (fun x' _ => integral_nonneg fun u => by positivity) hinner

theorem memX23_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ boxL ℓ, ∀ y ∈ boxL ℓ, memX23 ℓ p Θ₀ w y ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal,
    by positivity, fun w hw y hy => ?_⟩
  refine setIntegral_boxPiSet_le_const hℓ (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord2_mem_abox_iff hℓ hw hy z).mpr hz)) 2)

theorem dirX23_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ boxL ℓ, ∀ y ∈ boxL ℓ, dirX23 ℓ p Θ₀ w y ≤ C := by
  choose M hM0 hM using fun j : Fin 3 =>
    direction_bound (n := n) (ℓ := ℓ) hℓ hΘ₀ (slotDirVec p.1 j)
  refine ⟨∑ j : Fin 3, M j ^ 2
      * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal,
    by positivity, fun w hw y hy => ?_⟩
  rw [dirX23]
  exact Finset.sum_le_sum fun j _ => setIntegral_boxPiSet_le_const hℓ
    (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM j _ ((insertCoord2_mem_abox_iff hℓ hw hy z).mpr hz)) 2)

theorem memX21_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ boxL ℓ, ∀ b ∈ boxL ℓ, memX21 ℓ p Θ₀ a b ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal,
    by positivity, fun a ha b hb => ?_⟩
  refine setIntegral_boxPiSet_le_const hℓ (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord2_mem_abox_iff hℓ ha hb z).mpr hz)) 2)

theorem memY21_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ boxL ℓ, ∀ u ∈ boxL ℓ, memY21 ℓ p Θ₀ y u ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨M ^ 2 * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal,
    by positivity, fun y hy u hu => ?_⟩
  refine setIntegral_boxPiSet_le_const hℓ (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord2_mem_abox_iff hℓ hy hu z).mpr hz)) 2)

theorem dirY21_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ boxL ℓ, ∀ u ∈ boxL ℓ, dirY21 ℓ p Θ₀ y u ≤ C := by
  choose M hM0 hM using fun j : Fin 3 =>
    direction_bound (n := n) (ℓ := ℓ) hℓ hΘ₀ (slotDirVec p.2 j)
  refine ⟨∑ j : Fin 3, M j ^ 2
      * (volume (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)).toReal,
    by positivity, fun y hy u hu => ?_⟩
  rw [dirY21]
  exact Finset.sum_le_sum fun j _ => setIntegral_boxPiSet_le_const hℓ
    (fun z _ => by positivity)
    (fun z hz => pow_le_pow_left₀ (norm_nonneg _)
      (hM j _ ((insertCoord2_mem_abox_iff hℓ hy hu z).mpr hz)) 2)

theorem pinL2_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ} (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ pinL2 ℓ Θ₀ ≤ C := by
  have hc : IsCompact (Submission.BoseGases.abox n ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀
  refine ⟨M ^ 2 * (volume (Submission.BoseGases.abox n ℓ)).toReal, by positivity, ?_⟩
  have hfin : (volume (Submission.BoseGases.abox n ℓ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hc.measure_ne_top
  have h1 : |∫ z in Submission.BoseGases.abox n ℓ, ‖Θ₀ z‖ ^ 2|
      ≤ M ^ 2 * (volume (Submission.BoseGases.abox n ℓ)).toReal := by
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (f := fun z => ‖Θ₀ z‖ ^ 2) hfin
      fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM z hz) 2
  exact (abs_le.mp h1).2

end Work.BoseBoxFock
