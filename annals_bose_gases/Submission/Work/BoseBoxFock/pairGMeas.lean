import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGMeas` — measurability of parametric box integrals

The slice masses and slice Dirichlet contents of `pairGCore` are integrals of continuous functions
of the parameter and the integration variables over compact boxes; this module records the
`StronglyMeasurable` statements (needed to turn the pointwise estimates into integrability).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## Continuity of the insertion maps -/

theorem continuous_insertCoord {n : ℕ} (j : Fin n) :
    Continuous (fun q : E3 × ({k : Fin n // k ≠ j} → E3) => insertCoord j q.1 q.2) := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = j
  · have hc : Continuous (fun q : E3 × ({k : Fin n // k ≠ j} → E3) => q.1) := continuous_fst
    simpa only [insertCoord_eq, dif_pos hk] using hc
  · have hc : Continuous (fun q : E3 × ({k : Fin n // k ≠ j} → E3) =>
        q.2 (⟨k, hk⟩ : {i : Fin n // i ≠ j})) :=
      (continuous_apply (⟨k, hk⟩ : {i : Fin n // i ≠ j})).comp continuous_snd
    simpa only [insertCoord_eq, dif_neg hk] using hc

theorem continuous_insertCoord2_box {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      insertCoord2 p q.1.1 q.1.2 q.2) := by
  refine continuous_pi fun k => ?_
  by_cases h1 : k = p.1
  · have hc : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        q.1.1) := continuous_fst.comp continuous_fst
    simpa only [insertCoord2_eq, dif_pos h1] using hc
  · by_cases h2 : k = p.2
    · have hc : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          q.1.2) := continuous_snd.comp continuous_fst
      simpa only [insertCoord2_eq, dif_neg h1, dif_pos h2] using hc
    · have hc : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          q.2 (⟨k, h1, h2⟩ : {i : Fin n // i ≠ p.1 ∧ i ≠ p.2})) :=
        (continuous_apply (⟨k, h1, h2⟩ : {i : Fin n // i ≠ p.1 ∧ i ≠ p.2})).comp continuous_snd
      simpa only [insertCoord2_eq, dif_neg h1, dif_neg h2] using hc

theorem continuous_confY13_box {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun q : (E3 × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      confY13 p q.1.1 q.2 q.1.2) := by
  refine continuous_pi fun k => ?_
  by_cases h1 : k = p.1
  · have hc : Continuous (fun q : (E3 × ({k : Fin n // k ≠ p.2} → E3)) × E3 => q.1.1) :=
      continuous_fst.comp continuous_fst
    simpa only [confY13, dif_pos h1] using hc
  · by_cases h2 : k = p.2
    · have hc : Continuous (fun q : (E3 × ({k : Fin n // k ≠ p.2} → E3)) × E3 => q.2) :=
        continuous_snd
      simpa only [confY13, dif_neg h1, dif_pos h2] using hc
    · have hc : Continuous (fun q : (E3 × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
          q.1.2 (⟨k, h2⟩ : {i : Fin n // i ≠ p.2})) :=
        (continuous_apply (⟨k, h2⟩ : {i : Fin n // i ≠ p.2})).comp
          (continuous_snd.comp continuous_fst)
      simpa only [confY13, dif_neg h1, dif_neg h2] using hc

/-! ## Measurability of parametric box integrals -/

/-- Parametric integrals over a box of test functions are strongly measurable. -/
theorem stronglyMeasurable_integral_boxPiSet {α : Type*} [MeasurableSpace α] {ι : Type*}
    [Fintype ι] {ℓ : ℝ} {g : α → (ι → E3) → ℝ}
    (hg : StronglyMeasurable (fun q : α × (ι → E3) => g q.1 q.2)) :
    StronglyMeasurable (fun y : α => ∫ x in boxPiSet ι ℓ, g y x) := by
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (boxPiSet ι ℓ)) (f := fun (y : α) (x : ι → E3) => g y x) hg
  simpa only using h

/-- Parametric integrals over the one-particle box are strongly measurable. -/
theorem stronglyMeasurable_integral_boxL {α : Type*} [MeasurableSpace α] {ℓ : ℝ}
    {g : α → E3 → ℝ} (hg : StronglyMeasurable (fun q : α × E3 => g q.1 q.2)) :
    StronglyMeasurable (fun y : α => ∫ x in boxL ℓ, g y x) := by
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (boxL ℓ)) (f := fun (y : α) (x : E3) => g y x) hg
  simpa only using h

/-- Iterated parametric integrals over a box of test functions and the one-particle box. -/
theorem stronglyMeasurable_integral_boxPiSet_boxL {α : Type*} [MeasurableSpace α] {ι : Type*}
    [Fintype ι] {ℓ : ℝ} {g : α → (ι → E3) → E3 → ℝ}
    (hg : StronglyMeasurable (fun q : (α × (ι → E3)) × E3 => g q.1.1 q.1.2 q.2)) :
    StronglyMeasurable (fun y : α => ∫ x in boxPiSet ι ℓ, ∫ u in boxL ℓ, g y x u) := by
  have h1 : StronglyMeasurable (fun z : α × (ι → E3) => ∫ u in boxL ℓ, g z.1 z.2 u) :=
    stronglyMeasurable_integral_boxL (g := fun (z : α × (ι → E3)) (u : E3) => g z.1 z.2 u) hg
  have h2 : StronglyMeasurable (fun y : α => ∫ x in boxPiSet ι ℓ,
      (fun z : α × (ι → E3) => ∫ u in boxL ℓ, g z.1 z.2 u) (y, x)) :=
    stronglyMeasurable_integral_boxPiSet h1
  simpa only using h2

/-! ## The instances -/

theorem stronglyMeasurable_memX13 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) : StronglyMeasurable (memX13 ℓ p Θ₀) := by
  have h := stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
    (g := fun (w : E3) (x : {k : Fin n // k ≠ p.2} → E3) => ‖Θ₀ (insertCoord p.2 w x)‖ ^ 2)
    ((hΘ₀.comp (continuous_insertCoord p.2)).norm.pow 2).stronglyMeasurable
  change StronglyMeasurable (fun w : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
    ‖Θ₀ (insertCoord p.2 w x')‖ ^ 2)
  exact h

theorem stronglyMeasurable_dirX13 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) : StronglyMeasurable (dirX13 ℓ p Θ₀) := by
  have hd : Continuous (fun q : E3 × ({k : Fin n // k ≠ p.2} → E3) =>
      fderiv ℝ Θ₀ (insertCoord p.2 q.1 q.2)) :=
    (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord p.2)
  change StronglyMeasurable (fun w : E3 => ∑ j : Fin 3,
    ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
      ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2)
  have h := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin 3)) fun j _ =>
    stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
      (g := fun (w : E3) (x : {k : Fin n // k ≠ p.2} → E3) =>
        ‖fderiv ℝ Θ₀ (insertCoord p.2 w x) (slotDirVec p.2 j)‖ ^ 2)
      (((hd.clm_apply continuous_const).norm.pow 2).stronglyMeasurable)
  convert h using 1
  funext w
  rw [Finset.sum_apply]

theorem stronglyMeasurable_memY13 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) : StronglyMeasurable (memY13 ℓ p Θ₀) := by
  have h := stronglyMeasurable_integral_boxPiSet_boxL (ℓ := ℓ)
    (g := fun (y : E3) (x : {k : Fin n // k ≠ p.2} → E3) (u : E3) =>
      ‖Θ₀ (confY13 p y u x)‖ ^ 2)
    ((hΘ₀.comp (continuous_confY13_box p)).norm.pow 2).stronglyMeasurable
  change StronglyMeasurable (fun y : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
    ∫ u in boxL ℓ, ‖Θ₀ (confY13 p y u x')‖ ^ 2)
  exact h

theorem stronglyMeasurable_memX23 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) : StronglyMeasurable (Function.uncurry (memX23 ℓ p Θ₀)) := by
  have h := stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
    (g := fun (w : E3 × E3) (x : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      ‖Θ₀ (insertCoord2 p w.1 w.2 x)‖ ^ 2)
    ((hΘ₀.comp (continuous_insertCoord2_box p)).norm.pow 2).stronglyMeasurable
  change StronglyMeasurable (fun w : E3 × E3 => ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖Θ₀ (insertCoord2 p w.1 w.2 x'')‖ ^ 2)
  simpa only [Function.uncurry] using h

theorem stronglyMeasurable_dirX23 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) : StronglyMeasurable (Function.uncurry (dirX23 ℓ p Θ₀)) := by
  have hd : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      fderiv ℝ Θ₀ (insertCoord2 p q.1.1 q.1.2 q.2)) :=
    (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord2_box p)
  change StronglyMeasurable (fun w : E3 × E3 => ∑ j : Fin 3,
    ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ‖fderiv ℝ Θ₀ (insertCoord2 p w.1 w.2 x'') (slotDirVec p.1 j)‖ ^ 2)
  have h := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin 3)) fun j _ =>
    stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
      (g := fun (w : E3 × E3) (x : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ‖fderiv ℝ Θ₀ (insertCoord2 p w.1 w.2 x) (slotDirVec p.1 j)‖ ^ 2)
      (((hd.clm_apply continuous_const).norm.pow 2).stronglyMeasurable)
  convert h using 1
  funext w
  rw [Finset.sum_apply]

theorem stronglyMeasurable_memY21 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) : StronglyMeasurable (Function.uncurry (memY21 ℓ p Θ₀)) := by
  have h := stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
    (g := fun (w : E3 × E3) (x : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      ‖Θ₀ (insertCoord2 p w.1 w.2 x)‖ ^ 2)
    ((hΘ₀.comp (continuous_insertCoord2_box p)).norm.pow 2).stronglyMeasurable
  change StronglyMeasurable (fun w : E3 × E3 => ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖Θ₀ (insertCoord2 p w.1 w.2 x'')‖ ^ 2)
  simpa only [Function.uncurry] using h

theorem stronglyMeasurable_dirY21 {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) : StronglyMeasurable (Function.uncurry (dirY21 ℓ p Θ₀)) := by
  have hd : Continuous (fun q : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      fderiv ℝ Θ₀ (insertCoord2 p q.1.1 q.1.2 q.2)) :=
    (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord2_box p)
  change StronglyMeasurable (fun w : E3 × E3 => ∑ j : Fin 3,
    ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ‖fderiv ℝ Θ₀ (insertCoord2 p w.1 w.2 x'') (slotDirVec p.2 j)‖ ^ 2)
  have h := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin 3)) fun j _ =>
    stronglyMeasurable_integral_boxPiSet (ℓ := ℓ)
      (g := fun (w : E3 × E3) (x : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ‖fderiv ℝ Θ₀ (insertCoord2 p w.1 w.2 x) (slotDirVec p.2 j)‖ ^ 2)
      (((hd.clm_apply continuous_const).norm.pow 2).stronglyMeasurable)
  convert h using 1
  funext w
  rw [Finset.sum_apply]

end Work.BoseBoxFock
