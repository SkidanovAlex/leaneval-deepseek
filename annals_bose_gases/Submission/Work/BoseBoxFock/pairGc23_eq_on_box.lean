import Mathlib
import Submission.Work.BoseBoxFock.pairGBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23_eq_on_box`

The honest fibre `pairG23 p Θ A B` (of `pairRowGDefs`) integrates the two kernel slots `p.1`, `p.2`
over the *whole* space, while the clean fibre `pairGc23 ℓ p hp Θ₀ A B` of `pairGCore` integrates
them over the one-particle box `boxL ℓ` (and the remaining fibre over the box `boxPiSet`).

When `Θ = 1_{abox n ℓ}·Θ₀`, the two agree on `boxL ℓ × boxL ℓ`: the state factor
`star (Θ (insertCoord2 p w₀ w₁ x'))` already vanishes unless `x'` is in the fibre box, and the
updated configuration `update (update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u` is exactly
`insertCoord2 p y u x'`, which lies in `abox n ℓ` precisely when `y`, `u` are in `boxL ℓ`.  So each
of the three integrals collapses to the corresponding box, and the `A`/`B` factors — which are only
assumed measurable and bounded — acquire no indicator.

This is the `pairG23` companion of the first conjunct of `pairGc23_core`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The complementary fibre index type of the two removed slots `p.1`, `p.2`. -/
abbrev pg23Fib (n : ℕ) (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}

/-! ## 1. Continuity of the coordinate insertion -/

/-- The insertion with the two kernel coordinates fixed is continuous. -/
lemma pg23_continuous_ins_fixed {n : ℕ} (p : Fin n × Fin n) (a b : E3) :
    Continuous (fun x' : pg23Fib n p → E3 => insertCoord2 p a b x') := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have h : (fun x' : pg23Fib n p → E3 => insertCoord2 p a b x' k) = fun _ => a := by
      funext x'
      simp only [insertCoord2_eq, dif_pos h1]
    rw [h]; exact continuous_const
  · by_cases h2 : k = p.2
    · have h : (fun x' : pg23Fib n p → E3 => insertCoord2 p a b x' k) = fun _ => b := by
        funext x'
        simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
      rw [h]; exact continuous_const
    · have h : (fun x' : pg23Fib n p → E3 => insertCoord2 p a b x' k)
          = fun x' => x' ⟨k, h1, h2⟩ := by
        funext x'
        simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
      rw [h]; exact continuous_apply _

/-- The insertion of the two kernel coordinates is continuous in all its arguments. -/
lemma pg23_continuous_ins_joint {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have h : (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
        insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.1 := by
      funext z
      simp only [insertCoord2_eq, dif_pos h1]
    rw [h]; exact continuous_snd.fst
  · by_cases h2 : k = p.2
    · have h : (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
          insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.2 := by
        funext z
        simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
      rw [h]; exact continuous_snd.snd
    · have h : (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
          insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.1 ⟨k, h1, h2⟩ := by
        funext z
        simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
      rw [h]; exact (continuous_apply _).comp continuous_fst

/-! ## 2. Coordinates of inserted and updated configurations -/

lemma pg23_ins_self {n : ℕ} (p : Fin n × Fin n) (a b : E3) (x' : pg23Fib n p → E3) :
    insertCoord2 p a b x' p.1 = a := by
  change (if h : p.1 = p.1 then a else if h' : p.1 = p.2 then b else x' ⟨p.1, h, h'⟩) = a
  exact dif_pos rfl

lemma pg23_ins_other {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a b : E3)
    (x' : pg23Fib n p → E3) : insertCoord2 p a b x' p.2 = b := by
  change (if h : p.2 = p.1 then a else if h' : p.2 = p.2 then b else x' ⟨p.2, h, h'⟩) = b
  exact (dif_neg (show ¬ (p.2 = p.1) from fun h => hp h.symm)).trans (dif_pos rfl)

lemma pg23_ins_ne {n : ℕ} {p : Fin n × Fin n} {k : Fin n} (h1 : k ≠ p.1) (h2 : k ≠ p.2)
    (a b : E3) (x' : pg23Fib n p → E3) : insertCoord2 p a b x' k = x' ⟨k, h1, h2⟩ := by
  change (if h : k = p.1 then a else if h' : k = p.2 then b else x' ⟨k, h, h'⟩) = x' ⟨k, h1, h2⟩
  exact (dif_neg h1).trans (dif_neg h2)

/-- Replacing the two inserted coordinates by `y`, `u` gives the insertion of `(y, u)`. -/
lemma pg23_ins_update {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a b y u : E3)
    (x' : pg23Fib n p → E3) :
    Function.update (Function.update (insertCoord2 p a b x') p.1 y) p.2 u
      = insertCoord2 p y u x' := by
  funext k
  by_cases h1 : k = p.1
  · subst h1
    rw [Function.update_apply, if_neg hp, Function.update_apply, if_pos rfl,
      pg23_ins_self p y u x']
  · by_cases h2 : k = p.2
    · subst h2
      rw [Function.update_apply, if_pos rfl, pg23_ins_other hp]
    · rw [Function.update_apply, if_neg h2, Function.update_apply, if_neg h1,
        pg23_ins_ne h1 h2, pg23_ins_ne h1 h2]

/-- The first coordinate of the doubly updated configuration is `y`. -/
lemma pg23_upd_apply_fst {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (c : Fin n → E3)
    (y u : E3) : Function.update (Function.update c p.1 y) p.2 u p.1 = y := by
  rw [Function.update_apply, if_neg hp, Function.update_apply, if_pos rfl]

/-- The second coordinate of the doubly updated configuration is `u`. -/
lemma pg23_upd_apply_snd {n : ℕ} {p : Fin n × Fin n} (c : Fin n → E3) (y u : E3) :
    Function.update (Function.update c p.1 y) p.2 u p.2 = u := by
  rw [Function.update_apply, if_pos rfl]

/-- If `u` is outside the box, the doubly updated configuration is outside `abox`. -/
lemma pg23_upd_notMem_abox_of_snd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (c : Fin n → E3) (y u : E3) (hu : u ∉ boxL ℓ) :
    Function.update (Function.update c p.1 y) p.2 u ∉ Submission.BoseGases.abox n ℓ := by
  intro h
  refine hu ?_
  rw [corpusBox_boxL_eq_acube hℓ]
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.2
  rwa [pg23_upd_apply_snd c y u] at h1

/-- If `y` is outside the box, the doubly updated configuration is outside `abox`. -/
lemma pg23_upd_notMem_abox_of_fst {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) (c : Fin n → E3) (y u : E3) (hy : y ∉ boxL ℓ) :
    Function.update (Function.update c p.1 y) p.2 u ∉ Submission.BoseGases.abox n ℓ := by
  intro h
  refine hy ?_
  rw [corpusBox_boxL_eq_acube hℓ]
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.1
  rwa [pg23_upd_apply_fst hp c y u] at h1

/-! ## 3. The pointwise integrand identity -/

/-- On the box the `pairG23` integrand equals the box-restricted clean integrand. -/
lemma pg23_integrand_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {Θ₀ Θ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    {w₀ w₁ : E3} (h₀ : w₀ ∈ boxL ℓ) (h₁ : w₁ ∈ boxL ℓ)
    (x' : pg23Fib n p → E3) (y u : E3) :
    star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
        * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)
      = Set.indicator (boxPiSet (pg23Fib n p) ℓ) (fun _ => (1 : ℂ)) x'
        * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                    * Θ₀ (insertCoord2 p y u x')))) := by
  by_cases hx : x' ∈ boxPiSet (pg23Fib n p) ℓ
  · have hxab : insertCoord2 p w₀ w₁ x' ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord2_mem_abox_iff hℓ h₀ h₁ x').mpr hx
    by_cases hy : y ∈ boxL ℓ
    · by_cases hu : u ∈ boxL ℓ
      · have hupd : Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u
            ∈ Submission.BoseGases.abox n ℓ := upd23_mem_abox hℓ h₀ h₁ hy hu hx
        rw [hΘ (insertCoord2 p w₀ w₁ x'),
          hΘ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u),
          Set.indicator_of_mem hxab, Set.indicator_of_mem hupd, pg23_ins_update hp,
          Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hu]
        simp only [one_mul]
      · have hupd : Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u
            ∉ Submission.BoseGases.abox n ℓ := pg23_upd_notMem_abox_of_snd hℓ _ y u hu
        rw [hΘ (insertCoord2 p w₀ w₁ x'),
          hΘ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u),
          Set.indicator_of_mem hxab, Set.indicator_of_notMem hupd, Set.indicator_of_mem hx,
          Set.indicator_of_mem hy, Set.indicator_of_notMem hu]
        simp only [mul_zero, zero_mul]
    · have hupd : Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u
          ∉ Submission.BoseGases.abox n ℓ := pg23_upd_notMem_abox_of_fst hℓ hp _ y u hy
      rw [hΘ (insertCoord2 p w₀ w₁ x'),
        hΘ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u),
        Set.indicator_of_mem hxab, Set.indicator_of_notMem hupd, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hy]
      simp only [mul_zero, zero_mul]
  · have hxab : insertCoord2 p w₀ w₁ x' ∉ Submission.BoseGases.abox n ℓ :=
      fun h => hx ((insertCoord2_mem_abox_iff hℓ h₀ h₁ x').mp h)
    rw [hΘ (insertCoord2 p w₀ w₁ x'), Set.indicator_of_notMem hxab, Set.indicator_of_notMem hx]
    simp only [star_zero, zero_mul]

/-! ## 4. Measurability and integrability on the boxes -/

/-- The `pairGc23` integrand is measurable. -/
lemma pg23_integrand_measurable {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ₀ : Continuous Θ₀) (hA : Measurable A) (hB : Measurable B) (a b : E3) :
    Measurable (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
      star (Θ₀ (insertCoord2 p a b z.1)) * star (A z.2.1) * star (B z.2.2)
        * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)) := by
  have h1 : Measurable (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
      insertCoord2 p a b z.1) :=
    (pg23_continuous_ins_fixed p a b).measurable.comp measurable_fst
  have h2 : Continuous (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1) := pg23_continuous_ins_joint p
  exact (((continuous_star.measurable.comp (hΘ₀.measurable.comp h1)).mul
    (continuous_star.measurable.comp (hA.comp (measurable_fst.comp measurable_snd)))).mul
    (continuous_star.measurable.comp (hB.comp (measurable_snd.comp measurable_snd)))).mul
    (hΘ₀.measurable.comp h2.measurable)

lemma pg23_measurableSet_boxL_prod (ℓ : ℝ) : MeasurableSet (boxL ℓ ×ˢ boxL ℓ) :=
  (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)

lemma pg23_isCompact_boxL_prod (ℓ : ℝ) : IsCompact (boxL ℓ ×ˢ boxL ℓ) :=
  (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)

/-- A measurable function bounded on `boxL ℓ ×ˢ boxL ℓ` is integrable there. -/
theorem pg23_integrableOn_boxL_prod {ℓ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {F : E3 × E3 → E} (hF : Measurable F) (C : ℝ)
    (hC : ∀ z ∈ boxL ℓ ×ˢ boxL ℓ, ‖F z‖ ≤ C) : IntegrableOn F (boxL ℓ ×ˢ boxL ℓ) := by
  haveI : IsFiniteMeasure (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (pg23_isCompact_boxL_prod ℓ).measure_lt_top⟩
  exact Integrable.of_bound hF.aestronglyMeasurable C (by
    filter_upwards [self_mem_ae_restrict (pg23_measurableSet_boxL_prod ℓ)] with z hz
    exact hC z hz)

/-- Pulling a constant out of a double integral over `E3 × E3`. -/
lemma pg23_integral_const_mul_double (c : ℂ) (F : E3 → E3 → ℂ) :
    (∫ y, ∫ u, c * F y u) = c * ∫ y, ∫ u, F y u := by
  calc (∫ y, ∫ u, c * F y u) = ∫ y, c * (∫ u, F y u) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_const_mul c (F y))
    _ = c * (∫ y, ∫ u, F y u) := integral_const_mul c (fun y => ∫ u, F y u)

/-- A bound for `Θ₀` on the whole `n`-particle box. -/
lemma pg23_exists_bound_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, ‖Θ₀ x‖ ≤ C := by
  have hcomp : IsCompact (Submission.BoseGases.abox n ℓ) := by
    have h : Submission.BoseGases.abox n ℓ = boxPiSet (Fin n) ℓ := by
      refine Set.ext fun x => ?_
      rw [mem_boxPiSet, Submission.BoseGases.mem_abox_iff]
      constructor
      · intro hx i; rw [corpusBox_boxL_eq_acube hℓ]; exact hx i
      · intro hx i; rw [← corpusBox_boxL_eq_acube hℓ]; exact hx i
    rw [h]
    exact isCompact_boxPiSet (ι := Fin n) hℓ
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hΘ₀.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-! ## 5. The main identity -/

theorem pairGc23_eq_on_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    ∀ w y : EuclideanSpace ℝ (Fin 3), w ∈ Work.BoseK15.corpusBox.boxL ℓ →
        y ∈ Work.BoseK15.corpusBox.boxL ℓ →
      Work.BoseBoxFock.pairG23 p Θ A B w y
        = Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w y := by
  intro w₀ w₁ hw₀ hw₁
  classical
  have hbcomp : IsCompact (boxL ℓ) := Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  have hbmeas : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hSmeas : MeasurableSet (boxPiSet (pg23Fib n p) ℓ) :=
    (isCompact_boxPiSet (ι := pg23Fib n p) hℓ).measurableSet
  -- the inner reduction of the two `y`/`u` integrals, used in both directions
  have hinner : ∀ x' : pg23Fib n p → E3,
      (∫ (y : E3), ∫ (u : E3),
          Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                    * Θ₀ (insertCoord2 p y u x'))))
        = ∫ y in boxL ℓ, ∫ u in boxL ℓ,
            (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
              * Θ₀ (insertCoord2 p y u x')) := by
    intro x'
    have h1 : (∫ (y : E3), ∫ (u : E3),
          Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                    * Θ₀ (insertCoord2 p y u x'))))
        = ∫ (y : E3), Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
            * (∫ (u : E3), Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                    * Θ₀ (insertCoord2 p y u x'))) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => integral_const_mul _ _)
    rw [h1, integral_indicator_mul (s := boxL ℓ) hbmeas]
    exact setIntegral_congr_fun hbmeas (fun y _ => integral_indicator_mul (s := boxL ℓ) hbmeas _)
  have key1 : pairG23 p Θ A B w₀ w₁
      = ∫ x' in boxPiSet (pg23Fib n p) ℓ, ∫ y in boxL ℓ, ∫ u in boxL ℓ,
          (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
            * Θ₀ (insertCoord2 p y u x')) := by
    calc pairG23 p Θ A B w₀ w₁
        = ∫ (x' : pg23Fib n p → E3), ∫ (y : E3), ∫ (u : E3),
            star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
              * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u) :=
          rfl
      _ = ∫ (x' : pg23Fib n p → E3), ∫ (y : E3), ∫ (u : E3),
            Set.indicator (boxPiSet (pg23Fib n p) ℓ) (fun _ => (1 : ℂ)) x'
              * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
                  * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                      * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                          * Θ₀ (insertCoord2 p y u x')))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
          simp only []
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only []
          exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
            pg23_integrand_eq hℓ hp hΘ hw₀ hw₁ x' y u)
      _ = ∫ (x' : pg23Fib n p → E3),
            Set.indicator (boxPiSet (pg23Fib n p) ℓ) (fun _ => (1 : ℂ)) x'
              * (∫ (y : E3), ∫ (u : E3),
                  Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
                    * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                        * (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                            * Θ₀ (insertCoord2 p y u x')))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
          simp only []
          rw [pg23_integral_const_mul_double]
      _ = ∫ x' in boxPiSet (pg23Fib n p) ℓ, ∫ y in boxL ℓ, ∫ u in boxL ℓ,
            (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
              * Θ₀ (insertCoord2 p y u x')) := by
          rw [integral_indicator_mul (s := boxPiSet (pg23Fib n p) ℓ) hSmeas]
          exact setIntegral_congr_fun hSmeas (fun x' _ => hinner x')
  have key2 : pairGc23 ℓ p hp Θ₀ A B w₀ w₁
      = ∫ x' in boxPiSet (pg23Fib n p) ℓ, ∫ y in boxL ℓ, ∫ u in boxL ℓ,
          (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
            * Θ₀ (insertCoord2 p y u x')) := by
    obtain ⟨CΘ, hCΘ0, hCΘ⟩ := pg23_exists_bound_abox (n := n) hℓ hΘ₀.continuous
    have hfin : (volume : Measure ((pg23Fib n p → E3) × (E3 × E3)))
        (boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)) < ⊤ :=
      ((isCompact_boxPiSet (ι := pg23Fib n p) hℓ).prod (hbcomp.prod hbcomp)).measure_lt_top
    have hTmeas : MeasurableSet (boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)) :=
      hSmeas.prod (hbmeas.prod hbmeas)
    have hGm : Measurable (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
        star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)) :=
      pg23_integrand_measurable p hΘ₀.continuous hA hB w₀ w₁
    have hbound : ∀ z ∈ boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ),
        ‖star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ≤ CΘ ^ 2 * cA * cB := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Set.mem_prod.mp hz
      obtain ⟨hz2a, hz2b⟩ := Set.mem_prod.mp hz2
      have hm1 : insertCoord2 p w₀ w₁ z.1 ∈ Submission.BoseGases.abox n ℓ :=
        (insertCoord2_mem_abox_iff hℓ hw₀ hw₁ z.1).mpr hz1
      have hm2 : insertCoord2 p z.2.1 z.2.2 z.1 ∈ Submission.BoseGases.abox n ℓ :=
        (insertCoord2_mem_abox_iff hℓ hz2a hz2b z.1).mpr hz1
      simp only [norm_mul, norm_star]
      calc ‖Θ₀ (insertCoord2 p w₀ w₁ z.1)‖ * ‖A z.2.1‖ * ‖B z.2.2‖
            * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖
          ≤ (CΘ * cA * cB) * CΘ :=
            mul_le_mul (mul_le_mul (mul_le_mul (hCΘ _ hm1) (hAb _) (norm_nonneg _) hCΘ0)
              (hBb _) (norm_nonneg _) (mul_nonneg hCΘ0 hcA)) (hCΘ _ hm2) (norm_nonneg _)
              (mul_nonneg (mul_nonneg hCΘ0 hcA) hcB)
        _ = CΘ ^ 2 * cA * cB := by ring
    have hInt : IntegrableOn (fun z : (pg23Fib n p → E3) × (E3 × E3) =>
        star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1))
        (boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)) := by
      haveI : IsFiniteMeasure
          (volume.restrict (boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
      exact Integrable.of_bound hGm.aestronglyMeasurable (CΘ ^ 2 * cA * cB) (by
        filter_upwards [self_mem_ae_restrict hTmeas] with z hz
        exact hbound z hz)
    have hInt2 : ∀ x' ∈ boxPiSet (pg23Fib n p) ℓ,
        IntegrableOn (fun w' : E3 × E3 =>
          star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A w'.1) * star (B w'.2)
            * Θ₀ (insertCoord2 p w'.1 w'.2 x')) (boxL ℓ ×ˢ boxL ℓ) := by
      intro x' hx'
      refine pg23_integrableOn_boxL_prod ?_ (CΘ ^ 2 * cA * cB) ?_
      · have h2 : Continuous (fun w' : E3 × E3 => insertCoord2 p w'.1 w'.2 x') :=
          (pg23_continuous_ins_joint p).comp (continuous_const.prodMk continuous_id)
        have hc : Measurable (fun _ : E3 × E3 => star (Θ₀ (insertCoord2 p w₀ w₁ x'))) :=
          continuous_star.measurable.comp (hΘ₀.continuous.measurable.comp measurable_const)
        exact ((hc.mul (continuous_star.measurable.comp (hA.comp measurable_fst))).mul
          (continuous_star.measurable.comp (hB.comp measurable_snd))).mul
          (hΘ₀.continuous.measurable.comp h2.measurable)
      · intro w' hw'
        obtain ⟨hw1, hw2⟩ := Set.mem_prod.mp hw'
        have hm1 : insertCoord2 p w₀ w₁ x' ∈ Submission.BoseGases.abox n ℓ :=
          (insertCoord2_mem_abox_iff hℓ hw₀ hw₁ x').mpr hx'
        have hm2 : insertCoord2 p w'.1 w'.2 x' ∈ Submission.BoseGases.abox n ℓ :=
          (insertCoord2_mem_abox_iff hℓ hw1 hw2 x').mpr hx'
        simp only [norm_mul, norm_star]
        calc ‖Θ₀ (insertCoord2 p w₀ w₁ x')‖ * ‖A w'.1‖ * ‖B w'.2‖
              * ‖Θ₀ (insertCoord2 p w'.1 w'.2 x')‖
            ≤ (CΘ * cA * cB) * CΘ :=
              mul_le_mul (mul_le_mul (mul_le_mul (hCΘ _ hm1) (hAb _) (norm_nonneg _) hCΘ0)
                (hBb _) (norm_nonneg _) (mul_nonneg hCΘ0 hcA)) (hCΘ _ hm2) (norm_nonneg _)
                (mul_nonneg (mul_nonneg hCΘ0 hcA) hcB)
          _ = CΘ ^ 2 * cA * cB := by ring
    calc pairGc23 ℓ p hp Θ₀ A B w₀ w₁
        = ∫ z in boxPiSet (pg23Fib n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ),
            star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
              * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) := rfl
      _ = ∫ x' in boxPiSet (pg23Fib n p) ℓ, ∫ w' in boxL ℓ ×ˢ boxL ℓ,
            star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A w'.1) * star (B w'.2)
              * Θ₀ (insertCoord2 p w'.1 w'.2 x') :=
          setIntegral_prod _ hInt
      _ = ∫ x' in boxPiSet (pg23Fib n p) ℓ, ∫ y in boxL ℓ, ∫ u in boxL ℓ,
            (star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
              * Θ₀ (insertCoord2 p y u x')) := by
          refine setIntegral_congr_fun hSmeas (fun x' hx' => ?_)
          exact setIntegral_prod (fun w' : E3 × E3 =>
            star (Θ₀ (insertCoord2 p w₀ w₁ x')) * star (A w'.1) * star (B w'.2)
              * Θ₀ (insertCoord2 p w'.1 w'.2 x')) (hInt2 x' hx')
  rw [key1, key2]

end Work.BoseBoxFock
