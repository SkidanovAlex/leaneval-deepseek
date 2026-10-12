import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairG_supports
import Submission.Work.BoseBoxFock.pairRowS2Inst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary integrability and integration bounds -/

/-- **A measurable, everywhere bounded function supported in a set of finite measure is
integrable.**  The general-measure-space form of `Work.BoseBoxFock.integrable_of_bounded_support`
(the proof is the same: restrict to `s` and use `IntegrableOn.of_bound`). -/
theorem integrable_of_bounded_support' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- **The boxed double-integral bound.**  If `F` vanishes in each variable outside a set `s` of
finite measure and is pointwise bounded by `C`, then its iterated integral has norm at most
`C · (volume s).toReal²`. -/
theorem norm_doubleIntegral_le {F : E3 → E3 → ℂ} {s : Set E3} (hs : volume s < ⊤) {C : ℝ}
    (hb : ∀ y u, ‖F y u‖ ≤ C) (h1 : ∀ y, y ∉ s → ∀ u, F y u = 0)
    (h2 : ∀ y u, u ∉ s → F y u = 0) :
    ‖∫ y : E3, ∫ u : E3, F y u‖ ≤ C * (volume s).toReal * (volume s).toReal := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hs)
  have hvol : (volume.restrict s).real Set.univ = (volume s).toReal := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ]
  have hinner : ∀ y : E3, ‖∫ u : E3, F y u‖ ≤ C * (volume s).toReal := by
    intro y
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm (fun u => F y u)) ?_
    have hzero : ∀ u ∉ s, ‖F y u‖ = 0 := fun u hu => by simp [h2 y u hu]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun u => ‖F y u‖) hzero]
    have hmono : (∫ u in s, ‖F y u‖) ≤ ∫ u in s, C :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
        (integrable_const C) (Filter.Eventually.of_forall fun u => hb y u)
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const, hvol, smul_eq_mul]
    exact le_of_eq (by ring)
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm (fun y => ∫ u : E3, F y u)) ?_
  have hzero : ∀ y ∉ s, ‖∫ u : E3, F y u‖ = 0 := fun y hy => by
    have : (∫ u : E3, F y u) = 0 := by
      simp only [h1 y hy]
      simp
    rw [this, norm_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun y => ‖∫ u : E3, F y u‖) hzero]
  have hmono : (∫ y in s, ‖∫ u : E3, F y u‖) ≤ ∫ y in s, C * (volume s).toReal :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
      (integrable_const (C * (volume s).toReal)) (Filter.Eventually.of_forall fun y => hinner y)
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const, hvol, smul_eq_mul]
  exact le_of_eq (by ring)

/-- The product box of the fibre coordinates of block II.2 has finite measure. -/
theorem volume_fib23_lt_top {n : ℕ} (p : Fin n × Fin n) (ℓ : ℝ) :
    volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
      Work.BoseK15.corpusBox.boxL ℓ)) < (⊤ : ENNReal) :=
  IsCompact.measure_lt_top (isCompact_univ_pi (fun _ => Work.BoseK15.corpusBox.boxL_compact ℓ))

/-- The box squared has finite measure. -/
theorem volume_prod_boxL_lt_top (ℓ : ℝ) :
    volume (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) < (⊤ : ENNReal) :=
  IsCompact.measure_lt_top ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod
    (Work.BoseK15.corpusBox.boxL_compact ℓ))

/-! ## 2. The inner double integral of the block II.2 shape -/

/-- **The inner double integral of the block II.2 shape** at the configuration `x`: the free
variables `y`, `u` carry the state factors `A`, `B` and are substituted into the slots `p.1`,
`p.2`.  This is the second factor of the block II.2 integrand `K (x p.1) (x p.2) · phi23 x`. -/
noncomputable def phi23 {n : ℕ} (p : Fin n × Fin n) (Θ : Work.BoseDict.Xn n → ℂ) (A B : E3 → ℂ)
    (x : Fin n → E3) : ℂ :=
  ∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
    * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- `phi23` is measurable as soon as `Θ`, `A`, `B` are (the three iterated integrals are
parametric integrals of a jointly measurable integrand). -/
theorem phi23_measurable {n : ℕ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B) :
    Measurable (phi23 p Θ A B) := by
  have hupd : Measurable (fun q : ((Fin n → E3) × E3) × E3 =>
      Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2) := by
    have h1 : Measurable (fun q : ((Fin n → E3) × E3) × E3 => (q.1.1, q.1.2)) :=
      ((by fun_prop : Measurable (fun q : ((Fin n → E3) × E3) × E3 => q.1.1))).prod (by fun_prop)
    have h2 : Measurable (fun q : ((Fin n → E3) × E3) × E3 =>
        Function.update q.1.1 p.1 q.1.2) :=
      (measurable_update' (X := fun _ : Fin n => E3) (a := p.1)).comp h1
    have h3 : Measurable (fun q : ((Fin n → E3) × E3) × E3 =>
        (Function.update q.1.1 p.1 q.1.2, q.2)) := h2.prod (by fun_prop)
    exact (measurable_update' (X := fun _ : Fin n => E3) (a := p.2)).comp h3
  have hHss : StronglyMeasurable (fun q : ((Fin n → E3) × E3) × E3 =>
      star (Θ q.1.1) * star (A q.1.2) * star (B q.2)
        * Θ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) :=
    (((continuous_star.measurable.comp (hΘm.comp (by fun_prop : Measurable
        fun q : ((Fin n → E3) × E3) × E3 => q.1.1))).mul
      (continuous_star.measurable.comp (hAm.comp (by fun_prop : Measurable
        fun q : ((Fin n → E3) × E3) × E3 => q.1.2)))).mul
      (continuous_star.measurable.comp (hBm.comp (by fun_prop : Measurable
        fun q : ((Fin n → E3) × E3) × E3 => q.2)))).mul
      (hΘm.comp hupd) |>.stronglyMeasurable
  have step1 : StronglyMeasurable (fun a : (Fin n → E3) × E3 =>
      ∫ u : E3, star (Θ a.1) * star (A a.2) * star (B u)
        * Θ (Function.update (Function.update a.1 p.1 a.2) p.2 u)) :=
    StronglyMeasurable.integral_prod_right' (α := (Fin n → E3) × E3) (β := E3)
      (ν := (volume : Measure E3))
      (f := fun q : ((Fin n → E3) × E3) × E3 => star (Θ q.1.1) * star (A q.1.2) * star (B q.2)
        * Θ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) hHss
  have step2 : StronglyMeasurable (phi23 p Θ A B) :=
    StronglyMeasurable.integral_prod_right' (α := Fin n → E3) (β := E3)
      (ν := (volume : Measure E3))
      (f := fun a : (Fin n → E3) × E3 => ∫ u : E3, star (Θ a.1) * star (A a.2) * star (B u)
        * Θ (Function.update (Function.update a.1 p.1 a.2) p.2 u)) step1
  exact step2.measurable

/-- **The fibre function `pairG23` of block II.2 is measurable.**  (`pairG23` is the two-coordinate
fibre of `blockTwo3_fibre_gen`: the integral over the remaining coordinates of the state with the
two kernel slots frozen.)  Measurability of each of the three iterated integrals is
`StronglyMeasurable.integral_prod_right'`; the only pointwise input is the measurability of the
insertion map `(w₀, w₁, x') ↦ insertCoord2 p w₀ w₁ x'`, which is `measurable_pi_lambda` plus a
case distinction on the coordinate. -/
theorem pairG23_measurable {n : ℕ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B) :
    Measurable (Function.uncurry (pairG23 p Θ A B)) := by
  have hinsD : Measurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
      insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2) := by
    unfold insertCoord2
    apply measurable_pi_lambda
    intro k
    by_cases h : k = p.1
    · simp only [dif_pos h]; fun_prop
    · by_cases h' : k = p.2
      · simp only [dif_neg h, dif_pos h']; fun_prop
      · simp only [dif_neg h, dif_neg h']; exact (measurable_pi_apply _).comp (by fun_prop)
  have hupd : Measurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
      Function.update (Function.update (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2)
        p.1 q.1.2) p.2 q.2) := by
    have h1 : Measurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
        ((insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2), q.1.2)) :=
      hinsD.prod (by fun_prop)
    have h2 : Measurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
        Function.update (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2) p.1 q.1.2) :=
      (measurable_update' (X := fun _ : Fin n => E3) (a := p.1)).comp h1
    have h3 : Measurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
        (Function.update (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2) p.1 q.1.2, q.2)) :=
      h2.prod (by fun_prop)
    exact (measurable_update' (X := fun _ : Fin n => E3) (a := p.2)).comp h3
  have hHss : StronglyMeasurable (fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
      star (Θ (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2)) * star (A q.1.2)
        * star (B q.2) * Θ (Function.update (Function.update
            (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2) p.1 q.1.2) p.2 q.2)) :=
    (((continuous_star.measurable.comp (hΘm.comp hinsD)).mul
      (continuous_star.measurable.comp (hAm.comp (by fun_prop : Measurable
        fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 => q.1.2)))).mul
      (continuous_star.measurable.comp (hBm.comp (by fun_prop : Measurable
        fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 => q.2)))).mul
      (hΘm.comp hupd) |>.stronglyMeasurable
  have step1 : StronglyMeasurable (fun a : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
      ∫ u : E3, star (Θ (insertCoord2 p a.1.1.1 a.1.1.2 a.1.2)) * star (A a.2)
        * star (B u) * Θ (Function.update (Function.update
            (insertCoord2 p a.1.1.1 a.1.1.2 a.1.2) p.1 a.2) p.2 u)) :=
    StronglyMeasurable.integral_prod_right'
      (α := ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3)
      (β := E3) (ν := (volume : Measure E3))
      (f := fun q : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
        star (Θ (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2)) * star (A q.1.2)
          * star (B q.2) * Θ (Function.update (Function.update
              (insertCoord2 p q.1.1.1.1 q.1.1.1.2 q.1.1.2) p.1 q.1.2) p.2 q.2)) hHss
  have step2 : StronglyMeasurable (fun b : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      ∫ y : E3, ∫ u : E3, star (Θ (insertCoord2 p b.1.1 b.1.2 b.2)) * star (A y)
        * star (B u) * Θ (Function.update (Function.update
            (insertCoord2 p b.1.1 b.1.2 b.2) p.1 y) p.2 u)) :=
    StronglyMeasurable.integral_prod_right' (α := (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))
      (β := E3) (ν := (volume : Measure E3))
      (f := fun a : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
        ∫ u : E3, star (Θ (insertCoord2 p a.1.1.1 a.1.1.2 a.1.2)) * star (A a.2)
          * star (B u) * Θ (Function.update (Function.update
              (insertCoord2 p a.1.1.1 a.1.1.2 a.1.2) p.1 a.2) p.2 u)) step1
  have step3 : StronglyMeasurable (Function.uncurry (pairG23 p Θ A B)) :=
    StronglyMeasurable.integral_prod_right' (α := E3 × E3) (β := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)
      (ν := (volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)))
      (f := fun b : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ∫ y : E3, ∫ u : E3, star (Θ (insertCoord2 p b.1.1 b.1.2 b.2)) * star (A y)
          * star (B u) * Θ (Function.update (Function.update
              (insertCoord2 p b.1.1 b.1.2 b.2) p.1 y) p.2 u)) step2
  exact step3.measurable

end Work.BoseBoxFock
