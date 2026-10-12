import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.acubePVFacts
import Submission.Work.BoseBoxFock.slotProj1_finsetSum_ae
import Submission.Work.MB.SlotWeakDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.SlotWeakBase` — the measurable/bounded slot calculus: base facts

The measurable/bounded ("weak") line of the box ↔ model bridge replaces the *continuous*,
*compactly supported* mode hypotheses of the strong chain by measurability, everywhere
boundedness and support in the corpus box `Work.BoseK15.corpusBox.boxL ℓ` (and the state
hypotheses by measurability, everywhere boundedness and support in the `n`-particle box
`boxPow n ℓ`).

This module collects the *base* facts needed by every later step:

* `PV e` (`Work.BoseBoxFock.PV`) is measurable and bounded, and vanishes as soon as one of its
  two arguments leaves the box (`Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL{, _fst}`);
* `etaOf e w = Σ_l w_l · e_l` is measurable, bounded and supported in the box;
* the slot projections `slotProj e T`, `slotProj1 e i`, the sectors `slotExact e S` and the
  first-quantised slot sum `boxSlotSum e T Ψ` are measurable, bounded, and preserve support in
  `boxPow n ℓ`.

Everything is stated for `Measurable` (not only a.e. strongly measurable) data and *everywhere*
bounds, so that the identities proved downstream are identities of functions and not only a.e.
identities.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The `L¹` toolkit -/

/-- A measurable function which is everywhere bounded by `C` and vanishes outside a set `S` of
finite measure is integrable. -/
theorem integrable_of_bdd_of_support {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤) {f : α → ℂ} (hfm : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hsupp : ∀ x, x ∉ S → f x = 0) : Integrable f μ := by
  refine Integrable.mono' (g := fun x => max C 0 * S.indicator (fun _ => (1 : ℝ)) x) ?_ hfm ?_
  · exact ((integrable_indicator_iff hS).mpr (integrableOn_const hSfin)).const_mul _
  · filter_upwards with x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, mul_one]
      exact (hC x).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact le_of_eq (by rw [norm_eq_zero]; exact hsupp x hx)

/-- The product of the corpus boxes has finite volume. -/
theorem volume_boxPow_lt_top (n : ℕ) (ℓ : ℝ) : (volume : Measure (Fin n → E3)) (boxPow n ℓ) ≠ ⊤ := by
  have h : (volume : Measure (Fin n → E3)) (boxPow n ℓ)
      = ∏ i : Fin n, (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [boxPow]
    change MeasureTheory.Measure.pi (fun _ : Fin n => (volume : Measure E3))
      (Set.univ.pi (fun _ : Fin n => Work.BoseK15.corpusBox.boxL ℓ)) = _
    rw [MeasureTheory.Measure.pi_pi]
  rw [h]
  exact ENNReal.prod_ne_top fun i _ =>
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

/-- The product of the corpus boxes is measurable. -/
theorem measurableSet_boxPow (n : ℕ) (ℓ : ℝ) : MeasurableSet (boxPow n ℓ) := by
  rw [boxPow]
  exact MeasurableSet.univ_pi fun _ => Work.BoseB4.BoxData.boxL_measurableSet _ ℓ

/-- Membership in `boxPow`. -/
@[simp] theorem mem_boxPow_iff {n : ℕ} {ℓ : ℝ} {x : Fin n → E3} :
    x ∈ boxPow n ℓ ↔ ∀ i : Fin n, x i ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  simp [boxPow]

/-! ## 1. The projection kernel `PV` -/

theorem PV_weak_measurable {m : ℕ} {e : Fin m → E3 → ℂ} (hmeas : ∀ l, Measurable (e l)) :
    Measurable (fun p : E3 × E3 => Work.BoseBoxFock.PV e p.1 p.2) := by
  have hfun : (fun p : E3 × E3 => Work.BoseBoxFock.PV e p.1 p.2)
      = fun p : E3 × E3 => ∑ l : Fin m, e l p.1 * star (e l p.2) := rfl
  rw [hfun]
  exact Finset.measurable_sum Finset.univ fun l _ =>
    ((hmeas l).comp measurable_fst).mul
      (Complex.continuous_conj.measurable.comp ((hmeas l).comp measurable_snd))

theorem PV_weak_bound {m : ℕ} {e : Fin m → E3 → ℂ} (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : E3, ‖Work.BoseBoxFock.PV e a b‖ ≤ K := by
  choose C hC using hbdd
  refine ⟨(∑ l : Fin m, max (C l) 0) * (∑ l : Fin m, max (C l) 0),
    mul_nonneg (Finset.sum_nonneg fun l _ => le_max_right _ _)
      (Finset.sum_nonneg fun l _ => le_max_right _ _), fun a b => ?_⟩
  calc ‖Work.BoseBoxFock.PV e a b‖ = ‖∑ l : Fin m, e l a * star (e l b)‖ := rfl
    _ ≤ ∑ l : Fin m, ‖e l a * star (e l b)‖ := norm_sum_le _ _
    _ = ∑ l : Fin m, ‖e l a‖ * ‖e l b‖ := by simp
    _ ≤ ∑ l : Fin m, max (C l) 0 * max (C l) 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul ((hC l a).trans (le_max_left _ _)) ((hC l b).trans (le_max_left _ _))
          (norm_nonneg _) (le_max_right _ _)
    _ ≤ (∑ l : Fin m, max (C l) 0) * (∑ l : Fin m, max (C l) 0) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_le_sum fun l _ => Finset.single_le_sum
          (f := fun j : Fin m => max (C l) 0 * max (C j) 0)
          (fun j _ => mul_nonneg (le_max_right _ _) (le_max_right _ _)) (Finset.mem_univ l)

/-- The boundedness of `PV` in the indicator form used for the `L¹` bounds: given a bound `K` of
`‖PV e a b‖` and the box support of the modes, one has
`‖PV e a b‖ ≤ K · 1_{boxL ℓ}(b)` (the kernel vanishes in its second variable outside the box). -/
theorem PV_weak_le_indicator {m : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) {K : ℝ}
    (hK : ∀ a b : E3, ‖Work.BoseBoxFock.PV e a b‖ ≤ K) (a b : E3) :
    ‖Work.BoseBoxFock.PV e a b‖ ≤
      K * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) b := by
  by_cases hb : b ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hb, mul_one]
    exact hK a b
  · rw [Set.indicator_of_notMem hb, mul_zero]
    exact le_of_eq (by rw [Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hb, norm_zero])

/-! ## 2. The superposition `etaOf` -/

theorem etaOf_weak_measurable {m : ℕ} {e : Fin m → E3 → ℂ} (hmeas : ∀ l, Measurable (e l))
    (w : Fin m → ℝ) : Measurable (Work.BoseDict.etaOf e w) := by
  have hfun : Work.BoseDict.etaOf e w = fun z : E3 => ∑ l : Fin m, (w l : ℂ) * e l z := rfl
  rw [hfun]
  exact Finset.measurable_sum Finset.univ fun l _ => measurable_const.mul (hmeas l)

theorem etaOf_weak_support {m : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (w : Fin m → ℝ) :
    Function.support (Work.BoseDict.etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro z hz
  by_contra hznot
  refine hz ?_
  have hfun : Work.BoseDict.etaOf e w z = ∑ l : Fin m, (w l : ℂ) * e l z := rfl
  rw [hfun, Finset.sum_eq_zero fun l _ => ?_]
  have : e l z = 0 := Function.notMem_support.mp fun h => hznot (hsupp l h)
  rw [this, mul_zero]

theorem etaOf_weak_bound {m : ℕ} {e : Fin m → E3 → ℂ} (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (w : Fin m → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖Work.BoseDict.etaOf e w z‖ ≤ C := by
  choose C hC using hbdd
  refine ⟨∑ l : Fin m, ‖(w l : ℂ)‖ * max (C l) 0,
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (le_max_right _ _), fun z => ?_⟩
  have hfun : Work.BoseDict.etaOf e w = fun z : E3 => ∑ l : Fin m, (w l : ℂ) * e l z := rfl
  rw [hfun]
  calc ‖∑ l : Fin m, (w l : ℂ) * e l z‖ ≤ ∑ l : Fin m, ‖(w l : ℂ) * e l z‖ := norm_sum_le _ _
    _ = ∑ l : Fin m, ‖(w l : ℂ)‖ * ‖e l z‖ := by simp
    _ ≤ ∑ l : Fin m, ‖(w l : ℂ)‖ * max (C l) 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left ((hC l z).trans (le_max_left _ _)) (norm_nonneg _)

end Work.MB
