import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.boxSlotSum_measurable_bounded_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.MB.boxSlotSum_bdd` — the first-quantised slot sum at the weak mode hypotheses

The measurable/bounded ("weak") mode bundle replaces the continuous, compactly supported modes of
`Work.BoseBoxFock.boxSlotSum_finset_sum` by `Measurable (e l)`, `∃ C, ∀ x, ‖e l x‖ ≤ C` and
`Function.support (e l) ⊆ boxL ℓ`.  This file proves the corresponding three statements for the
first-quantised slot sum `Work.BoseDict.boxSlotSum e T`:

* linearity in the state over finite sums (the weak analogue of
  `Work.BoseBoxFock.boxSlotSum_finset_sum`);
* measurability and everywhere boundedness of `boxSlotSum e T Ψ` for measurable, everywhere
  bounded states `Ψ` (this is the sibling `Work.MB.boxSlotSum_measurable_bounded_ae`);
* preservation of the box support: if `Ψ` vanishes pointwise outside `boxPow d ℓ` then so does
  `boxSlotSum e T Ψ`.

The linearity of `boxSlotSum` is the linearity of the single slot
`boxSlotOf e w v j Θ x = η_w(x_j) · ∫ z, conj (η_v z) · Θ (x[j ↦ z])` in the state `Θ`, i.e. the
linearity of that Bochner integral.  At the weak bundle the integrand is measurable (the modes are
measurable and `z ↦ update x j z` is measurable) and it is bounded and supported in the finite
measure set `boxL ℓ` (`Work.MB.etaOf_weak_bound`, `Work.MB.etaOf_weak_support`), so
`Work.MB.integrable_of_bdd_of_support` applies: this replaces the `Continuous` /
`HasCompactSupport` integrability of the strong chain.

The support statement is pointwise: for `x ∉ boxPow d ℓ` there is `i₀` with `x i₀ ∉ boxL ℓ`; the
slot-`i₀` terms die through `η_w(x i₀) = 0` (`Work.BoseDict.etaOf_pi_single` plus `hsupp`), while
for `j ≠ i₀` the inner integrand vanishes identically because the `i₀`-th coordinate of
`update x j z` is still `x i₀`.
-/

/-! ## 0. Elementary helpers -/

/-- `η` at the coordinate vector `evec m l` is the mode `e l`. -/
private theorem etaOf_evec_weak {m : ℕ} (e : Fin m → E3 → ℂ) (l : Fin m) (z : E3) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) z = e l z :=
  Work.BoseDict.etaOf_pi_single e l z

/-- The change of variable `z ↦ update x j z` is measurable (for fixed `x`, `j`). -/
private theorem measurable_update_fixed {d : ℕ} (x : Fin d → E3) (j : Fin d) :
    Measurable (fun z : E3 => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · have h : (fun z : E3 => Function.update x j z i) = fun z : E3 => z := by
      funext z
      simp [hij]
    rw [h]
    exact measurable_id
  · have h : (fun z : E3 => Function.update x j z i) = fun _ => x i := by
      funext z
      simp [hij]
    rw [h]
    exact measurable_const

/-! ## 1. The slot integrand is integrable at the weak bundle -/

/-- At the weak mode bundle the slot integrand is integrable: it is measurable, bounded by
`Bv · max CΘ 0` and supported in `boxL ℓ`, which has finite measure. -/
private theorem integrable_slotIntegrand_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (x : Fin d → E3) (j : Fin d) :
    Integrable (fun z : E3 => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
      Θ (Function.update x j z)) := by
  obtain ⟨Bv, hBvnn, hBv⟩ := etaOf_weak_bound hbdE v
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hvm : Measurable (Work.BoseDict.etaOf e v) := etaOf_weak_measurable hmeas v
  have hjoint : Measurable (fun z : E3 => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
      Θ (Function.update x j z)) :=
    (Complex.continuous_conj.measurable.comp hvm).mul
      (hΘm.comp (measurable_update_fixed x j))
  refine integrable_of_bdd_of_support (C := Bv * max CΘ 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    hjoint.aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hBv z) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hBvnn
  · intro z hz
    have hzv : Work.BoseDict.etaOf e v z = 0 :=
      Function.notMem_support.mp (fun h => hz (etaOf_weak_support hsupp v h))
    rw [hzv, map_zero, zero_mul]

/-! ## 2. Linearity of the single slot `boxSlotOf` -/

/-- A single slot is additive in the state at the weak mode bundle. -/
private theorem boxSlotOf_add_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {Φ Ψ : (Fin d → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseDict.boxSlotOf e w v j (Φ + Ψ)
      = Work.BoseDict.boxSlotOf e w v j Φ + Work.BoseDict.boxSlotOf e w v j Ψ := by
  funext x
  simp only [Work.BoseDict.boxSlotOf, Pi.add_apply]
  have hI : (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        (Φ (Function.update x j z) + Ψ (Function.update x j z)))
      = (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
            Φ (Function.update x j z))
        + (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
            Ψ (Function.update x j z)) := by
    rw [← integral_add (integrable_slotIntegrand_weak hmeas hbdE hsupp v hΦm hΦb x j)
      (integrable_slotIntegrand_weak hmeas hbdE hsupp v hΨm hΨb x j)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [mul_add]
  rw [hI]
  ring

/-- A single slot is homogeneous in the state at the weak mode bundle. -/
private theorem boxSlotOf_smul_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (c : ℂ) {Φ : (Fin d → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseDict.boxSlotOf e w v j (c • Φ) = c • Work.BoseDict.boxSlotOf e w v j Φ := by
  funext x
  simp only [Work.BoseDict.boxSlotOf, Pi.smul_apply]
  have hI : (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        (c • Φ (Function.update x j z)))
      = c • (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
            Φ (Function.update x j z)) := by
    rw [show (fun z : E3 => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
          (c • Φ (Function.update x j z)))
        = fun z : E3 => c • ((starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
            Φ (Function.update x j z)) from by
      funext z
      simp only [smul_eq_mul]
      ring]
    exact integral_smul c _
  rw [hI]
  simp only [smul_eq_mul]
  ring

/-! ## 3. Linearity of the slot sum `boxSlotSum` -/

/-- `boxSlotSum` is additive in the state at the weak mode bundle. -/
private theorem boxSlotSum_add_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Φ Ψ : (Fin d → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e T (Φ + Ψ)
      = Work.BoseDict.boxSlotSum e T Φ + Work.BoseDict.boxSlotSum e T Ψ := by
  have h : ∀ (j : Fin d) (l l' : Fin m),
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j (Φ + Ψ)
        = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Φ
          + Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ :=
    fun j l l' => boxSlotOf_add_weak hmeas hbdE hsupp _ _ j hΦm hΦb hΨm hΨb
  simp only [Work.BoseDict.boxSlotSum, h, smul_add, Finset.sum_add_distrib]

/-- `boxSlotSum` is homogeneous in the state at the weak mode bundle. -/
private theorem boxSlotSum_smul_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : ℂ) {Φ : (Fin d → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e T (c • Φ) = c • Work.BoseDict.boxSlotSum e T Φ := by
  have h : ∀ (j : Fin d) (l l' : Fin m),
      T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j (c • Φ)
        = c • (T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Φ) := by
    intro j l l'
    rw [boxSlotOf_smul_weak hmeas hbdE hsupp _ _ j c hΦm hΦb]
    exact smul_comm _ _ _
  simp only [Work.BoseDict.boxSlotSum, h, ← Finset.smul_sum]

/-- Measurability of a finite linear combination of measurable states. -/
private theorem measurable_smul_sum {ι : Type*} [DecidableEq ι] {d : ℕ} {c : ι → ℂ}
    {f : ι → (Fin d → E3) → ℂ} (h : ∀ U, Measurable (f U)) (t : Finset ι) :
    Measurable (∑ U ∈ t, c U • f U) := by
  rw [Finset.sum_fn]
  exact Finset.measurable_sum t (fun U _ => (h U).const_smul (c U))

/-- Boundedness of a finite linear combination of bounded states. -/
private theorem exists_bound_smul_sum {ι : Type*} [DecidableEq ι] {d : ℕ} {c : ι → ℂ}
    {f : ι → (Fin d → E3) → ℂ} (h : ∀ U, ∃ C, ∀ x, ‖f U x‖ ≤ C) (t : Finset ι) :
    ∃ C, ∀ x, ‖(∑ U ∈ t, c U • f U) x‖ ≤ C := by
  induction t using Finset.induction with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a t ha ih =>
      obtain ⟨C1, h1⟩ := h a
      obtain ⟨C2, h2⟩ := ih
      refine ⟨‖c a‖ * C1 + C2, fun x => ?_⟩
      rw [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply]
      calc ‖c a • f a x + (∑ U ∈ t, c U • f U) x‖
          ≤ ‖c a • f a x‖ + ‖(∑ U ∈ t, c U • f U) x‖ := norm_add_le _ _
        _ = ‖c a‖ * ‖f a x‖ + ‖(∑ U ∈ t, c U • f U) x‖ := by rw [norm_smul]
        _ ≤ ‖c a‖ * C1 + C2 :=
            add_le_add (mul_le_mul_of_nonneg_left (h1 x) (norm_nonneg _)) (h2 x)

/-- Linearity of `boxSlotSum` over finite sums of states, at the weak mode bundle (function-sum
form). -/
private theorem boxSlotSum_finset_sum_weak_aux {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    {ι : Type} [DecidableEq ι] (c : ι → ℂ) (Ψ : ι → (Fin d → E3) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) (s : Finset ι) :
    Work.BoseDict.boxSlotSum e T (∑ U ∈ s, c U • Ψ U)
      = ∑ U ∈ s, c U • Work.BoseDict.boxSlotSum e T (Ψ U) := by
  induction s using Finset.induction with
  | empty => funext x; simp [Work.BoseDict.boxSlotSum, Work.BoseDict.boxSlotOf]
  | insert a s ha ih =>
      have hsplit : (∑ U ∈ insert a s, c U • Ψ U) = c a • Ψ a + ∑ U ∈ s, c U • Ψ U :=
        Finset.sum_insert ha
      have hsplit2 : (∑ U ∈ insert a s, c U • Work.BoseDict.boxSlotSum e T (Ψ U))
          = c a • Work.BoseDict.boxSlotSum e T (Ψ a)
            + ∑ U ∈ s, c U • Work.BoseDict.boxSlotSum e T (Ψ U) :=
        Finset.sum_insert ha
      have hb1 : ∃ C, ∀ x, ‖(c a • Ψ a) x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hΨb a
        exact ⟨‖c a‖ * C, fun x => by
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
      rw [hsplit, hsplit2,
        boxSlotSum_add_weak hmeas hbdE hsupp T ((hΨm a).const_smul (c a)) hb1
          (measurable_smul_sum hΨm s) (exists_bound_smul_sum hΨb s),
        ih, boxSlotSum_smul_weak hmeas hbdE hsupp T (c a) (hΨm a) (hΨb a)]

/-! ## 4. Preservation of the box support -/

/-- If the `j`-th coordinate of `x` is outside the box then the slot `j` of any state vanishes. -/
private theorem boxSlotOf_eq_zero_of_notMem_boxL {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {x : Fin d → E3}
    (hj : x j ∉ Work.BoseK15.corpusBox.boxL ℓ) (Ψ : (Fin d → E3) → ℂ) :
    Work.BoseDict.boxSlotOf e w v j Ψ x = 0 := by
  rw [Work.BoseDict.boxSlotOf]
  have hw : Work.BoseDict.etaOf e w (x j) = 0 :=
    Function.notMem_support.mp (fun h => hj (etaOf_weak_support hsupp w h))
  rw [hw, zero_mul]

/-- If the `i₀`-th coordinate of `x` is outside the box and `j ≠ i₀`, then the slot `j` of a state
supported in `boxPow d ℓ` vanishes at `x` (the inner integrand is identically zero). -/
private theorem boxSlotOf_eq_zero_of_ne_of_support {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (w v : Fin m → ℝ) {j i₀ : Fin d} (hji : i₀ ≠ j) {x : Fin d → E3}
    (hi₀ : x i₀ ∉ Work.BoseK15.corpusBox.boxL ℓ) {Ψ : (Fin d → E3) → ℂ}
    (hΨs : Function.support Ψ ⊆ boxPow d ℓ) :
    Work.BoseDict.boxSlotOf e w v j Ψ x = 0 := by
  rw [Work.BoseDict.boxSlotOf]
  have hpt : ∀ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
      Ψ (Function.update x j z) = 0 := by
    intro z
    have hupd : Function.update x j z i₀ = x i₀ := by
      rw [Function.update_apply, if_neg hji]
    have hmem : Function.update x j z ∉ boxPow d ℓ := by
      simp only [mem_boxPow_iff]
      exact fun hall => hi₀ (hupd ▸ hall i₀)
    have hz : Ψ (Function.update x j z) = 0 :=
      Function.notMem_support.mp (fun h => hmem (hΨs h))
    rw [hz, mul_zero]
  have hzero : (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
      Ψ (Function.update x j z)) = 0 := by
    rw [show (fun z : E3 => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        Ψ (Function.update x j z)) = fun _ => (0 : ℂ) from funext hpt]
    simp
  rw [hzero, mul_zero]

/-- `boxSlotSum e T` preserves the box support of the state, at the weak mode bundle. -/
private theorem boxSlotSum_support_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Ψ : (Fin d → E3) → ℂ}
    (hΨs : Function.support Ψ ⊆ boxPow d ℓ) :
    Function.support (Work.BoseDict.boxSlotSum e T Ψ) ⊆ boxPow d ℓ := by
  intro x hx
  by_contra hxnot
  refine hx ?_
  have hxnot' : ¬ ∀ i : Fin d, x i ∈ Work.BoseK15.corpusBox.boxL ℓ :=
    fun h => hxnot (mem_boxPow_iff.mpr h)
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hxnot'
  have hfun : Work.BoseDict.boxSlotSum e T Ψ x
      = ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x := by
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  rw [hfun]
  refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun l _ =>
    Finset.sum_eq_zero (fun l' _ => ?_)))
  by_cases hji : j = i₀
  · have hj' : x j ∉ Work.BoseK15.corpusBox.boxL ℓ := by
      rw [hji]; exact hi₀
    rw [boxSlotOf_eq_zero_of_notMem_boxL hsupp (Work.BoseB4.evec m l) (Work.BoseB4.evec m l')
      j hj' Ψ, smul_zero]
  · have hne : i₀ ≠ j := fun h => hji h.symm
    rw [boxSlotOf_eq_zero_of_ne_of_support (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') hne hi₀
      hΨs, smul_zero]

/-! ## 5. The target -/

/-- **The first-quantised slot sum `boxSlotSum e T` at the weak mode hypotheses: linearity in the
state, measurability, everywhere boundedness, and preservation of the box support.**

`boxSlotSum e T Θ = Σ_j Σ_l Σ_l' (T (evec m l'))_l • boxSlotOf e (evec m l) (evec m l') j Θ`, with
`boxSlotOf e w v j Θ x = etaOf e w (x j) · ∫ z, star (etaOf e v z) · Θ (update x j z)`.

The modes `e l` are measurable, everywhere bounded and supported in
`Work.BoseK15.corpusBox.boxL ℓ`; the states are measurable and everywhere bounded.  The three
conjuncts are

1. `boxSlotSum` is `ℂ`-linear in the state over finite sums (the analogue for `boxSlotSum` of
   `Work.BoseBoxFock.boxSlotSum_finset_sum`, which needs `Continuous`/`HasCompactSupport` modes);
   the linearity of each slot `boxSlotOf e w v j` in the state is the linearity of the Bochner
   integral `∫ z, star (etaOf e v z) · Θ (update x j z)`, whose integrand is bounded and supported
   in `boxL ℓ` (finite measure) — `Work.MB.etaOf_weak_bound`, `Work.MB.etaOf_weak_support`,
   `Work.MB.integrable_of_bdd_of_support`, `MeasureTheory.integral_finsetSum`,
   `MeasureTheory.integral_smul`;
2. `boxSlotSum e T Ψ` is measurable and everywhere bounded when `Ψ` is (finite sums of the
   measurable bounded slots; the bound uses `Work.MB.etaOf_weak_bound` and the finiteness of
   `boxL ℓ`);
3. if `Ψ` vanishes pointwise outside `Work.MB.boxPow d ℓ = (boxL ℓ)^d` then so does
   `boxSlotSum e T Ψ`: for `x ∉ boxPow d ℓ`, say `x i₀ ∉ boxL ℓ`, the slot-`i₀` terms die through
   the factor `etaOf e (evec m l) (x i₀) = e l (x i₀) = 0` (`Work.BoseBoxFock.etaOf_evec_self`
   plus `hsupp`), while for `j ≠ i₀` the inner integrand `star (etaOf e v z) · Ψ (update x j z)`
   vanishes identically because the `i₀`-th coordinate of `update x j z` is still `x i₀`. -/
theorem boxSlotSum_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ {κ : Type} [DecidableEq κ] (s : Finset κ) (c : κ → ℂ)
        (Ψ : κ → (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ),
        (∀ k, Measurable (Ψ k)) → (∀ k, ∃ C, ∀ x, ‖Ψ k x‖ ≤ C) →
        Work.BoseDict.boxSlotSum e T (fun x => ∑ k ∈ s, c k • Ψ k x)
          = fun x => ∑ k ∈ s, c k • Work.BoseDict.boxSlotSum e T (Ψ k) x) ∧
    (∀ (Ψ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ), Measurable Ψ → (∃ C, ∀ x, ‖Ψ x‖ ≤ C) →
        Measurable (Work.BoseDict.boxSlotSum e T Ψ) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseDict.boxSlotSum e T Ψ x‖ ≤ C) ∧
        (Function.support Ψ ⊆ Work.MB.boxPow d ℓ →
          Function.support (Work.BoseDict.boxSlotSum e T Ψ) ⊆ Work.MB.boxPow d ℓ)) := by
  refine ⟨?_, ?_⟩
  · intro κ _ s c Ψ hΨm hΨb
    have h1 : (fun x : Fin d → E3 => ∑ k ∈ s, c k • Ψ k x) = ∑ k ∈ s, c k • Ψ k := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply]
    have h2 : (∑ k ∈ s, c k • Work.BoseDict.boxSlotSum e T (Ψ k))
        = fun x : Fin d → E3 => ∑ k ∈ s, c k • Work.BoseDict.boxSlotSum e T (Ψ k) x := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply]
    rw [h1, boxSlotSum_finset_sum_weak_aux hmeas hbdd hsupp T c Ψ hΨm hΨb s, h2]
  · intro Ψ hΨm hΨb
    obtain ⟨hm, hb⟩ := boxSlotSum_measurable_bounded_ae hmeas hbdd hsupp T Ψ hΨm hΨb
    obtain ⟨C, hC⟩ := hb
    exact ⟨hm, ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩,
      fun hΨs => boxSlotSum_support_weak hmeas hbdd hsupp T hΨs⟩

end Work.MB
