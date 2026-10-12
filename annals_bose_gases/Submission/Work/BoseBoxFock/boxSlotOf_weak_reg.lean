import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-!
# `Work.BoseBoxFock.boxSlotOf_weak_reg` — weak regularity of a box slot

`boxSlotOf e w v j Θ` is the `j`-th slot of the first-quantised rank-one operator
`|η_w⟩⟨η_v|`:

  `(boxSlotOf e w v j Θ)(x) = η_w(x_j) · ∫_z conj(η_v z) · Θ(x[j ↦ z])`,  `η_w = Σ_l w_l e_l`.

The existing `Work.BoseBoxFock.boxSlotOf_measurable_bounded` proves measurability and
boundedness of the slot under the hypothesis that the modes `e l` are **continuous with
compact support**.  The lemma here is the *weak* version: it assumes only that each `e l` is
**measurable, bounded and supported in the box** `boxL ℓ`.  This is the regularity that the
dictionary's consumers actually have available (the corpus modes are only known to be
measurable and localised in the box; continuity is not part of the API).

The proof is the same pointwise argument as in the continuous case; two ingredients are
replaced:

* the compact support of `η_v` is replaced by the bound `‖η_v z‖ ≤ B` together with
  `support (η_v) ⊆ boxL ℓ`, which gives `‖η_v‖ ≤ max B 0 · 1_{boxL ℓ}` and hence
  `Integrable (fun z => ‖η_v z‖)` (using `BoxData.integrable_boxL_indicator` for the
  indicator of the box, which has finite volume);
* continuity of `η_w`, `η_v` is replaced by measurability.

Everything else — joint measurability of the integrand via `Function.update`, the parametric
integral `StronglyMeasurable.integral_prod_right'`, and the domination of the fibre integral
by `‖η_v z‖ · max CΘ 0` — is verbatim.
-/

/-- The superposed mode `η_w = Σ_l w_l e_l` is measurable when the modes are. -/
theorem etaOf_measurable {m : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l, Measurable (e l)) (w : Fin m → ℝ) : Measurable (Work.BoseDict.etaOf e w) := by
  unfold Work.BoseDict.etaOf
  exact Finset.measurable_sum Finset.univ (fun l _ => measurable_const.mul (he l))

/-- The superposed mode `η_w = Σ_l w_l e_l` is bounded when the modes are. -/
theorem etaOf_exists_bound_of_bounded {m : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) (w : Fin m → ℝ) :
    ∃ B : ℝ, ∀ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ≤ B := by
  classical
  choose C hC using hbdd
  refine ⟨∑ l, |w l| * max (C l) 0, fun z => ?_⟩
  have h1 : ‖Work.BoseDict.etaOf e w z‖ ≤ ∑ l : Fin m, ‖(w l : ℂ) * e l z‖ := by
    rw [Work.BoseDict.etaOf]
    exact norm_sum_le _ _
  have h2 : ∀ l : Fin m, ‖(w l : ℂ) * e l z‖ ≤ |w l| * max (C l) 0 := by
    intro l
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hC l z).trans (le_max_left _ _)) (abs_nonneg _)
  exact h1.trans (Finset.sum_le_sum (fun l _ => h2 l))

/-- The superposed mode `η_w = Σ_l w_l e_l` is supported in the box when the modes are. -/
theorem etaOf_support_subset {m : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) :
    Function.support (Work.BoseDict.etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro z hz
  by_contra h
  refine hz ?_
  rw [Work.BoseDict.etaOf]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have : e l z = 0 := by
    by_contra hne
    exact h (hsupp l (Function.mem_support.mpr hne))
  rw [this, mul_zero]

/-- **`η_v` is `L¹`** for a measurable, bounded, box-supported mode system: it is dominated by
`max B 0 · 1_{boxL ℓ}`, whose integral is finite by `BoxData.integrable_boxL_indicator`. -/
theorem integrable_norm_etaOf {m : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (v : Fin m → ℝ) :
    Integrable (fun z : Work.BoseDict.Sp => ‖Work.BoseDict.etaOf e v z‖) := by
  obtain ⟨B, hB⟩ := etaOf_exists_bound_of_bounded hbdd v
  have hgint : Integrable (fun z : Work.BoseDict.Sp =>
      max B 0 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z) :=
    (Work.BoseB4.BoxData.integrable_boxL_indicator Work.BoseK15.corpusBox ℓ).const_mul (max B 0)
  refine MeasureTheory.Integrable.mono' hgint
    ((etaOf_measurable hmeas v).aestronglyMeasurable.norm)
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hz, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (hB z).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, mul_zero]
    have h0 : Work.BoseDict.etaOf e v z = 0 := by
      by_contra hne
      exact hz (etaOf_support_subset hsupp v (Function.mem_support.mpr hne))
    rw [h0]; simp

/-- **Weak regularity of a box slot.**  For merely measurable, bounded, box-supported modes `e`
and a measurable bounded state `Θ`, the slot `boxSlotOf e w v j Θ` is measurable and bounded
on the configuration space. -/
theorem boxSlotOf_weak_reg {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotOf e w v j Θ) ∧
      ∃ C : ℝ, ∀ x : Work.BoseDict.Xn d, ‖Work.BoseDict.boxSlotOf e w v j Θ x‖ ≤ C := by
  have _hℓused : (0 : ℝ) < ℓ := hℓ
  have hmw : Measurable (Work.BoseDict.etaOf e w) := etaOf_measurable hmeas w
  have hmv : Measurable (Work.BoseDict.etaOf e v) := etaOf_measurable hmeas v
  have hintv : Integrable (fun z : Work.BoseDict.Sp => ‖Work.BoseDict.etaOf e v z‖) :=
    integrable_norm_etaOf hmeas hbdd hsupp v
  have hupd : Measurable (fun p : Work.BoseDict.Xn d × Work.BoseDict.Sp =>
      Function.update p.1 j p.2) := measurable_update_pair j
  have hjoint : Measurable (fun p : Work.BoseDict.Xn d × Work.BoseDict.Sp =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e v p.2) * Θ (Function.update p.1 j p.2)) :=
    ((Complex.continuous_conj.measurable.comp hmv).comp measurable_snd).mul (hΘm.comp hupd)
  refine ⟨?_, ?_⟩
  · have hsm : StronglyMeasurable (fun x : Work.BoseDict.Xn d =>
        ∫ z : Work.BoseDict.Sp,
          (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    exact (hmw.comp (measurable_pi_apply j)).mul hsm.measurable
  · obtain ⟨CΘ, hCΘ⟩ := hΘb
    obtain ⟨Bw, hBw⟩ := etaOf_exists_bound_of_bounded hbdd w
    refine ⟨max Bw 0 * (max CΘ 0 *
      ∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e v z‖), fun x => ?_⟩
    have hmono : (∫ z : Work.BoseDict.Sp,
          ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖)
        ≤ ∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
        (hintv.mul_const _) (Filter.Eventually.of_forall fun z => ?_)
      show ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖
        ≤ ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _)
    calc ‖Work.BoseDict.boxSlotOf e w v j Θ x‖
        = ‖Work.BoseDict.etaOf e w (x j)‖ *
            ‖∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖ := by
          rw [Work.BoseDict.boxSlotOf, norm_mul]
      _ ≤ max Bw 0 *
            ‖∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖ :=
          mul_le_mul_of_nonneg_right ((hBw _).trans (le_max_left _ _)) (norm_nonneg _)
      _ ≤ max Bw 0 *
            (∫ z : Work.BoseDict.Sp,
              ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (le_max_right _ _)
      _ ≤ max Bw 0 *
            (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0) :=
          mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
      _ = max Bw 0 * (max CΘ 0 *
            ∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e v z‖) := by
          rw [MeasureTheory.integral_mul_const]; ring

end Work.BoseBoxFock
