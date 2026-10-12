import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-!
# `Work.BoseBoxFock.boxSlotSum_measurable_bounded` — regularity of the slot sum

For continuous, compactly supported modes `e` and a **measurable, bounded** state
`Θ : Xn d → ℂ`, the first-quantised slot sum

  `boxSlotSum e T Θ = Σ_j Σ_l Σ_l' (T e_{l'})_l • boxSlotOf e e_l e_{l'} j Θ`

is measurable and bounded on `Xn d`.  This is the regularity input that every downstream
consumer of the box ↔ model dictionary needs: the slot sums are the *box side* of the model's
one-particle operators, and the rows of `H2ndF` are assembled from them, so they must be
measurable and bounded before any `L²` pairing with them can be formed (and before the
interchange of the slot sum with the configuration integral is legitimate).

The proof is pointwise.  For a single slot,

  `(boxSlotOf e w v j Θ) x = η_w(x_j) · ∫_z conj (η_v z) · Θ (x[j ↦ z])`,

so it suffices to show that

* `x ↦ η_w(x_j)` is continuous (`η_w = Σ_l w_l e_l` is a finite sum of continuous functions),
* `x ↦ ∫_z conj (η_v z) · Θ (update x j z)` is measurable — the integrand is *jointly* measurable
  (`update` is measurable in `(x, z)`) so `StronglyMeasurable.integral_prod_right'` applies,
* the fibre integral is bounded: the integrand is dominated by the *integrable* function
  `z ↦ ‖η_v z‖ · max CΘ 0` (`η_v` is continuous with compact support, hence integrable), so
  `‖∫_z …‖ ≤ ∫_z ‖…‖ ≤ max CΘ 0 · ∫_z ‖η_v z‖`.

The `T`-dependent sum is then a finite sum of scalars times these slot functions.
-/

/-! ## 1. Regularity of the superposed mode `η_w = Σ_l w_l e_l` -/

/-- The superposed mode `η_w = Σ_l w_l e_l` is continuous when the modes are. -/
theorem etaOf_continuous {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (w : Fin m → ℝ) : Continuous (Work.BoseDict.etaOf e w) := by
  unfold Work.BoseDict.etaOf
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul (he l))

/-- The superposed mode `η_w = Σ_l w_l e_l` has compact support when the modes do. -/
theorem etaOf_hasCompactSupport {m : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) (w : Fin m → ℝ) :
    HasCompactSupport (Work.BoseDict.etaOf e w) := by
  unfold Work.BoseDict.etaOf
  exact hasCompactSupport_finset_sum Finset.univ
    (fun l (z : Ω) => (w l : ℂ) * e l z)
    (fun l _ => (hec l).mul_left (f := fun _ : Ω => (w l : ℂ)))

/-- `η_w` is bounded, hence so is the corresponding slot factor. -/
theorem etaOf_exists_bound {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (w : Fin m → ℝ) :
    ∃ B, ∀ z : Ω, ‖Work.BoseDict.etaOf e w z‖ ≤ B :=
  (etaOf_continuous e he w).bounded_above_of_compact_support
    (etaOf_hasCompactSupport e hec w)

/-! ## 2. Regularity of a single slot -/

/-- `(x, z) ↦ Function.update x j z` is measurable (each coordinate is either the fibre
variable or a coordinate of `x`). -/
theorem measurable_update_pair {d : ℕ} (j : Fin d) :
    Measurable (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2) := by
  refine Measurable.of_eval (fun i => ?_)
  by_cases hi : i = j
  · subst hi
    have h : (fun p : (Fin d → Ω) × Ω => Function.update p.1 i p.2 i) = fun p => p.2 := by
      funext p; rw [Function.update_apply, if_pos rfl]
    rw [h]; exact measurable_snd
  · have h : (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2 i) = fun p => p.1 i := by
      funext p; rw [Function.update_apply, if_neg hi]
    rw [h]; exact (measurable_pi_apply i).comp measurable_fst

/-- **A single slot preserves measurability and boundedness.**  For continuous compactly supported
modes and a measurable bounded state `Θ`, the slot operator
`(boxSlotOf e w v j Θ) x = η_w(x_j) · ∫_z conj (η_v z) · Θ (x[j ↦ z])` is measurable and bounded
on `Xn d`. -/
theorem boxSlotOf_measurable_bounded {m d : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (w v : Fin m → ℝ) (j : Fin d) (Θ : (Fin d → Ω) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotOf e w v j Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e w v j Θ x‖ ≤ C := by
  have hcontw : Continuous (Work.BoseDict.etaOf e w) := etaOf_continuous e he w
  have hcontv : Continuous (Work.BoseDict.etaOf e v) := etaOf_continuous e he v
  have hcsv : HasCompactSupport (Work.BoseDict.etaOf e v) := etaOf_hasCompactSupport e hec v
  have hupd : Measurable (fun p : (Fin d → Ω) × Ω => Function.update p.1 j p.2) :=
    measurable_update_pair j
  have hjoint : Measurable (fun p : (Fin d → Ω) × Ω =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e v p.2) * Θ (Function.update p.1 j p.2)) :=
    (((Complex.continuous_conj.comp hcontv).measurable).comp measurable_snd).mul
      (hΘm.comp hupd)
  refine ⟨?_, ?_⟩
  · have hsm : StronglyMeasurable (fun x : Fin d → Ω =>
        ∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    exact ((hcontw.comp (continuous_apply j)).measurable).mul hsm.measurable
  · obtain ⟨CΘ, hCΘ⟩ := hΘb
    obtain ⟨Bw, hBw⟩ := etaOf_exists_bound e he hec w
    have hint : Integrable (fun z : Ω => ‖Work.BoseDict.etaOf e v z‖) :=
      (hcontv.integrable_of_hasCompactSupport hcsv).norm
    refine ⟨max Bw 0 * (max CΘ 0 * ∫ z : Ω, ‖Work.BoseDict.etaOf e v z‖), fun x => ?_⟩
    have hmono : (∫ z : Ω,
          ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖)
        ≤ ∫ z : Ω, ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0 := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => norm_nonneg _) (hint.mul_const _)
        (Filter.Eventually.of_forall fun z => ?_)
      show ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖
        ≤ ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _)
    calc ‖Work.BoseDict.boxSlotOf e w v j Θ x‖
        = ‖Work.BoseDict.etaOf e w (x j)‖ *
            ‖∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖ := by
          rw [Work.BoseDict.boxSlotOf, norm_mul]
      _ ≤ max Bw 0 *
            ‖∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖ :=
          mul_le_mul_of_nonneg_right ((hBw _).trans (le_max_left _ _)) (norm_nonneg _)
      _ ≤ max Bw 0 *
            (∫ z : Ω, ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)‖) :=
          mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
            (le_max_right _ _)
      _ ≤ max Bw 0 * (∫ z : Ω, ‖Work.BoseDict.etaOf e v z‖ * max CΘ 0) :=
          mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
      _ = max Bw 0 * (max CΘ 0 * ∫ z : Ω, ‖Work.BoseDict.etaOf e v z‖) := by
          rw [MeasureTheory.integral_mul_const]; ring

/-! ## 3. The slot sum -/

theorem boxSlotSum_measurable_bounded {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotSum e T Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseDict.boxSlotSum e T Θ x‖ ≤ C := by
  classical
  have hfun : Work.BoseDict.boxSlotSum e T Θ
      = fun x => ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
    funext x
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  have hterm : ∀ (j : Fin d) (l l' : Fin m),
      Measurable (fun x : Fin d → Ω => T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) ∧
      ∃ B, ∀ x : Fin d → Ω, ‖T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ B := by
    intro j l l'
    obtain ⟨hm, hb⟩ := boxSlotOf_measurable_bounded e he hec
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb
    refine ⟨hm.const_smul (T (Work.BoseB4.evec m l') l), ?_⟩
    obtain ⟨B, hB⟩ := hb
    refine ⟨‖T (Work.BoseB4.evec m l') l‖ * max B 0, fun x => ?_⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((hB x).trans (le_max_left _ _)) (norm_nonneg _)
  choose B hB using fun (j : Fin d) (l l' : Fin m) => (hterm j l l').2
  rw [hfun]
  refine ⟨?_, ⟨∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0, fun x => ?_⟩⟩
  · refine Finset.measurable_sum _ (fun j _ =>
      Finset.measurable_sum _ (fun l _ =>
        Finset.measurable_sum _ (fun l' _ => (hterm j l l').1)))
  · calc ‖∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖
        ≤ ∑ j : Fin d, ‖∑ l : Fin m, ∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ‖∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
            ‖T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ =>
            Finset.sum_le_sum (fun l _ => norm_sum_le _ _))
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0 :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ =>
            Finset.sum_le_sum (fun l' _ =>
              (hB j l l' x).trans (le_max_left _ _))))

end

end Work.BoseBoxFock
