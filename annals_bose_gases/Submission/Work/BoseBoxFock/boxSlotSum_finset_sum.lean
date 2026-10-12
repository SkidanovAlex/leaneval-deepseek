import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_finset_sum` — `boxSlotSum` is additive over finite sums of states

`Work.BoseDict.boxSlotSum e T Θ = Σ_j Σ_l Σ_{l'} (T (evec l'))_l • boxSlotOf e (evec l) (evec l') j Θ`
is the first-quantised form of a one-body operator `T` on the box (`Xn d → ℂ`).  This file proves
that it is `ℂ`-linear in its state argument, in the finite-sum form needed downstream:

    boxSlotSum e T (Σ_{U ∈ s} c U • Ψ U) = Σ_{U ∈ s} c U • boxSlotSum e T (Ψ U) .

The proof goes through the rank-one slots: `boxSlotOf e w v j Θ` is
`fun x => η_w(x_j) · ∫_z conj(η_v z) · Θ(x[j ↦ z])`, so the work is the linearity of that Bochner
integral.  Integrability is supplied by the hypotheses: each `e k` is continuous with compact
support, so `η_v = Σ_l v_l e_l` is continuous with compact support, hence integrable; the state is
measurable and bounded, so the product is integrable (`Integrable.mul_bdd`).  The one-particle
operator `T` only enters through the (real) coefficients `(T (evec l'))_l`, which are constants
with respect to the state, so the `Σ_j Σ_l Σ_{l'}`-bookkeeping is `Finset` algebra.

The finiteness of the index set `s` is handled by `Finset.induction`, the induction step using the
two-term additivity and the scalar homogeneity.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The physical function `η_w` has compact support and is continuous -/

/-- `η_w = Σ_l w_l e_l`, written as a `Finset` sum of functions. -/
private lemma etaOf_eq_sum {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) :
    etaOf e w = ∑ l : Fin m, (fun _ : Sp => (w l : ℂ)) * (e l) := by
  funext z
  simp only [etaOf, Finset.sum_apply, Pi.mul_apply]

private lemma continuous_etaOf {m : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (w : Fin m → ℝ) : Continuous (etaOf e w) := by
  rw [etaOf_eq_sum e w]
  simp only [Finset.sum_fn]
  exact continuous_finsetSum _ (fun l _ => Continuous.mul continuous_const (he l))

private lemma hasCompactSupport_etaOf {m : ℕ} {e : Fin m → Sp → ℂ}
    (hec : ∀ l, HasCompactSupport (e l)) (w : Fin m → ℝ) :
    HasCompactSupport (etaOf e w) := by
  rw [etaOf_eq_sum e w]
  exact HasCompactSupport.finset_sum (fun l _ => HasCompactSupport.mul_left (hec l))

/-! ## 2. The change of variable `z ↦ x[j ↦ z]` is measurable -/

private lemma measurable_update {d : ℕ} (x : Xn d) (j : Fin d) :
    Measurable (fun z : Sp => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-! ## 3. Integrability of the slot integrand -/

private lemma integrable_slotIntegrand {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {Θ : Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (x : Xn d) (j : Fin d) (v : Fin m → ℝ) :
    Integrable (fun z : Sp => (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)) := by
  obtain ⟨C, hC⟩ := hΘb
  refine Integrable.mul_bdd (c := C) ?_ ?_ ?_
  · exact Continuous.integrable_of_hasCompactSupport
      (Complex.continuous_conj.comp (continuous_etaOf he v))
      ((hasCompactSupport_etaOf hec v).comp_left (map_zero _))
  · exact (hΘm.comp (measurable_update x j)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => hC _)

/-! ## 4. Linearity of the individual slots `boxSlotOf` -/

private lemma boxSlotOf_add {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (w v : Fin m → ℝ) (j : Fin d) {Φ Ψ : Xn d → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    boxSlotOf e w v j (Φ + Ψ) = boxSlotOf e w v j Φ + boxSlotOf e w v j Ψ := by
  funext x
  simp only [boxSlotOf, Pi.add_apply]
  have hI : (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * (Φ (Function.update x j z) + Ψ (Function.update x j z)))
      = (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Φ (Function.update x j z))
        + (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Ψ (Function.update x j z)) := by
    rw [← integral_add (integrable_slotIntegrand he hec hΦm hΦb x j v)
          (integrable_slotIntegrand he hec hΨm hΨb x j v)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [mul_add]
  rw [hI]
  ring

private lemma boxSlotOf_smul {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (w v : Fin m → ℝ) (j : Fin d) (c : ℂ) {Φ : Xn d → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    boxSlotOf e w v j (c • Φ) = c • boxSlotOf e w v j Φ := by
  funext x
  simp only [boxSlotOf, Pi.smul_apply]
  have hI : (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * (c • Φ (Function.update x j z)))
      = c • (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Φ (Function.update x j z)) := by
    rw [show (fun z : Sp => (starRingEnd ℂ) (etaOf e v z) * (c • Φ (Function.update x j z)))
        = fun z : Sp => c • ((starRingEnd ℂ) (etaOf e v z) * Φ (Function.update x j z)) from by
        funext z
        simp only [smul_eq_mul]
        ring]
    exact integral_smul c _
  rw [hI]
  simp only [smul_eq_mul]
  ring

private lemma boxSlotOf_zero {m d : ℕ} (e : Fin m → Sp → ℂ) (w v : Fin m → ℝ) (j : Fin d) :
    boxSlotOf e w v j (0 : Xn d → ℂ) = 0 := by
  funext x
  simp [boxSlotOf]

/-! ## 5. Linearity of `boxSlotSum` -/

private lemma boxSlotSum_add {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Φ Ψ : Xn d → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    boxSlotSum e T (Φ + Ψ) = boxSlotSum e T Φ + boxSlotSum e T Ψ := by
  have h : ∀ (j : Fin d) (l l' : Fin m),
      boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j (Φ + Ψ)
        = boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Φ
          + boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ :=
    fun j l l' => boxSlotOf_add he hec _ _ j hΦm hΦb hΨm hΨb
  simp only [boxSlotSum, h, smul_add, Finset.sum_add_distrib]

private lemma boxSlotSum_smul {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : ℂ) {Φ : Xn d → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    boxSlotSum e T (c • Φ) = c • boxSlotSum e T Φ := by
  have h : ∀ (j : Fin d) (l l' : Fin m),
      T (Work.BoseB4.evec m l') l • boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j (c • Φ)
        = c • (T (Work.BoseB4.evec m l') l • boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Φ) := by
    intro j l l'
    rw [boxSlotOf_smul he hec _ _ j c hΦm hΦb]
    exact smul_comm _ _ _
  simp only [boxSlotSum, h, ← Finset.smul_sum]

/-! ## 6. Bookkeeping: measurability and boundedness of finite linear combinations -/

private lemma measurable_smul_sum {ι : Type*} [DecidableEq ι] {d : ℕ} {c : ι → ℂ}
    {f : ι → Xn d → ℂ} (h : ∀ U, Measurable (f U)) (t : Finset ι) :
    Measurable (∑ U ∈ t, c U • f U) := by
  rw [Finset.sum_fn]
  exact Finset.measurable_sum t (fun U _ => (h U).const_smul (c U))

private lemma exists_bound_smul_sum {ι : Type*} [DecidableEq ι] {d : ℕ} {c : ι → ℂ}
    {f : ι → Xn d → ℂ} (h : ∀ U, ∃ C, ∀ x, ‖f U x‖ ≤ C) (t : Finset ι) :
    ∃ C, ∀ x, ‖(∑ U ∈ t, c U • f U) x‖ ≤ C := by
  induction t using Finset.induction with
  | empty => exact ⟨0, by intro x; simp⟩
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

/-! ## 7. The finite-sum form -/

private lemma boxSlotSum_finset_sum_aux {m d : ℕ} {e : Fin m → Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    {ι : Type*} [DecidableEq ι] (c : ι → ℂ) (Ψ : ι → Xn d → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) (s : Finset ι) :
    boxSlotSum e T (∑ U ∈ s, c U • Ψ U) = ∑ U ∈ s, c U • boxSlotSum e T (Ψ U) := by
  induction s using Finset.induction with
  | empty => funext x; simp [boxSlotSum, boxSlotOf]
  | insert a s ha ih =>
      have hsplit : (∑ U ∈ insert a s, c U • Ψ U) = c a • Ψ a + ∑ U ∈ s, c U • Ψ U :=
        Finset.sum_insert ha
      have hsplit2 : (∑ U ∈ insert a s, c U • boxSlotSum e T (Ψ U))
          = c a • boxSlotSum e T (Ψ a) + ∑ U ∈ s, c U • boxSlotSum e T (Ψ U) :=
        Finset.sum_insert ha
      have hb1 : ∃ C, ∀ x, ‖(c a • Ψ a) x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hΨb a
        exact ⟨‖c a‖ * C, fun x => by
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
      rw [hsplit, hsplit2,
        boxSlotSum_add he hec T ((hΨm a).const_smul (c a)) hb1
          (measurable_smul_sum hΨm s) (exists_bound_smul_sum hΨb s),
        ih, boxSlotSum_smul he hec T (c a) (hΨm a) (hΨb a)]

/-! ## 8. The target -/

theorem boxSlotSum_finset_sum {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (Ψ : ι → (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e T (fun x => Finset.sum s (fun U => c U • Ψ U x))
      = fun x => Finset.sum s (fun U => c U • Work.BoseDict.boxSlotSum e T (Ψ U) x) := by
  have h1 : (fun x => Finset.sum s (fun U => c U • Ψ U x)) = ∑ U ∈ s, c U • Ψ U := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
  have h2 : (∑ U ∈ s, c U • Work.BoseDict.boxSlotSum e T (Ψ U))
      = fun x => Finset.sum s (fun U => c U • Work.BoseDict.boxSlotSum e T (Ψ U) x) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [h1, boxSlotSum_finset_sum_aux he hec T c Ψ hΨm hΨb s, h2]

end Work.BoseBoxFock
