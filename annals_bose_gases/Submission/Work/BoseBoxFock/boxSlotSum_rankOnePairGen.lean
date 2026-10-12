import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairDecompPairSetGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_rankOnePairGen` — the first quantisation of a rank-one operator

`Work.BoseDict.boxSlotSum e T Θ = Σ_j Σ_l Σ_{l'} (T e_{l'})_l • boxSlotOf e (evec l) (evec l') j Θ`
is, by definition, `Σ_j` of the rank-one expansion of the `j`-th slot of `T`.  For a **rank-one**
one-body operator `T = |w⟩⟨v|` (`Work.BoseBoxFock.rankOnePair`) that double sum *is* the single
superposed slot: the two forms agree,

    `boxSlotSum e (|w⟩⟨v|) Θ = Σ_j boxSlotOf e w v j Θ`,

because `η_w = Σ_l w_l e_l`, `conj (η_v) = Σ_{l'} v_{l'} conj (e_{l'})` and the Bochner integral is
additive over the finite sum of (integrable) mode slots.

This is the general-arity (`Xn d`) form of the first-quantised identity used by the box ↔ model
dictionary.  It is stated for the weak bundle of hypotheses (measurable / everywhere bounded /
supported in the corpus box `boxL ℓ`), which is exactly what is needed to make the integral of each
mode slot integrable; the module is otherwise self-contained (the `L¹` criterion used is the
generic `Work.MB.integrable_of_bdd_of_support`).

The proof is the one already used, at a fixed arity, inside
`Submission/Work/BoseBoxFock/pairDecompPairSetGen.lean` (`boxSlotSum_rankOnePair_loc`, a `private`
lemma of that module) and is re-derived here in the target's own module.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The coordinate vectors

`η_{evec l} = e_l` and `(|w⟩⟨v|) (evec l') = w · v_{l'}`. -/

private lemma etaOf_evec {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The sum defining `η_v` at a coordinate vector: `Σ_k v_k (evec l')_k = v_{l'}`. -/
private lemma sum_evec_mul {m : ℕ} (v : Fin m → ℝ) (l' : Fin m) :
    (∑ k : Fin m, v k * (Work.BoseB4.evec m l' k)) = v l' := by
  rw [Finset.sum_eq_single l']
  · simp [Work.BoseB4.evec]
  · intro b _ hb
    simp [Work.BoseB4.evec, Pi.single_eq_of_ne, hb]
  · intro h; exact absurd (Finset.mem_univ l') h

/-- `(|w⟩⟨v| (evec l'))_l = w_l v_{l'}`. -/
private lemma rankOnePair_evec {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  simp only [rankOnePair_apply, Pi.smul_apply, smul_eq_mul, sum_evec_mul]
  ring

/-! ## 2. The `j`-th slot expands in the coordinate basis

The only analytic input is that each mode slot is `L¹` at the weak bundle. -/

/-- The change of variable `z ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_fixed {d : ℕ} (x : Xn d) (j : Fin d) :
    Measurable (fun z : Ω => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-- **The slot integrand is integrable at the weak bundle.** -/
private lemma integrable_slotIntegrand {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (x : Xn d) (j : Fin d) (l : Fin m) :
    Integrable (fun z : Ω => (starRingEnd ℂ) (e l z) * Θ (Function.update x j z)) := by
  obtain ⟨C, hC⟩ := hbdd l
  obtain ⟨C', hC'⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max C 0 * max C' 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    ((Complex.continuous_conj.measurable.comp (hmeas l)).mul
      (hΘm.comp (measurable_update_fixed x j))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [hz0]

/-- The inner integral of the superposed slot is the finite sum of the mode slots:
`∫ z, conj (η_v z) · Θ (x[j ↦ z]) = Σ_{l'} v_{l'} ∫ z, conj (e_{l'} z) · Θ (x[j ↦ z])`. -/
private lemma slotIntegral_etaOf_eq_sum {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) (j : Fin d) (x : Xn d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z))
      = ∑ l' : Fin m, (v l' : ℂ) *
          ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  have key : (fun z : Ω => (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z))
      = fun z : Ω => ∑ l' : Fin m,
          (v l' : ℂ) * ((starRingEnd ℂ) (e l' z) * Θ (Function.update x j z)) := by
    funext z
    simp only [etaOf, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [key, integral_finsetSum _
    (fun l' _ => (integrable_slotIntegrand hmeas hbdd hsupp hΘm hΘb x j l').const_mul _)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- **A single slot expands in the coordinate basis** (weak bundle):
`boxSlotOf e w v j Θ = Σ_l Σ_{l'} (w_l v_{l'}) • boxSlotOf e (evec l) (evec l') j Θ`. -/
private lemma boxSlotOf_expand {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (Θ : Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  funext x
  have hI := slotIntegral_etaOf_eq_sum hmeas hbdd hsupp v j x Θ hΘm hΘb
  have hL : boxSlotOf e w v j Θ x
      = (∑ i : Fin m, (w i : ℂ) * e i (x j)) *
          ∑ b : Fin m, (v b : ℂ) *
            ∫ z : Ω, (starRingEnd ℂ) (e b z) * Θ (Function.update x j z) := by
    rw [show boxSlotOf e w v j Θ x
        = etaOf e w (x j) * ∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) *
            Θ (Function.update x j z) from rfl]
    rw [hI]
    simp only [etaOf]
  have hR : (∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
      boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) x
      = ∑ a : Fin m, ∑ b : Fin m, ((w a : ℂ) * (v b : ℂ)) *
          (e a (x j) * ∫ z : Ω, (starRingEnd ℂ) (e b z) *
            Θ (Function.update x j z)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, boxSlotOf, etaOf_evec, Complex.real_smul,
      Complex.ofReal_mul]
  rw [hL, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-! ## 3. The target -/

theorem boxSlotSum_rankOnePairGen {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Θ : Work.BoseDict.Xn d → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w v) Θ
      = ∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ := by
  have hexp : ∀ j : Fin d, boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ :=
    fun j => boxSlotOf_expand hmeas hbdd hsupp w v j Θ hΘm hΘb
  simp only [boxSlotSum, rankOnePair_evec, hexp]

end Work.BoseBoxFock
