import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_chiMode_eq
import Submission.Work.BoseBoxFock.chiRowDefs
import Submission.Work.BoseBoxFock.chiRow_constPart_vanish
import Submission.Work.BoseBoxFock.chiTail_bound
import Submission.Work.BoseBoxFock.pin_e0_eq
import Submission.Work.BoseBoxFock.potChiLin_eq_summed_good
import Submission.Work.BoseBoxFock.potTruncRepair
import Submission.Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing
import Submission.Work.BoseBoxFock.thetaTail_bound
import Submission.Work.BoseBoxFock.wLoc_fibre_kernelCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_slotSum_expand_weak`

The slot-form expansion of the rank-one one-body operator `T = |w⟩⟨v| = rankOnePair w v` at the
**measurable/bounded** ("weak") mode bundle used throughout the box ↔ model bridge: the modes
`e l` are `Measurable`, *everywhere* bounded (`∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C`) and supported in the
corpus box `Work.BoseK15.corpusBox.boxL ℓ`; the state `Θ` is measurable and everywhere bounded.
Under those hypotheses the first-quantised slot sum of `T` collapses to the elementary form

    `boxSlotSum e (rankOnePair w v) Θ = Σ_j boxSlotOf e w v j Θ`.

The proof is a pointwise computation in the coordinate basis.  Since
`boxSlotOf e w v j Θ x = η_w(x_j) · ∫_z conj (η_v z) · Θ (x[j ↦ z])` and `η_u = Σ_l u_l e_l` by
definition of `etaOf`, the identity reduces to the finite-sum expansion of the two factors
(`Finset.sum_mul_sum`).  The only analytic input is the fact that the superposition `η_v` may be
pulled **out of the Bochner integral**: the slot integrand `z ↦ conj (e l z) · Θ (x[j ↦ z])` is
measurable (composition of the measurable mode with the measurable change of variable
`z ↦ Function.update x j z`), everywhere bounded, and supported in the compact box `boxL ℓ`; hence
integrable by `Work.MB.integrable_of_bdd_of_support`, and `integral_finsetSum` applies.  This is
the weak-bundle twin of the `Continuous`/`HasCompactSupport` identity
`Work.BoseBoxFock.boxSlotSum_rankOnePair`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open MeasureTheory Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Coordinate-vector reductions -/

/-- `η` at the coordinate vector `evec m l` is the mode `e l`. -/
private lemma etaOf_evec_eq {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The sum defining `η_v` at a coordinate vector: `Σ_k v_k (evec l')_k = v_{l'}`. -/
private lemma sum_evec_mul_w {m : ℕ} (v : Fin m → ℝ) (l' : Fin m) :
    (∑ k : Fin m, v k * (Work.BoseB4.evec m l' k)) = v l' := by
  rw [Finset.sum_eq_single l']
  · simp [Work.BoseB4.evec]
  · intro b _ hb
    simp [Work.BoseB4.evec, Pi.single_eq_of_ne, hb]
  · intro h; exact absurd (Finset.mem_univ l') h

/-- `(|w⟩⟨v| (evec l'))_l = w_l v_{l'}`. -/
private lemma rankOnePair_evec_eq {m : ℕ} (w v : Fin m → ℝ) (l l' : Fin m) :
    rankOnePair w v (Work.BoseB4.evec m l') l = w l * v l' := by
  rw [rankOnePair_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [sum_evec_mul_w]
  ring

/-- The slot at coordinate vectors, in the explicit form used by the expansion. -/
private lemma boxSlotOf_evec_eq {m d : ℕ} (e : Fin m → Ω → ℂ) (l l' : Fin m) (j : Fin d)
    (Θ : Xn d → ℂ) :
    boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ
      = fun x => e l (x j) * ∫ z : Ω, (starRingEnd ℂ) (e l' z) * Θ (Function.update x j z) := by
  funext x
  simp only [boxSlotOf, etaOf_evec_eq]

/-! ## 2. Integrability of the slot integrand at the weak bundle -/

/-- The change of variable `z ↦ Function.update x j z` is measurable. -/
private lemma measurable_update_slot {d : ℕ} (x : Xn d) (j : Fin d) :
    Measurable (fun z : Ω => Function.update x j z) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_apply]
    exact measurable_id
  · simp [hij]

/-- **The slot integrand is integrable at the weak bundle.**  It is measurable, it is bounded by
`max C 0 * max C_Θ 0`, and it is supported in `boxL ℓ`, which has finite measure; hence
`Work.MB.integrable_of_bdd_of_support` applies (this is the weak replacement of the
`Continuous`/`HasCompactSupport` integrability of the strong chain). -/
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
      (hΘm.comp (measurable_update_slot x j))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    simp [hz0]

/-! ## 3. The superposition `η_v` comes out of the integral -/

/-- `∫ z, conj (η_v z) · Θ (x[j ↦ z]) = Σ_{l'} v_{l'} ∫ z, conj (e_{l'} z) · Θ (x[j ↦ z])`. -/
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

/-! ## 4. Expansion of a general slot in the coordinate basis -/

/-- **A single slot expands in the coordinate basis** (weak bundle): since `η_w = Σ_l w_l e_l` and
`η_v = Σ_{l'} v_{l'} e_{l'}`, the slot `boxSlotOf e w v j` is the finite linear combination
`Σ_{l,l'} (w_l v_{l'}) • boxSlotOf e (evec l) (evec l') j` of the elementary slots. -/
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
    simp only [Finset.sum_apply, Pi.smul_apply, boxSlotOf_evec_eq, Complex.real_smul,
      Complex.ofReal_mul]
  rw [hL, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-! ## 5. The target -/

theorem chiRow_slotSum_expand_weak {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w v) Θ
      = ∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ := by
  have hexp : ∀ j : Fin d, boxSlotOf e w v j Θ
      = ∑ l : Fin m, ∑ l' : Fin m, (w l * v l') •
          boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ :=
    fun j => boxSlotOf_expand hmeas hbdd hsupp w v j Θ hΘm hΘb
  simp only [boxSlotSum, rankOnePair_evec_eq, hexp]

end Work.BoseBoxFock
