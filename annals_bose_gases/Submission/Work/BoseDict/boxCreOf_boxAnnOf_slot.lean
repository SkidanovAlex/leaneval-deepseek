import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxCreOf_boxAnnOf_slot` — second quantisation vs first quantisation

For a symmetric `(d+1)`-particle function `Θ`, the composite `boxCreOf ∘ boxAnnOf`
(the box's second-quantised rank-one operator `η_w ⊗ conj η_v`) equals the sum of the
first-quantised slots `Σ_j boxSlotOf e w v j Θ`.

Concretely, after unfolding the definitions the only point is that, for every `j`, the
plugged function `Fin.cons z (fun i => x (j.succAbove i))` (the hole coordinate `z` put in
slot `0`, the surviving coordinates compressed into slots `1,…,d`) is the coordinate
permutation by `σ_j := Fin.cons j (Fin.succAbove j)` (the cyclic shift `0 ↦ j`,
`i+1 ↦ succAbove j i`) of `Function.update x j z` (the hole put in slot `j`).  `hΘ` then
identifies the two integrands, and the explicit normalisation constant `√(d+1)` cancels.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

/-- The coordinate map `0 ↦ j`, `i+1 ↦ succAbove j i` on `Fin (n+1)`. -/
private def consShiftFun (n : ℕ) (j : Fin (n+1)) : Fin (n+1) → Fin (n+1) :=
  (Fin.cons j (Fin.succAbove j) : Fin (n+1) → Fin (n+1))

private lemma consShiftFun_apply (n : ℕ) (j k : Fin (n+1)) :
    consShiftFun n j k = (Fin.cons j (Fin.succAbove j) : Fin (n+1) → Fin (n+1)) k := rfl

private lemma inj_consShiftFun (n : ℕ) (j : Fin (n+1)) :
    Function.Injective (consShiftFun n j) := by
  rw [consShiftFun, Fin.cons_injective_iff]
  exact ⟨fun ⟨i, hi⟩ => Fin.succAbove_ne j i hi, Fin.succAbove_right_injective⟩

/-- The permutation of `Fin (n+1)` sending `0` to `j` and `i+1` to `succAbove j i`. -/
private noncomputable def permConsSuccAbove (n : ℕ) (j : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (consShiftFun n j) ⟨inj_consShiftFun n j,
    Finite.injective_iff_surjective.mp (inj_consShiftFun n j)⟩

private lemma permConsSuccAbove_apply (n : ℕ) (j k : Fin (n+1)) :
    permConsSuccAbove n j k = consShiftFun n j k := rfl

/-- Moving the first coordinate of a tuple into slot `j` is the coordinate permutation
`permConsSuccAbove` applied to `Function.update x j z`. -/
private lemma cons_succAbove_eq_update_comp {n : ℕ} (x : Fin (n+1) → Sp) (j : Fin (n+1))
    (z : Sp) :
    Fin.cons z (fun i : Fin n => x (Fin.succAbove j i))
      = (Function.update x j z) ∘ (permConsSuccAbove n j) := by
  funext k
  rw [Function.comp_apply, permConsSuccAbove_apply, consShiftFun_apply]
  cases k using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Cancellation of the normalisation constant: `a⁻¹ * (b * (a * c)) = b * c`. -/
private lemma div_mul_mul_mul {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) :
    (1 / a) * (b * (a * c)) = b * c := by
  field_simp

theorem boxCreOf_boxAnnOf_slot {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (w v : Fin m → ℝ) (Θ : Work.BoseDict.Xn (d + 1) → ℂ)
    (hΘ : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)), Θ (x ∘ σ) = Θ x) :
    Work.BoseDict.boxCreOf e w d (Work.BoseDict.boxAnnOf e v d Θ)
      = ∑ j : Fin (d + 1), Work.BoseDict.boxSlotOf e w v j Θ := by
  have hsqne : ((Real.sqrt ((d : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero, Real.sqrt_ne_zero']
    positivity
  funext x
  simp only [boxCreOf, boxAnnOf, boxSlotOf, Finset.sum_apply]
  have hint : ∀ j : Fin (d + 1),
      (∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Θ (Fin.cons z fun i => x (j.succAbove i)))
        = ∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z) := by
    intro j
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [cons_succAbove_eq_update_comp x j z, hΘ (permConsSuccAbove d j) (Function.update x j z)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hint j, div_mul_mul_mul hsqne]

end Work.BoseDict
