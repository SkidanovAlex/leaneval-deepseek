import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.integrable_termOf` — integrability of the `j`-th slot of a rank-one word

The dictionary writes the box's rank-one word `|η_w⟩⟨η_v|` as a sum over the slots
`j : Fin (d+1)` of the first-quantised operators `boxSlotOf e w v j`.  To integrate such a
term against a box state one must know that the *integrand* is integrable, and the natural
hypothesis available is the integrability of the **`0`-slot** version, in which the hole sits
in the first coordinate (`Fin.cons p.1 p.2`) and the remaining `d` coordinates are the
compressed variables `p.2`.

This lemma transfers that hypothesis to an arbitrary slot `j`: the map

    Φ : Sp × Xn d → Xn (d+1),   p ↦ Fin.insertNth j p.1 p.2

(which is `Submission.BoseGases.kcInsN`, hence a measure-preserving measurable equivalence,
`Submission.BoseGases.kc_mp_insN`) realises `Xn (d+1)` as a product with the `j`-th
coordinate exposed, and the remaining coordinates `x ∘ j.succAbove` are exactly `p.2`.
The only difference between the two integrands is therefore the replacement of
`Fin.cons p.1 p.2` by `Fin.insertNth j p.1 p.2` inside a **symmetric** `Θ`; those two
functions are related by the coordinate permutation `i ↦` (`0 ↦ j`, `succ i ↦ j.succAbove i`)
— this is the permutation `permConsSuccAbove` of `Work.BoseDict.boxCreOf_boxAnnOf_slot` —
so `hΘsym` identifies the two values.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option linter.unusedVariables false

/-! ## 1. The coordinate permutation `0 ↦ j`, `i+1 ↦ j.succAbove i` -/

/-- The coordinate map `0 ↦ j`, `i+1 ↦ succAbove j i` on `Fin (n+1)`. -/
private def consShiftFun (n : ℕ) (j : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) :=
  (Fin.cons j (Fin.succAbove j) : Fin (n + 1) → Fin (n + 1))

private lemma inj_consShiftFun (n : ℕ) (j : Fin (n + 1)) :
    Function.Injective (consShiftFun n j) := by
  rw [consShiftFun, Fin.cons_injective_iff]
  exact ⟨fun ⟨i, hi⟩ => Fin.succAbove_ne j i hi, Fin.succAbove_right_injective⟩

/-- The permutation of `Fin (n+1)` sending `0` to `j` and `i+1` to `succAbove j i`. -/
private noncomputable def permConsSuccAbove (n : ℕ) (j : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (consShiftFun n j) ⟨inj_consShiftFun n j,
    Finite.injective_iff_surjective.mp (inj_consShiftFun n j)⟩

private lemma permConsSuccAbove_apply (n : ℕ) (j k : Fin (n + 1)) :
    permConsSuccAbove n j k = consShiftFun n j k := rfl

/-! ## 2. Integrability transfers along the coordinate insertion -/

/-- Integrability transfers along the measure-preserving coordinate insertion
`p ↦ Fin.insertNth j p.1 p.2` (realised as `Submission.BoseGases.kcInsN`). -/
private lemma integrable_comp_kcInsN {d : ℕ} (j : Fin (d + 1)) {f : Xn (d + 1) → ℂ}
    (hf : Integrable (fun p : Sp × Xn d => f (⇑(Submission.BoseGases.kcInsN d j) p))) :
    Integrable f :=
  ((Submission.BoseGases.kc_mp_insN d j).integrable_comp_emb
    (Submission.BoseGases.kcInsN d j).measurableEmbedding).mp hf

/-! ## 3. The lemma -/

theorem integrable_termOf {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ) (j : Fin (d + 1))
    (Θ : Work.BoseDict.Xn (d + 1) → ℂ) (Θ' : Work.BoseDict.Xn d → ℂ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)), Θ (x ∘ σ) = Θ x)
    (hInt : MeasureTheory.Integrable (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d =>
      Work.BoseDict.etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2)) :
    MeasureTheory.Integrable (fun x : Work.BoseDict.Xn (d + 1) =>
      (starRingEnd ℂ) (Θ x) * (Work.BoseDict.etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i)))) := by
  classical
  -- `Θ (cons z y) = Θ (insertNth j z y)`: the two tuples differ by a coordinate permutation.
  have hΘcons : ∀ (z : Sp) (y : Xn d),
      Θ (Fin.cons z y) = Θ (⇑(Submission.BoseGases.kcInsN d j) (z, y)) := by
    intro z y
    have h1 : Fin.cons z y
        = (⇑(Submission.BoseGases.kcInsN d j) (z, y)) ∘ (permConsSuccAbove d j) := by
      funext k
      rw [Function.comp_apply, permConsSuccAbove_apply, consShiftFun]
      cases k using Fin.cases with
      | zero => simp [Submission.BoseGases.kc_insN_apply_same]
      | succ i => simp [Submission.BoseGases.kc_insN_apply_succ]
    rw [h1, hΘsym (permConsSuccAbove d j) (⇑(Submission.BoseGases.kcInsN d j) (z, y))]
  -- Pull the hypothesis integrand back along `kcInsN`; only `Θ (cons …)` vs
  -- `Θ (insertNth …)` and the exposed coordinate `p.1`/`p.2` differ.
  have hpull : Integrable (fun p : Sp × Xn d =>
      (starRingEnd ℂ) (Θ (⇑(Submission.BoseGases.kcInsN d j) p)) *
        (etaOf e w ((⇑(Submission.BoseGases.kcInsN d j) p) j) *
          Θ' (fun i : Fin d => (⇑(Submission.BoseGases.kcInsN d j) p) (Fin.succAbove j i)))) := by
    refine hInt.congr (Filter.Eventually.of_forall fun p => ?_)
    show etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2
      = (starRingEnd ℂ) (Θ (⇑(Submission.BoseGases.kcInsN d j) p)) *
        (etaOf e w ((⇑(Submission.BoseGases.kcInsN d j) p) j) *
          Θ' (fun i : Fin d => (⇑(Submission.BoseGases.kcInsN d j) p) (Fin.succAbove j i)))
    have htail : (fun i : Fin d =>
        (⇑(Submission.BoseGases.kcInsN d j) (p.1, p.2)) (Fin.succAbove j i)) = p.2 := by
      funext i
      exact Submission.BoseGases.kc_insN_apply_succ d j p.1 p.2 i
    rw [hΘcons p.1 p.2, htail, Submission.BoseGases.kc_insN_apply_same]
    ring
  exact integrable_comp_kcInsN j hpull

end Work.BoseDict
