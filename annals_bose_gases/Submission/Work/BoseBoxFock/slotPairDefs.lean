import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.SMul
import Submission.Work.BoseBoxFock.boxTwinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotPairDefs` — the **slot-form** box twins of the pair rows of `H2ndF`

`Work.BoseBoxFock.boxTwinDefs` realises the pair rows of `H2ndF` (the four-letter ladder words
`creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`) by the *ladder* box word
`Work.BoseBoxFock.bW4 = boxCreOf w₁ ∘ boxCreOf w₂ ∘ boxAnnOf v₁ ∘ boxAnnOf v₂`.

That realisation is **not sector-local**: `boxCreOf` symmetrises, so `bW4` does not commute with
the slot-sector projections `slotExact e S` of the BF3c selection
(`FINDING_BF3c_dict_s12.md` §5).  The proved selection layer therefore cannot be run with `bW4`,
and the repair is to realise the pair rows in **first-quantised slot form**, which *is* sector
local (each single-slot operator `boxSlotOf e w v j` commutes with every `slotExact e S`).

This module supplies the vocabulary of that repair:

* `rankOnePair w v = |w⟩⟨v| : x ↦ (Σ_l v_l x_l) • w`, the general rank-one one-body operator
  (`Work.BoseBoxFock.rankOne v` is the case `w = v`);
* `dGamma_rankOnePair` — the bridge `dGamma m (|w⟩⟨v|) = creOf m w ∘ annOf m v`
  (the general-mode version of the proved `Work.BoseB4.creOf_annOf_eq_dGamma`);
* `bW4slot e w₁ w₂ v₁ v₂ d` — the slot-form twin of the four-letter word, namely
  `boxSlotSum e (|w₁⟩⟨v₁|) ∘ boxSlotSum e (|w₂⟩⟨v₂|) − boxSlotSum e (|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|)`.

The mathematical content of the last definition is the *operator* identity (valid on all box
states, from the definition `boxSlotSum e T = Σ_j T^{(j)}` of the first quantisation)

    `Σ_{p ∈ pairSet} (|w₁⟩⟨v₁|)^{(p.1)} (|w₂⟩⟨v₂|)^{(p.2)}
        = boxSlotSum e T₁ ∘ boxSlotSum e T₂ − boxSlotSum e (T₁ ∘ T₂)`,

which on the **symmetric** states (the physical ones) collapses, by the box CCR, to the ladder
word `bW4` (`Work.BoseB4.AnnOf_creOf_ccr` is the model twin of that step).  The two facts make the
slot form the correct box twin for the selection: sector-local *and* equal to `bW4` where it must
be (so the analytic row inequalities, stated in ladder form, still apply).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ}

/-! ## 1. The general rank-one one-body operator -/

/-- The rank-one one-body operator `|w⟩⟨v| : x ↦ (Σ_l v_l x_l) • w`. -/
noncomputable def rankOnePair {m : ℕ} (w v : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  (∑ l : Fin m, v l • LinearMap.proj l).smulRight w

/-- Evaluation of `rankOnePair`. -/
theorem rankOnePair_apply {m : ℕ} (w v x : Fin m → ℝ) :
    rankOnePair w v x = (∑ l : Fin m, v l * x l) • w := by
  simp only [rankOnePair, LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

/-- `rankOne` is the diagonal case of `rankOnePair`. -/
theorem rankOne_eq_rankOnePair {m : ℕ} (v : Fin m → ℝ) :
    rankOne v = rankOnePair (m := m) v v := rfl

/-- **The composition of two rank-one operators is a scalar multiple of a rank-one operator.** -/
theorem rankOnePair_comp {m : ℕ} (w₁ w₂ v₁ v₂ : Fin m → ℝ) :
    (rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)
      = (∑ l : Fin m, v₁ l * w₂ l) • rankOnePair w₁ v₂ := by
  refine LinearMap.ext fun x => ?_
  funext i
  simp only [LinearMap.comp_apply, rankOnePair_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  have hsum : (∑ l : Fin m, v₁ l * ((∑ l', v₂ l' * x l') * w₂ l))
      = (∑ l : Fin m, v₁ l * w₂ l) * (∑ l', v₂ l' * x l') := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hsum]
  ring

/-! ## 2. The `dGamma` bridge in general modes -/

/-- **The general rank-one bridge**: the second quantisation of `|w⟩⟨v|` is the two-letter ladder
word `creOf w ∘ annOf v`.  This is `Work.BoseB4.creOf_annOf_eq_dGamma` in the vocabulary of
`rankOnePair`. -/
theorem dGamma_rankOnePair {m : ℕ} (w v : Fin m → ℝ) :
    Work.BoseB4.dGamma m (rankOnePair w v)
      = (Work.BoseB4.creOf m w).comp (Work.BoseB4.annOf m v) :=
  (Work.BoseB4.creOf_annOf_eq_dGamma w v).symm

/-! ## 3. The slot-form twin of the four-letter word -/

/-- **The slot-form twin of the four-letter ladder word**
`creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`, on degree-`(d+2)` box states:

    `bW4slot e w₁ w₂ v₁ v₂ d = boxSlotSum e (|w₁⟩⟨v₁|) ∘ boxSlotSum e (|w₂⟩⟨v₂|)
                                 − boxSlotSum e (|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|)`.

This is a *composition of first-quantised slot sums*, hence sector-local for the BF3c selection
(unlike the ladder word `Work.BoseBoxFock.bW4`), while on symmetric states it agrees with `bW4`
(both equal `Σ_{i≠j} (|w₁⟩⟨v₁|)^{(i)} (|w₂⟩⟨v₂|)^{(j)}`). -/
noncomputable def bW4slot {m : ℕ} (e : Fin m → Sp → ℂ) (w₁ w₂ v₁ v₂ : Fin m → ℝ) (d : ℕ) :
    (Xn (d + 2) → ℂ) → (Xn (d + 2) → ℂ) :=
  (fun Θ => Work.BoseDict.boxSlotSum e (rankOnePair w₁ v₁)
      (Work.BoseDict.boxSlotSum e (rankOnePair w₂ v₂) Θ))
    - (fun Θ => Work.BoseDict.boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ)

/-- The evaluation form of `bW4slot`. -/
theorem bW4slot_apply {m : ℕ} (e : Fin m → Sp → ℂ) (w₁ w₂ v₁ v₂ : Fin m → ℝ) (d : ℕ)
    (Θ : Xn (d + 2) → ℂ) :
    bW4slot e w₁ w₂ v₁ v₂ d Θ
      = Work.BoseDict.boxSlotSum e (rankOnePair w₁ v₁)
          (Work.BoseDict.boxSlotSum e (rankOnePair w₂ v₂) Θ)
        - Work.BoseDict.boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ := by
  rfl

end Work.BoseBoxFock
