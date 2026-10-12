import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.n0ProjOpOrthAux.n0Iter_sub`

**Linearity of the slot iteration `n0Iter` in its state argument, pointwise on the analysis box.**

Both branches of the single-slot operator `n0Slot volA A b i` are *linear* in the state: the
`true` branch is the box projection `P_{B,i}` (linear because the Bochner integral is) and the
`false` branch is the pointwise difference `Ψ − P_{B,i}Ψ`.  Hence
the composed iteration `n0Iter volA A b l` is linear as well:

    n0Iter volA A b l (Φ − Ψ) x = n0Iter volA A b l Φ x − n0Iter volA A b l Ψ x,   x ∈ abox N ℓ.

The on-the-box restriction and the `GoodState` (`=` `BoxNice`: measurable and bounded on the box)
hypotheses are exactly what `boxPInd_sub` needs: the two slot pullbacks
`z ↦ Φ(x|i↦z)`, `z ↦ Ψ(x|i↦z)` must be `IntegrableOn A` for `integral_sub` to apply, and
boundedness on the box supplies that (`Work.BoseFixB1S.slotInt_of_bound`).

The proof is an induction on the slot list: at each slot the agreement lemma
`n0Iter_eq_of_eqOn_box` moves the difference *inside* the already-applied tail (the iteration reads
its argument only on the box), and the induction hypothesis is applied to the two single-slot
images, which stay in `GoodState` (`Work.BoseFixB1S.goodState_n0Slot`).
-/

namespace Work.n0ProjOpOrthAux

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Linearity of a single slot** in the state argument, pointwise on the analysis box: the box
projection is additive because the Bochner integral is (`Work.BoseFixB1S.boxPInd_sub`), and the
complement branch is the pointwise difference. -/
theorem n0Slot_sub {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (b : Fin N → Bool) (i : Fin N)
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.n0Slot volA A b i (Φ - Ψ) x
        = Work.BoseFixB1S.n0Slot volA A b i Φ x - Work.BoseFixB1S.n0Slot volA A b i Ψ x := by
  intro x hx
  obtain ⟨hmΦ, CΦ, hCΦ⟩ := hΦ
  obtain ⟨hmΨ, CΨ, hCΨ⟩ := hΨ
  have hIΦ := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hmΦ hCΦ
  have hIΨ := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hmΨ hCΨ
  by_cases h : b i = true
  · rw [Work.BoseFixB1S.n0Slot_apply_true volA A b i (Φ - Ψ) h x,
      Work.BoseFixB1S.n0Slot_apply_true volA A b i Φ h x,
      Work.BoseFixB1S.n0Slot_apply_true volA A b i Ψ h x]
    exact Work.BoseFixB1S.boxPInd_sub volA A i x hIΦ hIΨ
  · rw [Work.BoseFixB1S.n0Slot_apply_false volA A b i (Φ - Ψ) (by simpa using h) x,
      Work.BoseFixB1S.n0Slot_apply_false volA A b i Φ (by simpa using h) x,
      Work.BoseFixB1S.n0Slot_apply_false volA A b i Ψ (by simpa using h) x]
    rw [Work.BoseFixB1S.boxPInd_sub volA A i x hIΦ hIΨ]
    simp only [Pi.sub_apply]
    ring

theorem n0Iter_sub {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (b : Fin N → Bool) (l : List (Fin N)) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.n0Iter volA A b l (Φ - Ψ) x
        = Work.BoseFixB1S.n0Iter volA A b l Φ x - Work.BoseFixB1S.n0Iter volA A b l Ψ x := by
  induction l generalizing Φ Ψ with
  | nil => intro x _; rfl
  | cons i l ih =>
    intro x hx
    rw [Work.BoseFixB1S.n0Iter_cons volA A b i l (Φ - Ψ),
      Work.BoseFixB1S.n0Iter_cons volA A b i l Φ,
      Work.BoseFixB1S.n0Iter_cons volA A b i l Ψ]
    rw [Work.BoseFixB1S.n0Iter_eq_of_eqOn_box hA hAc b
      (f := Work.BoseFixB1S.n0Slot volA A b i (Φ - Ψ))
      (g := Work.BoseFixB1S.n0Slot volA A b i Φ - Work.BoseFixB1S.n0Slot volA A b i Ψ)
      (fun y hy => by
        rw [n0Slot_sub hℓ hA hAc b i hΦ hΨ y hy]
        rfl) l x hx]
    exact ih (Work.BoseFixB1S.goodState_n0Slot hℓ hvol hA hvolA hAc b i hΦ)
      (Work.BoseFixB1S.goodState_n0Slot hℓ hvol hA hvolA hAc b i hΨ) x hx

end Work.n0ProjOpOrthAux
