import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.integral_sliceRestore`

The slice/Fubini identity for the configuration space `Xn n = Fin n → Sp`: for an integrable
`F : Xn n → E` and any slot `j : Fin n`,

    ∫ x, F x = ∫ ŷ : ({i // i ≠ j} → Sp), ∫ a : Sp, F (sliceRestore j a ŷ) .

**Proof.**  Write `n = m + 1`.  The coordinate `j` is split off by the measure preserving
equivalence `MeasurableEquiv.piFinSuccAbove` (`Xn (m+1) ≃ᵐ Sp × Xn m`), the remaining `m`
coordinates are relabelled by `MeasurableEquiv.piCongrLeft` along the canonical bijection
`Fin m ≃ {i : Fin (m+1) // i ≠ j}` (`finSuccAboveEquiv`), and the two `Sp`-valued factors are
swapped by `MeasurableEquiv.prodComm`.  The composite

    sliceEquiv j : Xn (m+1) ≃ᵐ ({i // i ≠ j} → Sp) × Sp

is measure preserving (`volume_preserving_sliceEquiv`), satisfies
`(sliceEquiv j).symm (ŷ, a) = sliceRestore j a ŷ` (`sliceEquiv_symm_apply`), and the change of
variables `MeasurePreserving.integral_comp` followed by the product Fubini theorem
`MeasureTheory.integral_prod` gives the identity.  The integrability needed for Fubini is
transported along the equivalence with `MeasurePreserving.integrable_comp_emb`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false

/-- **The slicing equivalence in the forward direction**: the configuration of `Fin (m+1)` slots
is written as the pair consisting of its `{i // i ≠ j}`-part (relabelled as a function on `Fin m`
by `finSuccAboveEquiv`) and its `j`-th coordinate.

Explicitly, on the slice `sliceRestore j a ŷ` this map is `ŷ ↦ (ŷ, a)`
(`sliceEquiv_apply_sliceRestore`), and its inverse is `(ŷ, a) ↦ sliceRestore j a ŷ`
(`sliceEquiv_symm_apply`). -/
def sliceEquiv {m : ℕ} (j : Fin (m + 1)) :
    Work.BoseDict.Xn (m + 1) ≃ᵐ
      ({i : Fin (m + 1) // i ≠ j} → Work.BoseDict.Sp) × Work.BoseDict.Sp :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Work.BoseDict.Sp) j).trans
    ((MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piCongrLeft
          (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp)
          (finSuccAboveEquiv j))
        (MeasurableEquiv.refl Work.BoseDict.Sp)))

/-- `sliceEquiv` composed with `sliceRestore` is the identity pairing: the slice with `a` in slot
`j` is sent back to the pair `(ŷ, a)`. -/
theorem sliceEquiv_apply_sliceRestore {m : ℕ} (j : Fin (m + 1)) (a : Work.BoseDict.Sp)
    (ŷ : {i : Fin (m + 1) // i ≠ j} → Work.BoseDict.Sp) :
    sliceEquiv j (sliceRestore j a ŷ) = (ŷ, a) := by
  have h₁ : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Work.BoseDict.Sp) j)
      (sliceRestore j a ŷ) = (a, fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩) := by
    rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    refine Prod.ext ?_ ?_
    · simp [sliceRestore]
    · funext k
      simp [Fin.removeNth_apply, sliceRestore, Fin.succAbove_ne]
  rw [sliceEquiv, MeasurableEquiv.trans_apply, h₁, MeasurableEquiv.trans_apply]
  have hswap : (MeasurableEquiv.prodComm : Work.BoseDict.Sp × Work.BoseDict.Xn m ≃ᵐ
      Work.BoseDict.Xn m × Work.BoseDict.Sp)
      (a, (fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩))
      = ((fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩), a) := rfl
  rw [hswap]
  have hpc : (MeasurableEquiv.piCongrLeft
      (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp) (finSuccAboveEquiv j))
      (fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩) = ŷ := by
    funext i
    rw [← (finSuccAboveEquiv j).apply_symm_apply i, MeasurableEquiv.piCongrLeft_apply_apply]
    have h : (⟨j.succAbove ((finSuccAboveEquiv j).symm i), j.succAbove_ne _⟩ :
        {i : Fin (m + 1) // i ≠ j}) = i := by
      rw [← finSuccAboveEquiv_apply j ((finSuccAboveEquiv j).symm i), Equiv.apply_symm_apply]
    rw [h, Equiv.apply_symm_apply]
  rw [show (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp)
          (finSuccAboveEquiv j))
        (MeasurableEquiv.refl Work.BoseDict.Sp))
      ((fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩), a)
      = ((MeasurableEquiv.piCongrLeft (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp)
            (finSuccAboveEquiv j)) (fun k : Fin m => ŷ ⟨j.succAbove k, j.succAbove_ne k⟩), a)
        from rfl,
    hpc]

/-- **The inverse of the slicing equivalence** is `sliceRestore`. -/
theorem sliceEquiv_symm_apply {m : ℕ} (j : Fin (m + 1)) (a : Work.BoseDict.Sp)
    (ŷ : {i : Fin (m + 1) // i ≠ j} → Work.BoseDict.Sp) :
    (sliceEquiv j).symm (ŷ, a) = sliceRestore j a ŷ := by
  rw [← sliceEquiv_apply_sliceRestore j a ŷ, MeasurableEquiv.symm_apply_apply]

/-- The slicing equivalence is measure preserving for the product measures. -/
theorem volume_preserving_sliceEquiv {m : ℕ} (j : Fin (m + 1)) :
    MeasureTheory.MeasurePreserving (⇑(sliceEquiv j)) := by
  have h₁ : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Work.BoseDict.Sp) j)) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Work.BoseDict.Sp) j
  have h₂a : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.prodComm : Work.BoseDict.Sp × Work.BoseDict.Xn m ≃ᵐ
        Work.BoseDict.Xn m × Work.BoseDict.Sp)) :=
    Measure.measurePreserving_swap
  have h₂b : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr
        (MeasurableEquiv.piCongrLeft
          (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp) (finSuccAboveEquiv j))
        (MeasurableEquiv.refl Work.BoseDict.Sp))) := by
    refine MeasureTheory.MeasurePreserving.congr
      (f := Prod.map (⇑(MeasurableEquiv.piCongrLeft
        (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp)
          (finSuccAboveEquiv j))) id) ?_ ?_ ?_
    · exact (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp) (finSuccAboveEquiv j)).prod
        (MeasureTheory.MeasurePreserving.id volume)
    · exact (MeasurableEquiv.prodCongr _ _).measurable
    · exact Filter.EventuallyEq.of_eq (funext fun p => by ext <;> rfl)
  have h₂ : MeasureTheory.MeasurePreserving
      (⇑((MeasurableEquiv.prodComm).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.piCongrLeft
            (fun _ : {i : Fin (m + 1) // i ≠ j} => Work.BoseDict.Sp) (finSuccAboveEquiv j))
          (MeasurableEquiv.refl Work.BoseDict.Sp)))) := h₂a.trans h₂b
  rw [sliceEquiv]
  exact h₁.trans h₂

theorem integral_sliceRestore {n : ℕ} (j : Fin n) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Work.BoseDict.Xn n → E} (hF : MeasureTheory.Integrable F) :
    ∫ x : Work.BoseDict.Xn n, F x
      = ∫ ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp), ∫ a : Work.BoseDict.Sp,
          F (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ) := by
  match n with
  | 0 => exact Fin.elim0 j
  | m + 1 =>
    have hmp := volume_preserving_sliceEquiv (m := m) j
    let g : ({i : Fin (m + 1) // i ≠ j} → Work.BoseDict.Sp) × Work.BoseDict.Sp → E :=
      fun p => F ((sliceEquiv (m := m) j).symm p)
    -- integrability of the transported integrand, needed for Fubini
    have hg : MeasureTheory.Integrable g (volume.prod volume) := by
      have h := hmp.integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding (sliceEquiv (m := m) j)) (g := g)
      refine h.mp ?_
      show MeasureTheory.Integrable
        (fun x => F ((sliceEquiv (m := m) j).symm ((sliceEquiv (m := m) j) x))) volume
      rw [show (fun x : Work.BoseDict.Xn (m + 1) =>
          F ((sliceEquiv (m := m) j).symm ((sliceEquiv (m := m) j) x))) = F from
        funext fun x => by rw [MeasurableEquiv.symm_apply_apply]]
      exact hF
    -- the change of variables along `sliceEquiv`
    have hcomp := hmp.integral_comp
      (MeasurableEquiv.measurableEmbedding (sliceEquiv (m := m) j)) g
    rw [show (fun x : Work.BoseDict.Xn (m + 1) => g ((sliceEquiv (m := m) j) x)) = F from
      funext fun x => by
        show F ((sliceEquiv (m := m) j).symm ((sliceEquiv (m := m) j) x)) = F x
        rw [MeasurableEquiv.symm_apply_apply]] at hcomp
    -- Fubini on the product `({i // i ≠ j} → Sp) × Sp`, then the identification of the slice
    rw [hcomp, Measure.volume_eq_prod, MeasureTheory.integral_prod g hg]
    congr 1 with ŷ
    refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
    funext a
    show g (ŷ, a) = F (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ)
    rw [show g (ŷ, a) = F ((sliceEquiv (m := m) j).symm (ŷ, a)) from rfl, sliceEquiv_symm_apply]

end Work.BoseBoxFock.PotCubicLowBandAux
