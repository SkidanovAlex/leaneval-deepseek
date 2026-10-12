import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
import Submission.Work.PerSector.FibreResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.fibre_defs_v3` — the slot/fibre vocabulary of the C3 fibre bound

This file fixes the vocabulary in which the sector (fibre) decomposition of the localised box
form `Work.BoseKinLoc.boxForm` is stated.  The slot framework itself (the measurable
equivalence `Work.PerSector.slotME : X N ≃ᵐ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)`, the
reassembly `Work.PerSector.slotComb`, the slot sets `Work.PerSector.slotSet B S` and the fibre
`Work.PerSector.slotFibre S Φ y`) is the one built in `Submission.Work.PerSector`; here we only

* fix a **canonical** bijection `slotIso S : SlotIn N S ≃ Fin S.card`, namely the *order
  isomorphism* `Finset.orderIsoOfFin S rfl`.  Order preservation is what makes the pair sum of
  `potWordU` (`∑_{i<j} …`, an *oriented* sum over unordered pairs) match the pair sum of the
  `|S|`-particle word the fibre carries: under an order isomorphism the pairs `i < j` of
  `Fin S.card` correspond exactly to the pairs `s < t` of the slots of `S`;
* name the **fibre state** `fibState S Ψ y : X S.card → ℝ` (the `|S|`-particle function obtained
  by freezing the coordinates outside `S` at `y`), the object that `hEi`'s box Rayleigh
  quotients are applied to, and the **fibre sum** `fibreSum`, the object that the target's
  assembly compares with `boxForm`.

Nothing is proved here beyond the elementary facts about `slotIso`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **canonical order isomorphism** between the slots of `S` and `Fin |S|`; its inverse is
the `i`-th smallest slot of `S`. -/
noncomputable def slotIso {N : ℕ} (S : Finset (Fin N)) : Work.PerSector.SlotIn N S ≃ Fin S.card :=
  (Finset.orderIsoOfFin S rfl).symm

/-- `slotIso` is order preserving (in the direction `Fin |S| → slots of S`). -/
theorem slotIso_symm_lt {N : ℕ} {S : Finset (Fin N)} {i j : Fin S.card}
    (hij : i < j) : ((slotIso S).symm i).1 < ((slotIso S).symm j).1 :=
  (Finset.orderIsoOfFin S rfl).lt_iff_lt.mpr hij

/-- **The fibre state**: the `|S|`-particle state obtained from `Ψ` by freezing the coordinates
outside `S` at the configuration `y` and re-indexing the slots of `S` by `Fin |S|` along
`slotIso S`. -/
noncomputable def fibState {N : ℕ} (S : Finset (Fin N)) (Ψ : Submission.BoseGases.X N → ℝ)
    (y : Work.PerSector.SlotOut N S → ℝ³) : Submission.BoseGases.X S.card → ℝ :=
  Work.PerSector.slotFibreState S (slotIso S) Ψ y

theorem fibState_apply {N : ℕ} (S : Finset (Fin N)) (Ψ : Submission.BoseGases.X N → ℝ)
    (y : Work.PerSector.SlotOut N S → ℝ³) (x : Submission.BoseGases.X S.card) :
    fibState S Ψ y x = Ψ (Work.PerSector.slotComb S (fun i : Work.PerSector.SlotIn N S =>
      x (slotIso S i)) y) := rfl

/-- The fibre state of a smooth state is smooth. -/
theorem contDiff_fibState {N : ℕ} (S : Finset (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (y : Work.PerSector.SlotOut N S → ℝ³) :
    ContDiff ℝ (⊤ : ENat) (fibState S Ψ y) :=
  Work.PerSector.contDiff_slotFibreState S (slotIso S) hΨ y

/-- **The fibre sum**: for a state `Ψ` on `X N` and the box `acube ℓ`, the sum over the slot sets
`S` of the `boxFormB` of the corresponding fibre state, integrated over the outside
configurations.  This is the object that the sector decomposition of `boxForm` produces. -/
noncomputable def fibreSum {N : ℕ} (v g : ℝ³ → ℝ) (ℓ L μ d s εT b : ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N),
    ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
      Work.BoseKinLoc.boxFormB S.card v g ℓ μ d s εT b (fibState S Ψ y)

/-- **The fibre norm sum**: the same sum with the *box norm* `sqNormB` in place of the box form.
It is (by the sector decomposition of the squared norm) the total squared norm `∫ Ψ²`. -/
noncomputable def fibreNorm {N : ℕ} (ℓ L : ℝ) (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N),
    ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)

/-- **The fibre sum with a general support box `A`**: same as `fibreSum` but with the outside
configurations ranging over `A ∩ (acube ℓ)ᶜ` instead of `acube (max L ℓ) ∩ (acube ℓ)ᶜ`.  This is
the form needed when the state is supported in a *translated* box `c +ᵥ abox N L`: the translation
covariance `word_translate` moves the anchor of `boxForm` to `0` but moves the support of the state
to `(-ℓu) +ᵥ abox N L`, and the outside configurations of the fibres then range over the
correspondingly translated ambient box. -/
noncomputable def fibreSumA {N : ℕ} (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (A : Set ℝ³)
    (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N),
    ∫ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
      Work.BoseKinLoc.boxFormB S.card v g ℓ μ d s εT b (fibState S Ψ y)

/-- **The fibre norm sum with a general support box `A`**. -/
noncomputable def fibreNormA {N : ℕ} (ℓ : ℝ) (A : Set ℝ³)
    (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N),
    ∫ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (A ∩ (Submission.BoseGases.acube ℓ)ᶜ),
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)

end Work.BoseKinLoc.Sector
