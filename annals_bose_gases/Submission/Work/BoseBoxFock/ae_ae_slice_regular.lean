import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceFCRealise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ae_ae_slice_regular`

The regularisation of the slice of an a.e. `L^∞` state along a sector splitting.

Given an a.e. strongly measurable and a.e. bounded function `Θ` on the full configuration space
`Fin n → Ω`, almost every complement configuration `y` gives a slice
`u ↦ Θ (pairCoord S (u ∘ S.equivFin) y)` that is again a.e. strongly measurable and a.e. bounded
(with the *same* bound `C`).

The two measure-theoretic ingredients are independent of the corpus and are stated here in full
generality:

* `ae_ae_section_aestronglyMeasurable` — a.e. sections of an a.e. strongly measurable function
  are a.e. strongly measurable (via a strongly measurable representative and the Fubini order
  swap `Measure.measurePreserving_swap` + `Measure.ae_ae_of_ae_prod`);
* `ae_ae_section_bound` — a.e. bounds pass to a.e. sections (same swap, pointwise property).

The corpus-specific part is the slot splitting: `MeasurableEquiv.piEquivPiSubtypeProd` (whose
inverse is `pairCoord`) is measure preserving (`volume_preserving_piEquivPiSubtypeProd`), and the
identification of `Fin S.card → Ω` with `↥S → Ω` through `S.equivFin` is measure preserving
(`volume_measurePreserving_piCongrLeft`).

⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a
`update_pairCoord` clash).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Sections of an a.e. strongly measurable function -/

/-- **A.e. sections of an a.e. strongly measurable function.**  If `f : α × β → γ` is a.e.
strongly measurable for the product measure `μ.prod ν`, then for almost every `y` the section
`x ↦ f (x, y)` is a.e. strongly measurable for `μ`.

Proof: a strongly measurable representative `g` of `f` has strongly measurable sections
(compose with the measurable `x ↦ (x, y)`); the a.e. equality `f =ᵐ g` on the product becomes an
a.e. (in `y`) equality of sections after swapping the two factors of the product measure
(`Measure.measurePreserving_swap`), by `Measure.ae_ae_of_ae_prod`. -/
lemma ae_ae_section_aestronglyMeasurable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace γ] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → γ} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x : α => f (x, y)) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hswap : ∀ᵐ z ∂ν.prod μ, g z.swap = f z.swap :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hfg.symm
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
  have hsec : StronglyMeasurable (fun x : α => g (x, y)) :=
    hg.comp_measurable (by fun_prop)
  exact hsec.aestronglyMeasurable.congr hy

/-- **A.e. bounds on a.e. sections.**  If `f : α × β → ℂ` is a.e. bounded by `C` for the product
measure `μ.prod ν`, then for almost every `y` the section `x ↦ f (x, y)` is a.e. bounded by `C`.

Proof: the pointwise property is transported to the swapped product `ν.prod μ`
(`Measure.measurePreserving_swap`) and then Fubini'd (`Measure.ae_ae_of_ae_prod`). -/
lemma ae_ae_section_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℂ} {C : ℝ} (hf : ∀ᵐ z ∂μ.prod ν, ‖f z‖ ≤ C) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ‖f (x, y)‖ ≤ C := by
  have h : ∀ᵐ z ∂ν.prod μ, ‖f z.swap‖ ≤ C :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hf
  exact Measure.ae_ae_of_ae_prod h

/-! ## 2. The slot splitting -/

/-- **For almost every complement configuration `y`, the slice is a.e. strongly measurable and a.e. bounded.** The slot splitting `MeasurableEquiv.piEquivPiSubtypeProd` (whose inverse is `pairCoord`, see `sliceFubiniPairCoord_symm`) is measure preserving, so an a.e. statement about `Θ` on `Fin n → Ω` pulls back to the product `(Fin S.card → Ω) × ({i // i ∉ S} → Ω)`, and `Measure.ae_ae_of_ae_prod` turns it into a statement about almost every section.
⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a `update_pairCoord` clash). -/
theorem ae_ae_slice_regular {n : ℕ} {S : Finset (Fin n)}
    {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} {C : ℝ}
    (hΘ : MeasureTheory.AEStronglyMeasurable Θ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))))
    (hC : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Fin n → EuclideanSpace ℝ (Fin 3))), ‖Θ x‖ ≤ C) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.AEStronglyMeasurable
        (fun u : Fin S.card → EuclideanSpace ℝ (Fin 3) =>
          Θ (Work.BoseBoxFock.pairCoord S (fun i => u (S.equivFin i)) y))
        (MeasureTheory.volume : MeasureTheory.Measure
          (Fin S.card → EuclideanSpace ℝ (Fin 3)))
      ∧ ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure
          (Fin S.card → EuclideanSpace ℝ (Fin 3))),
          ‖Θ (Work.BoseBoxFock.pairCoord S (fun i => u (S.equivFin i)) y)‖ ≤ C := by
  classical
  -- the slot splitting equivalence is measure preserving
  have hinst : (Finset.Subtype.fintype S : Fintype {i // i ∈ S}) =
      Subtype.fintype (fun i : Fin n => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      (volume : Measure (Fin n → Ω))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  -- its inverse is `pairCoord`
  have hsymm : ⇑((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω)
      (fun i => i ∈ S)).symm)
      = fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) => pairCoord S q.1 q.2 := by
    funext q
    obtain ⟨u, y⟩ := q
    funext i
    by_cases h : i ∈ S <;> simp [pairCoord, h]
  -- pull the two a.e. statements back to the product
  have hΘaesm : AEStronglyMeasurable
      (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) => Θ (pairCoord S q.1 q.2))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    have h := hΘ.comp_measurePreserving hmp.symm
    simpa only [Function.comp_def, hsymm] using h
  have hΘbdd : ∀ᵐ q ∂(volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))),
      ‖Θ (pairCoord S q.1 q.2)‖ ≤ C := by
    have h := hmp.symm.quasiMeasurePreserving.ae hC
    simpa only [Function.comp_def, hsymm] using h
  -- sections at almost every complement configuration
  have hsecA : ∀ᵐ y : {i // i ∉ S} → Ω,
      AEStronglyMeasurable (fun u : {i // i ∈ S} → Ω => Θ (pairCoord S u y))
        (volume : Measure ({i // i ∈ S} → Ω)) :=
    ae_ae_section_aestronglyMeasurable hΘaesm
  have hsecB : ∀ᵐ y : {i // i ∉ S} → Ω,
      ∀ᵐ u : {i // i ∈ S} → Ω, ‖Θ (pairCoord S u y)‖ ≤ C :=
    ae_ae_section_bound hΘbdd
  -- re-index the slots by `Fin S.card` along `S.equivFin`
  have hE2 : MeasurePreserving
      (fun u : Fin S.card → Ω => fun i : {i // i ∈ S} => u (S.equivFin i))
      (volume : Measure (Fin S.card → Ω)) (volume : Measure ({i // i ∈ S} → Ω)) := by
    have h := volume_measurePreserving_piCongrLeft (fun _ : {i // i ∈ S} => Ω) (S.equivFin.symm)
    convert h using 1
    funext u k
    conv_rhs => rw [← S.equivFin.symm_apply_apply k]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  filter_upwards [hsecA, hsecB] with y hyA hyB
  refine ⟨?_, ?_⟩
  · exact hyA.comp_measurePreserving hE2
  · exact hE2.quasiMeasurePreserving.ae hyB

end Work.BoseBoxFock
