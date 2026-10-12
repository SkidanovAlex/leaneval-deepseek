import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FibreWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FibreWord.SliceAE` — the slice-a.e. foundations of the fibre word

The per-fibre chapter's residual chain has to replace a state `Ψ` by an a.e.-equal state `Ψ'` in
expressions that are *integrals of slice averages*: the localised word `tBwordBInd + qLHSwordB`
depends on its state argument through

* the box projection `boxPInd volA A i Ψ x = |A|⁻¹ ∫_{z∈A} Ψ(x ←ᵢ z)` — the mean of `Ψ` over the
  line through `x` in the `i`-th coordinate direction,
* the windowed amplitude `tBamp χ p Ψ i x = ∫_z χ(z)e^{-i⟨p,z⟩} Ψ(x ←ᵢ z)`,
* the plain multiplication `Ψ x`,

and then integrates the results over the ambient box.  Every one of these is an integral over the
*single* coordinate `z` of the slice function `z ↦ Ψ(x ←ᵢ z)`, so the a.e.-invariance of the word
follows once we know that **a.e. equality of `Ψ` and `Ψ'` on the product space `X N` propagates to
the slice functions for a.e. `x`**.

That propagation is *not* a direct instance of `Measure.ae_eq_comp`, because the slice map
`Tᵢ(p) = Function.update p.1 i p.2 : X N × ℝ³ → X N` is not the coordinate projection: its
preimage of a point is a *line* in `X N`, of measure zero (for `N ≥ 2`, `Tᵢ` is not injective and
`(volume.prod volume).map Tᵢ` is not σ-finite — it is `⊤ • volume`).  What it **is**, is
quasi-measure-preserving: a null set's `Tᵢ`-preimage is null, because a null set in a product
measure has null slices for a.e. value of the dropped coordinate, and the preimage of `N` is the
union of those slices.  `qmp_update` below proves exactly that, by factoring `Tᵢ` through the
measure-preserving splitting `MeasurableEquiv.piFinSuccAbove` — which turns `Tᵢ` into the map
`((a,b),z) ↦ (z,b)`, i.e. a projection (quasi-measure-preserving) followed by a swap
(measure-preserving).

`ae_eq_slice` and `ae_eq_slice_set` are then the consequences the congruence chain consumes:
`F =ᵐ G` on `X N` gives `∫ z, F (x ←ᵢ z) =ᵐ_x ∫ z, G (x ←ᵢ z)`, and the same with the integral
restricted to an arbitrary measurable-or-not set `A ⊆ ℝ³`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FibreWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.BlockBound4
open Work.KinPSuperadd
open Work.SlotWord
open Work.SmallBoxTBWord

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1  The slice map is quasi-measure-preserving -/

/-- **The `(Fin (m+1))`-form of the slice map.**  Overwrite the `i`-th coordinate of a
configuration `x : X (m+1)` by `z`, as a map `X (m+1) × ℝ³ → X (m+1)`.  It is quasi-measure-
preserving, essentially because it is, up to the measure-preserving splitting
`MeasurableEquiv.piFinSuccAbove`, the map `((a,b),z) ↦ (z,b)` — a projection (dropping the `a`,
quasi-measure-preserving) followed by a swap (measure-preserving). -/
theorem qmp_update (m : ℕ) (i : Fin (m + 1)) :
    Measure.QuasiMeasurePreserving
      (fun p : X (m + 1) × ℝ³ => Function.update p.1 i p.2) volume volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ³) i
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ³) i
  have hS : Measure.QuasiMeasurePreserving
      (fun p : (ℝ³ × (Fin m → ℝ³)) × ℝ³ => (p.2, p.1.2)) volume volume :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).quasiMeasurePreserving.comp
      (QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
        (Measure.QuasiMeasurePreserving.id volume))
  have hT : (fun p : X (m + 1) × ℝ³ => Function.update p.1 i p.2)
      = e.symm ∘ (fun p : (ℝ³ × (Fin m → ℝ³)) × ℝ³ => (p.2, p.1.2)) ∘ Prod.map e id := by
    funext p
    obtain ⟨x, z⟩ := p
    simp only [Function.comp_apply, Prod.map, id_eq]
    have h1 : e (Function.update x i z) = (z, i.removeNth x) := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        ← Fin.insertNth_removeNth, Fin.insertNth_apply_same, Fin.removeNth_insertNth]
    have h2 : (e x).2 = i.removeNth x := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    rw [← e.symm_apply_apply (Function.update x i z), h1, h2]
  rw [hT]
  exact (he.symm.quasiMeasurePreserving).comp
    (hS.comp ((MeasurePreserving.prod he (MeasurePreserving.id volume)).quasiMeasurePreserving))

/-- **The slice map is quasi-measure-preserving** at every particle number. -/
theorem quasiMeasurePreserving_update {n : ℕ} (i : Fin n) :
    Measure.QuasiMeasurePreserving
      (fun p : X n × ℝ³ => Function.update p.1 i p.2) volume volume := by
  match n, i with
  | m + 1, i => exact qmp_update m i

/-! ## 2  The slice a.e. lemmas -/

/-- **The slice a.e. lemma.**  If two states agree `volume`-a.e. on `X n`, then their slice
functions agree a.e. in the position and in the slice variable, hence their `z`-integrals agree
a.e. in `x`. -/
theorem ae_eq_slice {n : ℕ} (i : Fin n) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : X n → E} (h : F =ᵐ[volume] G) :
    (fun x : X n => ∫ z : ℝ³, F (Function.update x i z)) =ᵐ[volume]
      (fun x : X n => ∫ z : ℝ³, G (Function.update x i z)) := by
  have hcomp : Function.uncurry (fun (x : X n) (z : ℝ³) => F (Function.update x i z))
      =ᵐ[volume] Function.uncurry (fun (x : X n) (z : ℝ³) => G (Function.update x i z)) :=
    (quasiMeasurePreserving_update i).ae_eq h
  have hae := Measure.ae_ae_eq_of_ae_eq_uncurry hcomp
  filter_upwards [hae] with x hx
  exact integral_congr_ae hx

/-- **The restricted slice a.e. lemma.**  Same as `ae_eq_slice`, for the integral over an
arbitrary set `A ⊆ ℝ³` (no measurability needed: the restriction only ever *shrinks* the a.e.
statement). -/
theorem ae_eq_slice_set {n : ℕ} (i : Fin n) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set ℝ³) {F G : X n → E} (h : F =ᵐ[volume] G) :
    (fun x : X n => ∫ z in A, F (Function.update x i z)) =ᵐ[volume]
      (fun x : X n => ∫ z in A, G (Function.update x i z)) := by
  have hcomp : Function.uncurry (fun (x : X n) (z : ℝ³) => F (Function.update x i z))
      =ᵐ[volume] Function.uncurry (fun (x : X n) (z : ℝ³) => G (Function.update x i z)) :=
    (quasiMeasurePreserving_update i).ae_eq h
  have hae := Measure.ae_ae_eq_of_ae_eq_uncurry hcomp
  filter_upwards [hae] with x hx
  exact integral_congr_ae (hx.filter_mono (ae_mono Measure.restrict_le_self))

/-! ## 3  The FS box projections -/

/-- **The FS box projection respects a.e. equality of the state.** -/
theorem boxPInd_congr_ae {volA : ℝ} {A : Set ℝ³} (i : Fin N) {F G : X N → ℝ}
    (h : F =ᵐ[volume] G) :
    boxPInd volA A i F =ᵐ[volume] boxPInd volA A i G := by
  have hslice := ae_eq_slice_set i A h
  filter_upwards [hslice] with x hx
  simp only [boxPInd]
  rw [hx]

/-- **The FS mean-free projection respects a.e. equality of the state.** -/
theorem boxQInd_congr_ae {volA : ℝ} {A : Set ℝ³} (i : Fin N) {F G : X N → ℝ}
    (h : F =ᵐ[volume] G) :
    boxQInd volA A i F =ᵐ[volume] boxQInd volA A i G := by
  have hP := boxPInd_congr_ae (volA := volA) (A := A) i h
  have h1 : (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * F x) =ᵐ[volume]
      (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * G x) :=
    h.mono fun x hx => by
      show A.indicator (fun _ => (1 : ℝ)) (x i) * F x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * G x
      rw [hx]
  filter_upwards [h1, hP] with x h1x hPx
  simp only [boxQInd]
  rw [h1x, hPx]

end Work.FibreWord
