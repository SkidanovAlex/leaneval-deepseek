import Mathlib
import Submission.Work.BoseFixB1S.boxQInd_sq_aesm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.Gen.boxQIndAesm`

A.e. strong measurability of the FS-faithful mean-free box projection
`Work.UBBInputs8.boxQInd volA A i Ψ = 1_A(x i)·Ψ − (1/volA)∫_{z∈A} Ψ(x|i↦z) dz`
against the box measure `volume.restrict (abox N ℓ)`, for an arbitrary `Ψ` that is only
a.e. strongly measurable — the *linear* companion of
`Work.BoseFixB1S.boxQInd_sq_aesm` (which handles the square).

The only measure-theoretic input is that overwriting the `i`-th coordinate with a value in
`A ⊆ acube ℓ` pushes the box measure quasi-onto itself (`qmp_update_abox_gen` below):
`hΨm.comp_quasiMeasurePreserving` gives a.e. strong measurability of the joint function
`(x,z) ↦ Ψ (update x i z)`, and Fubini for the Bochner integral
(`AEStronglyMeasurable.integral_prod_right'`) gives that of the box mean.  The rest is the
pointwise decomposition `boxQInd = 1_A(x i)·Ψ − (1/volA)·mean·1_A(x i)`.

Note that `hvol : 0 < volA` is not needed for the measurability statement itself (no
division/integrability takes place); `hA` is used only to see the box indicator as a
measurable function.
-/

namespace Work.BoseFixB1S.Gen

open MeasureTheory
open Submission.BoseGases

/-- **Quasi-measure-preservation of the slot-update map.**  Overwriting the `i`-th coordinate
of a configuration by an independent value drawn from `A ⊆ acube a` maps
`(volume.restrict (abox (n+1) a)) ⊗ (volume.restrict A)` into a measure absolutely continuous
w.r.t. `volume.restrict (abox (n+1) a)`.

This is the measure-theoretic content of the box projection's fibre averaging, isolated from
`Work.BoseFixB1S.boxQInd_sq_aesm` (where it appears inline). -/
theorem qmp_update_abox_gen {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAc : A ⊆ acube a) (n : ℕ) (i : Fin (n + 1)) :
    Measure.QuasiMeasurePreserving
      (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) => Function.update p.1 i p.2)
      ((volume.restrict (abox (n + 1) a)).prod (volume.restrict A))
      (volume.restrict (abox (n + 1) a)) := by
  have hW : Measurable (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 i p.2) := by fun_prop
  -- the peel of the box at slot `i`, in the direction `kcInsN n i`
  have hT : MeasurePreserving (⇑(kcInsN n i))
      ((volume.restrict (acube a)).prod (volume.restrict (abox n a)))
      (volume.restrict (abox (n + 1) a)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) =>
        EuclideanSpace ℝ (Fin 3)) i)) (abox_peel_mp (n := n) a i)
    simpa [kcInsN] using h
  -- the symmetric case `A = acube a`: the pushforward of the update map
  have hsym : Measure.map
      (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) => Function.update p.1 i p.2)
      ((volume.restrict (abox (n + 1) a)).prod (volume.restrict (acube a)))
      = (volume.restrict (acube a)) Set.univ •
        volume.restrict (abox (n + 1) a) := by
    have hσ : Measurable (fun z : (EuclideanSpace ℝ (Fin 3) × X n) ×
        EuclideanSpace ℝ (Fin 3) => (z.2, z.1.2)) := by fun_prop
    have h1 : (volume.restrict (abox (n + 1) a)).prod (volume.restrict (acube a))
        = Measure.map (Prod.map (⇑(kcInsN n i)) id)
            (((volume.restrict (acube a)).prod (volume.restrict (abox n a))).prod
              (volume.restrict (acube a))) := by
      rw [← Measure.map_prod_map ((volume.restrict (acube a)).prod
            (volume.restrict (abox n a))) (volume.restrict (acube a))
            (kcInsN n i).measurable measurable_id, hT.map_eq, Measure.map_id]
    rw [h1, Measure.map_map hW (Measurable.prodMap (kcInsN n i).measurable measurable_id)]
    have hcomp : ((fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
          Function.update p.1 i p.2) ∘ (Prod.map (⇑(kcInsN n i)) id))
        = fun z : (EuclideanSpace ℝ (Fin 3) × X n) × EuclideanSpace ℝ (Fin 3) =>
            kcInsN n i (z.2, z.1.2) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      rw [Submission.BoseGases.update_kcInsN]
    rw [hcomp]
    have h2 : (fun z : (EuclideanSpace ℝ (Fin 3) × X n) × EuclideanSpace ℝ (Fin 3) =>
          (kcInsN n i) (z.2, z.1.2))
        = (⇑(kcInsN n i)) ∘ (fun z : (EuclideanSpace ℝ (Fin 3) × X n) ×
            EuclideanSpace ℝ (Fin 3) => (z.2, z.1.2)) := rfl
    rw [h2, ← Measure.map_map (kcInsN n i).measurable hσ]
    have h3 : (fun z : (EuclideanSpace ℝ (Fin 3) × X n) × EuclideanSpace ℝ (Fin 3) =>
          (z.2, z.1.2))
        = Prod.swap ∘ (Prod.map Prod.snd (id : EuclideanSpace ℝ (Fin 3) →
            EuclideanSpace ℝ (Fin 3))) := by
      funext z; simp [Prod.map]
    rw [h3, ← Measure.map_map measurable_swap
      (Measurable.prodMap measurable_snd measurable_id)]
    rw [← Measure.map_prod_map ((volume.restrict (acube a)).prod
          (volume.restrict (abox n a))) (volume.restrict (acube a))
          measurable_snd measurable_id]
    rw [Measure.map_snd_prod, Measure.map_id, Measure.prod_smul_left, Measure.map_smul,
      Measure.prod_swap, Measure.map_smul, hT.map_eq]
    all_goals first | fun_prop | (apply Continuous.aestronglyMeasurable; fun_prop) | (apply Continuous.aemeasurable; fun_prop) | (apply Continuous.measurable; fun_prop) | measurability
  refine ⟨hW, ?_⟩
  have hle : Measure.map (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
        Function.update p.1 i p.2)
        ((volume.restrict (abox (n + 1) a)).prod (volume.restrict A))
      ≤ (volume.restrict (acube a)) Set.univ •
        volume.restrict (abox (n + 1) a) :=
    calc Measure.map (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
            Function.update p.1 i p.2)
            ((volume.restrict (abox (n + 1) a)).prod (volume.restrict A))
        ≤ Measure.map (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
            Function.update p.1 i p.2)
            ((volume.restrict (abox (n + 1) a)).prod (volume.restrict (acube a))) :=
          Measure.map_mono
            (Measure.prod_mono le_rfl (Measure.restrict_mono hAc le_rfl)) hW
      _ = (volume.restrict (acube a)) Set.univ •
            volume.restrict (abox (n + 1) a) := hsym
  exact Measure.absolutelyContinuous_of_le_smul hle

/-- A.e. strong measurability of the one-slot box mean `x ↦ ∫_{z∈A} Ψ (update x i z)` for an
a.e. strongly measurable `Ψ` on the box. -/
theorem aesm_update_boxMean {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAc : A ⊆ acube a) (n : ℕ) (i : Fin (n + 1)) {Ψ : X (n + 1) → ℝ}
    (hΨm : AEStronglyMeasurable Ψ (volume.restrict (abox (n + 1) a))) :
    AEStronglyMeasurable (fun x : X (n + 1) => ∫ z in A, Ψ (Function.update x i z))
      (volume.restrict (abox (n + 1) a)) :=
  (hΨm.comp_quasiMeasurePreserving (qmp_update_abox_gen hAc n i)).integral_prod_right'

theorem boxQIndAesm {N : ℕ} {ℓ volA : ℝ} (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨm : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxQInd volA A i Ψ x)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hmean := aesm_update_boxMean (a := ℓ) hAc n i hΨm
    have hInd : Measurable (fun x : X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hA).comp (measurable_pi_apply i)
    have hQ : (fun x : X (n + 1) => Work.UBBInputs8.boxQInd volA A i Ψ x)
        = fun x : X (n + 1) => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
            - (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
              * A.indicator (fun _ => (1 : ℝ)) (x i) := by
      funext x
      rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    rw [hQ]
    exact (hInd.aestronglyMeasurable.mul hΨm).sub
      ((hmean.const_mul (1 / volA)).mul hInd.aestronglyMeasurable)

end Work.BoseFixB1S.Gen
