import Mathlib
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQInd_sq_aesm`

A.e. strong measurability of the square of the FS-faithful mean-free box projection
`Work.UBBInputs8.boxQInd` (`Q_{B,i} = 1_{B,i} − P_{B,i}`) against the box measure
`volume.restrict (abox N a)`, for an arbitrary `Ψ` that is only a.e. strongly measurable.

The one non-trivial input is that overwriting one particle coordinate with a value of
`A ⊆ acube a` pushes the box measure into the box measure (quasi-measure-preservation):
`(x, u) ↦ update x i u` maps `(vol↾abox (n+1) a) ⊗ (vol↾A)` absolutely continuously into
`vol↾abox (n+1) a`.  A.e. strong measurability then transfers
(`AEStronglyMeasurable.comp_quasiMeasurePreserving`) and Fubini for the Bochner integral
(`AEStronglyMeasurable.integral_prod_right'`) gives measurability of the box mean.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open Submission.BoseGases

theorem boxQInd_sq_aesm {a volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolApos : 0 < volA)
    (hA : MeasurableSet A) (hsub : A ⊆ Submission.BoseGases.acube a) {N : ℕ} (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ)
    (hΨm : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hW : Measurable (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) =>
        Function.update p.1 i p.2) := by fun_prop
    have hqmp : Measure.QuasiMeasurePreserving
        (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) => Function.update p.1 i p.2)
        ((volume.restrict (abox (n + 1) a)).prod (volume.restrict A))
        (volume.restrict (abox (n + 1) a)) := by
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
        all_goals first | fun_prop | measurability
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
                (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl)) hW
          _ = (volume.restrict (acube a)) Set.univ •
                volume.restrict (abox (n + 1) a) := hsym
      exact Measure.absolutelyContinuous_of_le_smul hle
    -- a.e. strong measurability of the joint function `(x,u) ↦ Ψ (update x i u)`
    have hjoint : AEStronglyMeasurable
        (fun p : X (n + 1) × EuclideanSpace ℝ (Fin 3) => Ψ (Function.update p.1 i p.2))
        ((volume.restrict (abox (n + 1) a)).prod (volume.restrict A)) :=
      hΨm.comp_quasiMeasurePreserving hqmp
    -- and hence of the one-slot box mean, by Fubini for the Bochner integral
    have hmean : AEStronglyMeasurable
        (fun x : X (n + 1) => ∫ z in A, Ψ (Function.update x i z))
        (volume.restrict (abox (n + 1) a)) := hjoint.integral_prod_right'
    have hInd : Measurable (fun x : X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hA).comp (measurable_pi_apply i)
    have hQ : (fun x : X (n + 1) => Work.UBBInputs8.boxQInd volA A i Ψ x)
        = fun x : X (n + 1) => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
            - (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
              * A.indicator (fun _ => (1 : ℝ)) (x i) := by
      funext x
      rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have hq : AEStronglyMeasurable
        (fun x : X (n + 1) => Work.UBBInputs8.boxQInd volA A i Ψ x)
        (volume.restrict (abox (n + 1) a)) := by
      rw [hQ]
      exact (hInd.aestronglyMeasurable.mul hΨm).sub
        ((hmean.const_mul (1 / volA)).mul hInd.aestronglyMeasurable)
    exact hq.pow 2

end Work.BoseFixB1S
