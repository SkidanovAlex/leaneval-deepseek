import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open MeasureTheory

/-- The one-particle centred box is the cube: integrating `F : X 1 → ℝ` over `abox 1 s` is
integrating `z ↦ F (fun _ => z)` over `acube s`. -/
theorem integral_abox_one_slot {s : ℝ} (F : Submission.BoseGases.X 1 → ℝ) :
    (∫ x in Submission.BoseGases.abox 1 s, F x)
      = ∫ z in Submission.BoseGases.acube s, F (fun _ => z) := by
  -- `X 1 = Fin 1 → ℝ³` is measurably equivalent to `ℝ³` by evaluation at the unique slot,
  -- via the measure-preserving `MeasurableEquiv.funUnique`; the change of variables
  -- `z ↦ fun _ => z` is exactly its inverse, and `abox 1 s = e ⁻¹' acube s`.
  let e : Submission.BoseGases.X 1 ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
    MeasurableEquiv.funUnique (Fin 1) (EuclideanSpace ℝ (Fin 3))
  have he : ⇑e = fun x : Submission.BoseGases.X 1 => x 0 := by
    funext x
    simp [e, MeasurableEquiv.funUnique_apply]
  have hpre : Submission.BoseGases.abox 1 s = e ⁻¹' Submission.BoseGases.acube s := by
    ext x
    simp only [Set.mem_preimage, he]
    rw [Submission.BoseGases.mem_abox_iff]
    exact Fin.forall_fin_one
  have h1 :=
    (volume_preserving_funUnique (Fin 1) (EuclideanSpace ℝ (Fin 3))).setIntegral_preimage_emb
      e.measurableEmbedding (fun z : EuclideanSpace ℝ (Fin 3) => F (fun _ => z))
      (Submission.BoseGases.acube s)
  -- a configuration in `X 1` is determined by its unique slot
  have hfun : ∀ x : Submission.BoseGases.X 1, (fun _ : Fin 1 => e x) = x := by
    intro x
    funext i
    rw [Fin.eq_zero i]
    exact congrFun he x
  rw [hpre]
  rw [show (∫ x in ⇑e ⁻¹' Submission.BoseGases.acube s, F x)
      = ∫ x in ⇑e ⁻¹' Submission.BoseGases.acube s, F (fun _ => e x) from ?_]
  · exact h1
  · refine setIntegral_congr_fun ((MeasurableEquiv.measurableSet_preimage e).mpr
      (Submission.BoseGases.acube_measurable s)) (fun x _ => ?_)
    rw [hfun x]

end Work.KinPSuperadd
