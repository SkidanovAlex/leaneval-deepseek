import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

namespace Work.Maximal

open MeasureTheory Set Filter

/-- The fundamental-domain lift respects a.e. equality of circle functions: if `f =ᵐ g` on the
circle `𝕋 = AddCircle 1` (with the Haar measure `haarAddCircle`), then their lifts
`circleLift f x = if x ∈ Ioc (-1/2) (1/2] then f (-(x:𝕋)) else 0` agree a.e. on `ℝ`. -/
theorem circleLift_ae_eq_congr {f g : AddCircle (1:ℝ) → ℂ}
    (h : f =ᵐ[AddCircle.haarAddCircle (T := 1)] g) :
    Work.BourgainPlan.Thm52.circleLift f =ᵐ[volume] Work.BourgainPlan.Thm52.circleLift g := by
  -- For `T = 1` the standard measure on `AddCircle 1` is exactly the normalized Haar measure.
  have hvol : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have h1 : f =ᵐ[volume] g := by rw [hvol]; exact h
  -- Negation on the circle is measure preserving, so `ξ ↦ f (-ξ) =ᵐ ξ ↦ g (-ξ)`.
  have h2 : (fun ξ : AddCircle (1:ℝ) => f (-ξ)) =ᵐ[volume]
      (fun ξ : AddCircle (1:ℝ) => g (-ξ)) :=
    (Measure.measurePreserving_neg (volume : Measure (AddCircle (1:ℝ)))).quasiMeasurePreserving.ae_eq h1
  have hIeq : Set.Ioc (-(1/2:ℝ)) (-(1/2) + 1) = Set.Ioc (-(1/2:ℝ)) (1/2) := by
    rw [show -(1/2:ℝ) + 1 = 1/2 by norm_num]
  -- The covering map `ℝ → AddCircle 1` is measure preserving from the fundamental domain.
  have hqmp : Measure.QuasiMeasurePreserving (fun x : ℝ => (x : AddCircle (1:ℝ)))
      (volume.restrict (Set.Ioc (-(1/2:ℝ)) (1/2))) volume := by
    have hmp := (AddCircle.measurePreserving_mk (1:ℝ) (-(1/2))).quasiMeasurePreserving
    rwa [hIeq] at hmp
  have h3 : (fun x : ℝ => f (-(x : AddCircle (1:ℝ))))
      =ᵐ[volume.restrict (Set.Ioc (-(1/2:ℝ)) (1/2))]
      (fun x : ℝ => g (-(x : AddCircle (1:ℝ)))) := hqmp.ae_eq h2
  -- The bad set of the lifts is contained in the preimage of the bad set of `f, g` inside the
  -- fundamental domain, which has measure zero.
  have hbad : volume {x : ℝ | ¬ (Work.BourgainPlan.Thm52.circleLift f x =
      Work.BourgainPlan.Thm52.circleLift g x)} = 0 := by
    have h3bad := (MeasureTheory.ae_iff).mp h3
    rw [Measure.restrict_apply' measurableSet_Ioc] at h3bad
    refine measure_mono_null ?_ h3bad
    intro x hx
    by_cases hxI : x ∈ Set.Ioc (-(1/2:ℝ)) (1/2)
    · refine ⟨?_, hxI⟩
      intro hfg
      refine hx ?_
      rw [Work.BourgainPlan.Thm52.circleLift_of_mem hxI,
        Work.BourgainPlan.Thm52.circleLift_of_mem hxI]
      exact hfg
    · exact absurd (by rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hxI,
        Work.BourgainPlan.Thm52.circleLift_of_notMem hxI]) hx
  exact (MeasureTheory.ae_iff).mpr hbad

end Work.Maximal
