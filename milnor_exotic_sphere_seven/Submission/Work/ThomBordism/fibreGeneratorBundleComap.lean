import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.comapAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-- The map between the fibres of the pullback and of the bundle, induced by the total-space map
`⟨x,v⟩ ↦ ⟨f x, v⟩`. -/
def fibreMapComap (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') :
    C(↥(fibre (Work.Thom.bundleComap Z f) b'), ↥(fibre Z (f b'))) :=
  ⟨fun p => ⟨Work.Thom.totalMap Z f p.1, by
      rw [Work.Thom.totalMap_apply]
      exact congrArg f p.2⟩,
   Continuous.subtype_mk ((Work.Thom.totalMap Z f).continuous.comp continuous_subtype_val)
     (fun p => by
      show (Work.Thom.totalMap Z f (p : (Work.Thom.bundleComap Z f).TotalSpace)).1 = f b'
      rw [Work.Thom.totalMap_apply]
      exact congrArg f p.2)⟩

@[simp] theorem fibreMapComap_apply (Z : RealBundle B F ι) (f : C(B', B)) (b' : B')
    (p : ↥(fibre (Work.Thom.bundleComap Z f) b')) :
    ((fibreMapComap Z f b' p : ↥(fibre Z (f b'))) : Z.TotalSpace)
      = Work.Thom.totalMap Z f (p : (Work.Thom.bundleComap Z f).TotalSpace) := rfl

/-- The fibre map commutes with the inclusions into the total spaces. -/
theorem fibreIncl_comp_fibreMapComap (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') :
    (fibreIncl Z (f b')).comp (fibreMapComap Z f b')
      = (Work.Thom.totalMap Z f).comp (fibreIncl (Work.Thom.bundleComap Z f) b') := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The fibre map carries the punctured fibre into the punctured fibre. -/
theorem fibreMapComap_mem (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') :
    ∀ x ∈ fibrePunctSub (Work.Thom.bundleComap Z f) b',
      fibreMapComap Z f b' x ∈ fibrePunctSub Z (f b') := by
  intro x hx
  refine ⟨?_, hx.2⟩
  rw [fibreMapComap_apply, Work.Thom.totalMap_apply]
  exact congrArg f hx.1

end

end Work.ThomBordism
