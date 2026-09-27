import Mathlib
import Submission.Work.EKLC6Core.adapted_partition
import Submission.Work.EKLC6Core.cutData_of_partition

/-!
# `Work.EKLC6Core.cutHCutData` — existence of the "cut" data at an arbitrary scale `η > 0`

For every probability measure `μ` on `X₃`, every subgroup `U ≤ SL₃(ℝ)` and every `η > 0` there is
a `CutData μ U η`, i.e. a finite cell/lift system (Pisa 7.38) whose exceptional piece has mass
`< η`.

The proof is an assembly of the two independent ingredients:

* `Work.EKLC6Core.adapted_partition` (Pisa 7.37): for every `ε > 0` a finite open disjoint family
  `Q i` of `V ρ`-diameter with `Γ₃`-free centres at scale `60 ρ`, covering all but `< ε` of `μ`,
  with `μ`-thin boundaries;
* `Work.EKLC6Core.cutData_of_partition` (Pisa 7.38): from such a family, with `ε` the *same*
  scale as the `CutData` parameter, build a `CutData μ U ε` at a smaller diameter scale
  `S.ρ ≤ ρ`.

The only bookkeeping is that `cutData_of_partition` asks for the centres to be `Γ₃`-free at scale
`30 ρ`, which follows from `adapted_partition`'s stronger `60 ρ` version by monotonicity of `V`.
-/

namespace Work.EKLC6Core

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise
open Work.EKLContract

theorem cutHCutData (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup Work.EKLContract.SL3)
    (η : ℝ) (hη : 0 < η) :
    Nonempty (Work.EKLC6Core.CutData μ U η) := by
  obtain ⟨N, Q, g, ρ, c, hρ, hc, hopen, hdisj, hgm, hsub, hinj, hbad, hthin⟩ :=
    Work.EKLC6Core.adapted_partition μ η hη
  refine ⟨(Work.EKLC6Core.cutData_of_partition Q g c ρ hρ hc hopen hdisj hgm hsub
    (fun i γ hγ hm => hinj i γ hγ (Work.EKLC6Core.adapted_V_mono (by linarith) hm))
    hthin (fun i => (hopen i).measurableSet) η hη hbad).choose⟩

end Work.EKLC6Core
