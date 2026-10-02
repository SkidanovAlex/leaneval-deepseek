import Mathlib
import Submission.Work.Tubular.Transversality
import Submission.Work.Tubular.DiscManifold.TubeFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The transversality of the collapse, for a tube chart

This file discharges `Work.Tubular.TubeTransversality` — the last *input* of the Transversality
chapter (`Submission/Work/Tubular/Transversality.lean`) — for the tube chart `C` of any embedding
data `E : V ↪ ℝ^{8+k}`: the derivative of the normal coordinate at a point of the zero section has
image exactly the normal space `ν_x = T_x^⊥`.

Two on-disk facts combine:

* `Work.Tubular.range_normalProj` (`DiscManifold/TubeFrame.lean`): the range of the Fréchet
  derivative of the normal coordinate `tubeNormal C y = (C.inv y).1.2` at `E.e x` is `ν_x`.  This is
  the geometric content, proved by hand from the two defining properties of the tube chart
  (`tubeNormal_embedding`: the normal coordinate vanishes on `e(V)`, so its derivative kills
  `T_x = range (mfderiv E.e x)`, and `tubeNormal_add`: it is the identity on the normal disc, so its
  derivative is the identity on `ν_x`) together with the dimension count
  `finrank ℝ T_x = 8`, `finrank ℝ ν_x = k`.
* `mfderiv_eq_fderiv`: for a map between vector spaces the manifold derivative and the Fréchet
  derivative coincide, so the `mfderiv` in the statement of `TubeTransversality` *is* the `fderiv`
  computed above.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

theorem TubeTransversalityOfChart {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : Work.Tubular.TubeTransversality E ε C := by
  refine ⟨fun x => ?_⟩
  rw [mfderiv_eq_fderiv]
  have h := range_normalProj (E := E) C x
  simp only [normalProj] at h
  exact h.symm

end Work.Tubular
