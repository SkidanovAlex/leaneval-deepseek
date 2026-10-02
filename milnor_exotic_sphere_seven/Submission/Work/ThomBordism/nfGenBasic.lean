import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.nfRead_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the oriented fibre generator `nfGen`, unconditionally

`Work.ThomBordism.nfGen` is defined in `Submission/Work/ThomBordism/orientedFibreGen.lean` as a
*conditional* expression (`if h : ∀ p ∈ nfPunct E x, nfRead E ND x p ≠ 0 then … else 0`), because the
membership obligation it needs was a separate delegation.  With
`Work.ThomBordism.nfRead_ne_zero` proved, the `else` branch is dead and `nfGen` is literally the
pullback of `Work.ThomBordism.stdThomGen` along the frame reading `Work.ThomBordism.nfRead`; that is
`Work.ThomBordism.nfGen_eq` below, which is the form the fibre comparisons consume.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-- **`nfGen` is the pullback of the standard generator along the frame reading.** -/
theorem nfGen_eq {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    nfGen hk E ND x
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
          (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k).hom (stdThomGen k hk) := by
  rw [nfGen]
  exact dif_pos fun p hp => nfRead_ne_zero hk E ND x p hp

end Work.ThomBordism
