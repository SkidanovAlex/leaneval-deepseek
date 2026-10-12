import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open Submission.BoseGases

/-- The sliding small box `B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is compact
for `ℓ > 0`, `d > 0`: it is the intersection of the closed cube `acube ℓ` with
the preimage of the closed cube `acube (ℓd)` under the continuous translation
`x ↦ x − (ℓd)•u`, hence closed, and contained in the compact cube `acube ℓ`. -/
theorem isCompact_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) : IsCompact (Submission.BoseGases.dlBox ℓ d u) := by
  have hpre : IsClosed ((fun x : EuclideanSpace ℝ (Fin 3) => x - (ℓ * d) • u) ⁻¹'
      Submission.BoseGases.acube (ℓ * d)) :=
    (Submission.BoseGases.acube_isClosed (ℓ * d)).preimage (by fun_prop)
  refine (Submission.BoseGases.acube_compact hℓ).of_isClosed_subset ?_ ?_
  · unfold Submission.BoseGases.dlBox
    exact (Submission.BoseGases.acube_isClosed ℓ).inter hpre
  · intro x hx
    exact (Submission.BoseGases.mem_dlBox_iff ℓ d u x).mp hx |>.1

end Work.SmallBoxTBWord
