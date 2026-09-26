import Mathlib
import Submission.Work.BoxShrink.crux
import Submission.Work.BoxShrink.sweepNice_of_ae
import Submission.Work.BoxShrink.Core.All
import Submission.Work.BoxShrink.Bubble.Corrected

/-!
# Assembling Pardon's shrinking step from the crux

`Work.BoxShrink.boxShrink_of_crux` proves `Submission.BoxShrinkStatement` from
`Work.BoxShrink.CruxStatement = CleansDiscsAll ∧ CruxCore p q ∧ AeSlicedAll`:

* `AeSlicedAll` (the almost-everywhere general position of the box-norm level sets) gives
  `SweepNice` through `Work.BoxShrink.sweepNice_of_ae`, i.e. a swept level `s` in general position
  with the two intersection counts;
* `CruxCore` (Pardon's double bubble, using `CleansDiscsAll`) gives an essential loop in one of
  the two halves of `PBox s c σ` cut by the plane;
* the halving geometry (`Work.BoxShrink.hasEssBox_of_upperHalf` / `hasEssBox_of_lowerHalf`) turns
  it into a box of size `shrinkFactor * r`.
-/

namespace Work.BoxShrink

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **`SweepNice` from the almost-everywhere general position.** -/
theorem SweepNice.of_aeAll (h : AeSlicedAll) : ∀ p q : ℕ, SweepNice p q := by
  intro p q hp hq hc ψ K d hd hbound _himg _hsmall r hr c σ
  exact sweepNice_of_ae ψ K hd hbound r hr c σ (h ψ c σ)

/-- **`BoxShrinkStatement` from the crux.**  The sweep in general position gives the level `s`
and the plane level `u` with their counts, the double-bubble core gives an essential loop in one
of the two halves, and the halving geometry converts it into a box of size `shrinkFactor * r`. -/
theorem boxShrink_of_crux (h : ∀ p q : ℕ, CruxStatement p q) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ hbox
  obtain ⟨hcl, hcore, hae⟩ := h p q
  obtain ⟨s, hs, hslice, hS, u, hu, hU⟩ :=
    SweepNice.of_aeAll hae p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ
  rcases hcore hp hq hc ψ K d hd hbound himg hsmall (hcl ψ)
      r hr c σ hbox s hs.1 hs.2 hslice u (abs_lt.mpr hu) hS hU with hup | hlow
  · exact ⟨_, _, hasEssBox_of_upperHalf (P := Work.CoreTopology.ParamTorus.mapHomeomorph
        ψ.toHomeomorph) hr hs.1 hs.2 (abs_lt.mpr hu) hup⟩
  · exact ⟨_, _, hasEssBox_of_lowerHalf (P := Work.CoreTopology.ParamTorus.mapHomeomorph
        ψ.toHomeomorph) hr hs.1 hs.2 (abs_lt.mpr hu) hlow⟩


end

end Work.BoxShrink
