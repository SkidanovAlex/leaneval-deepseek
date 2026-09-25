import Mathlib
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ShafarevichKoch.continuous_restrictToEmpty
import Submission.Work.TopologyGroup.isOpenMap_of_compact_surjective

/-!
# `Work.ShafarevichKoch.isOpenMap_restrictToEmpty`

The comparison `restrictToEmpty F p S : Gal(k_S/F) →* Gal(k_∅/F)` (`SupportedComparison.lean`) is
an **open** map for the Krull topologies.  Both groups are profinite (`CompactSpace Gal(K/k)` for
`IsGalois` extensions, `krullTopology_t2` for algebraic ones), so a continuous surjective
homomorphism between them is open -- the classical open mapping theorem, available in this
workspace as `Work.TopologyGroup.isOpenMap_of_compact_surjective`.

This is roadmap item (iii) of `README.md` §16.3, and it is exactly the hypothesis
`IsOpenMap E.q` of the corrected section-free counting lemma of §16.2 (equivalently, it is what
makes `q⁻¹ (q U) = U · ker q` open, i.e. `q` a quotient map).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **The comparison is an open map.** -/
theorem isOpenMap_restrictToEmpty (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) : IsOpenMap (restrictToEmpty F p S) := by
  haveI : IsGalois F ↥(kSupported F p S) := isGalois_kSupported (F := F) (p := p) (S := S)
  haveI : IsGalois F ↥(kSupported F p (∅ : Finset ℕ)) :=
    isGalois_kSupported (F := F) (p := p) (S := (∅ : Finset ℕ))
  exact Work.TopologyGroup.isOpenMap_of_compact_surjective (restrictToEmpty F p S)
    (continuous_restrictToEmpty F p S) (restrictToEmpty_surjective F p S)

end Work.ShafarevichKoch
