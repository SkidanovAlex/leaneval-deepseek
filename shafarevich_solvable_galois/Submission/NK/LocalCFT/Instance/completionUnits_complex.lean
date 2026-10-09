import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean instance of the local side: `ℝˣ^{∧} ≃* Gal(ℂ/ℝ)`

`NK.LocalCFT.Instance.artinReciprocity_complex` instantiates the corrected local reciprocity datum
`NK.LocalCFT.ArtinReciprocity ℝ ℂ` (the archimedean local field: `Gal(ℂ/ℝ) ≅ ℤ/2`, the Artin map
being the sign map `ℝˣ →* ℤ/2` with kernel `ℝ_{>0} = N_{ℂ/ℝ}ℂˣ`).

Consequently the two outputs of the local side of the Neukirch–Uchida development are
*unconditional* at the archimedean place:

* the infinite-level reciprocity isomorphism `ℝˣ^{∧} ≃* Gal(ℂ/ℝ)` (this file), and
* the local Brauer computation `NK.BrauerHasse.LocalFieldBrauerCyclic 2 ℝ ℂ`
  (`NK.LocalCFT.Brauer.localFieldBrauerCyclic_complex`).

For a `p`-adic `κ` the analogous statements are *reduced* to the two classical theorems of local
class field theory (the canonical reciprocity law and `Br(κ)[p] ≅ ℤ/p`); see `README.md` §§3–4.
-/

open scoped Classical

namespace NK.LocalCFT

universe u

/-- **The archimedean infinite-level local reciprocity**: the profinite completion of `ℝˣ` (which
is `ℤ/2`, `ℝ_{>0}` being divisible) is the abelianised absolute Galois group `Gal(ℂ/ℝ) ≅ ℤ/2`. -/
theorem completionUnits_complex [IsSepClosure ℝ ℂ] :
    Nonempty (NK.LocalReciprocity.completionUnits ℝ ≃* NK.LocalCFT.AbGal ℝ ℂ) :=
  NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
    (Classical.choice (NK.LocalCFT.Instance.artinReciprocity_complex))

end NK.LocalCFT
