import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local norm subgroup is everything at an infinite place of a totally complex field

If the base field `M` is *totally complex* (`NumberField.IsTotallyComplex M`, i.e. every infinite
place of `M` is complex), then for **every** finite extension `E/M` the local norm subgroup at any
infinite place `w` of `M` is everything:

`localNormSubgroup (K := M) (L := E) (Place.ofInfinite w) = ⊤`.

Indeed every place `w'` of `E` above `w` is complex, and the local norm `ℂˣ → ℂˣ` is surjective
(`NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex`), so one local norm
factor already fills the supremum
(`NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top`).

This is the design's "at a real place `v₀` the local group of `E_w/M_v` is trivial" step in step L7
of `Submission/Work/CFTLib/HR/STATUS_proof_owner.md`: for `M = K(ζ_q)` (`q > 2`) the field `M` is
totally complex, hence every element of `M_wˣ` is a local norm from `E_w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

noncomputable section

namespace NK.CFTLib.HR

/-- **The local norm subgroup at an infinite place of a totally complex field is `⊤`.** -/
theorem localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex
    {M E : Type} [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra M E] [FiniteDimensional M E] [IsGalois M E]
    (htc : NumberField.IsTotallyComplex M) (w : NumberField.InfinitePlace M) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E)
      (NK.GlobalCFT.Place.ofInfinite w) = ⊤ := by
  haveI : NumberField.IsTotallyComplex M := htc
  obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := M) (L := E) w
  haveI : w'.LiesOver w := hw'
  refine NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top
    (K := M) (L := E) (v := w) (w₀ := w') ?_
  exact NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
    (K := M) (L := E) (v := w) (w := w') (NumberField.IsTotallyComplex.isComplex w)
    (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' (NumberField.IsTotallyComplex.isComplex w))

end NK.CFTLib.HR
