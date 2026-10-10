import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow
import Submission.Work.SSGRoute.ZConstruction.AuxTwoOfRealisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-field `p = 2` orthogonality gate from the `NoKimag` lane's theorem

`Work.SSGRoute.ZConstruction.TwoFieldOrthogonalityAll` (`ZConstruction/AuxTwoOfRealisation.lean`) is
the `p = 2` orthogonality gate consumed by the two-field realisation
(`Work.SSGRoute.ZConstruction.auxRealisationGate_of_twoField`), hence by the `p = 2` case of the node
`Work.SSGRoute.shafarevich_z_construction`.

Its content is verbatim the conclusion of the two-field narrow orthogonality
`Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` (`NoKimag/OrthHsplitTwoNarrow.lean`), which the
`NoKimag` lane has proved sorry-free and axiom-clean.  The only difference between the two
statements is the bookkeeping of the primitive `2`-nd root of unity: the gate is stated for
`ζ : Ω` together with `hζK : ζ ∈ K` and `hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2` (this is the shape
in which the node's `z_data_general_of_ramified` carries it), whereas the orthogonality theorem is
stated for `ζ : ↥K` and `hζ : IsPrimitiveRoot ζ 2`.  This file performs that identification
(`hζ ↦ hζK'`), rewriting the modulus `normClassSubgroup ↥K ↥M` of the gate by the hypothesis
`hMnorm` of the gate into the group `narrowGesU ↥K 2 T' ⊔ pPowSubgroup 2 _` in which the
orthogonality theorem states its conclusion.

See `ACTION_p2_twoFieldRealisation.md` and `PING_NoKimag_realisation_escape_field.md` §5. -/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- **The two-field narrow orthogonality of the `p = 2` escape, in the shape of the gate
`TwoFieldOrthogonalityAll`.**  For `ζ : Ω` with `ζ ∈ K` and `hζK'` the primitivity of `⟨ζ, hζK⟩` in
`↥K`, this is `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` read at `ζ = ⟨ζ, hζK⟩`, `hζ = hζK'`, with
the modulus group `normClassSubgroup ↥K ↥M` replaced by `narrowGesU ↥K 2 T' ⊔ pPowSubgroup 2 _`
along the gate's hypothesis `hMnorm`. -/
theorem twoFieldOrthogonalityAll_of_orthHsplitTwoNarrow (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2) :
    TwoFieldOrthogonalityAll (k := k) (Ω := Ω) K ζ hζ hζK hζK' := by
  intro Λ L₂ _ _ _ _ hKΛ hKL₂
  intro T hTfin hTdisj hTcov g hg hgc hgram hginf h hh hhc horth₁ horth₂ hsplit T' hTbelow hT'above
  intro M _ _ _ hMnorm N _ _ _ hN a ha hapos
  rw [hMnorm]
  exact Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow k Ω K ⟨ζ, hζK⟩ hζK' Λ L₂ hKΛ hKL₂ T hTfin
    hTdisj hTcov g hg hgc hgram hginf h hh hhc horth₁ horth₂ hsplit T' hTbelow hT'above N hN a ha
    hapos

end Work.SSGRoute.ZConstruction
