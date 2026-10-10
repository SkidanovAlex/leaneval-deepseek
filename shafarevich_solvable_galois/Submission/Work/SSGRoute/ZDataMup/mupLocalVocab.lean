import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local arithmetic at a finite place: the completion, the local Galois identification, and
the local Artin map

For a finite place `A` of `Ω` over `k` (an algebraic closure of the number field `k`), with
`K/k` finite Galois and `ζ_p ∈ K`, this file fixes the local objects attached to `A` that the wiring
of the `μ_p` local Tate system consumes (see `NOTES_mup_wiring_session6.md`, item 2 of the build
order):

* the completion `κ_A = 𝔭.adicCompletion ↥K` at the canonical prime `𝔭 = primeOf A hAK` of `↥K`
  below `A`;
* the **local Galois identification** `↥(decomp (k := ↥K) A) ≃* Gal(κ̄_A/κ_A)`, a homeomorphism
  (`ZConstruction.localGaloisEquiv_decomp_canonical`);
* the **local Artin reciprocity datum** at `κ_A`
  (`NK.NUV2.kernelCondition_all` + `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`),
  i.e. `rec_A : κ_Aˣ →* Gal(κ_A^ab/κ_A)` with the level isomorphisms.

Everything here is axiom-clean: the local class field theory of the completions is proved in the
`NK` chapter.
-/

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The local field of `A`**: the completion of `↥K` at the canonical prime `𝔭 = primeOf A hAK`
below `A`. -/
abbrev mupCompletion (A : ValuationSubring Ω) (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) : Type :=
  (Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K

/-- **The local Galois identification** `↥(decomp (k := ↥K) A) ≃* Gal(κ̄_A/κ_A)` at the canonical
prime, chosen once and for all (`ZConstruction.localGaloisEquiv_decomp_canonical`); it is a
homeomorphism for the Krull topologies (`isHomeomorph_mupLocalGalEquiv`). -/
noncomputable def mupLocalGalEquiv (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    ↥(_root_.SSGRoute.decomp (k := ↥K) A) ≃*
      ((SeparableClosure (mupCompletion (K := K) A hAK)) ≃ₐ[mupCompletion (K := K) A hAK]
        (SeparableClosure (mupCompletion (K := K) A hAK))) :=
  Classical.choose (Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp_canonical
    (p := p) (k := k) (Ω := Ω) (K := K) A hAK)

/-- The chosen local Galois identification is a homeomorphism. -/
theorem isHomeomorph_mupLocalGalEquiv (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    IsHomeomorph (mupLocalGalEquiv (p := p) (K := K) A hAK :
      ↥(_root_.SSGRoute.decomp (k := ↥K) A) →
        ((SeparableClosure (mupCompletion (K := K) A hAK)) ≃ₐ[mupCompletion (K := K) A hAK]
          (SeparableClosure (mupCompletion (K := K) A hAK)))) :=
  Classical.choose_spec (Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp_canonical
    (p := p) (k := k) (Ω := Ω) (K := K) A hAK)

/-- **The local Artin reciprocity datum at `κ_A`**: the local class field theory of the completion
(`NK.NUV2.kernelCondition_all` produces the kernel condition, and
`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` the full datum). -/
noncomputable def mupArtinReciprocity (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    NK.LocalCFT.ArtinReciprocity (mupCompletion (K := K) A hAK)
      (SeparableClosure (mupCompletion (K := K) A hAK)) :=
  Classical.choice (NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion
    (Submission.NeukirchUchida.primeOf A hAK)
    (NK.NUV2.kernelCondition_all ↥K (Submission.NeukirchUchida.primeOf A hAK)).some)

/-- **The local Artin map** `rec_A : κ_Aˣ →* Gal(κ_A^ab/κ_A)` of the completion. -/
noncomputable def mupRec (A : ValuationSubring Ω) (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    (mupCompletion (K := K) A hAK)ˣ →*
      NK.LocalCFT.AbGal (mupCompletion (K := K) A hAK)
        (SeparableClosure (mupCompletion (K := K) A hAK)) :=
  (mupArtinReciprocity (K := K) A hAK).artin

/-- **The level isomorphism at every finite abelian level of `κ_A^ab`**: the composite of `rec_A`
with the restriction to a finite abelian level is surjective with kernel the norm group. -/
theorem mupRec_isLevelIso (A : ValuationSubring Ω)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (L : IntermediateField (mupCompletion (K := K) A hAK)
      (NK.LocalReciprocity.maxAbelianSubext (mupCompletion (K := K) A hAK)
        (SeparableClosure (mupCompletion (K := K) A hAK))))
    [FiniteDimensional (mupCompletion (K := K) A hAK) L]
    [Normal (mupCompletion (K := K) A hAK) L]
    (hcomm : ∀ σ τ : L ≃ₐ[mupCompletion (K := K) A hAK] L, σ * τ = τ * σ) :
    Function.Surjective ((NK.LocalCFT.levelRestrict L).comp
        (mupRec (K := K) A hAK)) ∧
      MonoidHom.ker ((NK.LocalCFT.levelRestrict L).comp
        (mupRec (K := K) A hAK)) =
        NK.LocalReciprocity.normGroup (mupCompletion (K := K) A hAK) ↥L :=
  (mupArtinReciprocity (K := K) A hAK).isLevelIso L hcomm

end

end Work.SSGRoute.ZDataMup
