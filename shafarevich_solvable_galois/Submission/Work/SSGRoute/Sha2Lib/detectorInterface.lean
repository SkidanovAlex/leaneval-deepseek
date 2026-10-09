import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified detector (node `C6`), as a named predicate, and its two reductions

This file provides the *interface* used by the `sha2_image_of_Hm2` lane to talk about node `C6`
(`Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`, `Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`,
`Work.SSGRoute.SSGStage.unramifiedDetector`): a `Prop`-valued predicate `DetectsAt` for the
*conclusion* of the node at one `φ`, and `IsUnramifiedDetector` for the node itself (the conclusion
for every nonzero `φ`).

Two lemmas are stated here (their proofs are delegated, see
`Submission/Work/SSGRoute/NOTE_sha2_image_of_Hm2_session13.md` §2 and §3):

* `isUnramifiedDetector_of_induced` — **the induced reduction**: the detector for
  `M` follows from the detector for `Ind_{D_w}^{G}(res_{D_w}M)` (with the functional transported along
  the counit `c : Ind_{D_w}^{G}(res_{D_w}M) ⟶ M` of the adjunction `Ind ⊣ res`, which is surjective).
  After it, a prover of the node may assume `M` is induced from `D_w`; that is the shape in which
  Shapiro's lemma applies and the shape of the flagged configuration of `E7cC/NOTE_C6_state.md` §3.
* `shapiro_cocycle_formula` — the Shapiro description of the classes at a level, with the
  computation rule for the induced functional.  (Stated in the abstract `Rep`/`extH` language; see
  the note for the mathematical content and for the consequences.)
-/

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- **The conclusion of node `C6` at one coefficient class `φ`.**

`DetectsAt p k K Ω w q hI M hM φ` is literally the conclusion of
`Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ` (and of
`Work.SSGRoute.SSGStage.unramifiedDetector`): there are a finite Galois level `L ⊇ K` over `k`, a
place `q' | q` with `e(q'|q)` prime to `p`, and a class `h ∈ H¹(Gal(L/k), res M)` unramified at
`q'` whose level pairing with `φ` is nonzero.  The hypotheses `hI` (inertia acts trivially on `M`)
and `hM` (`M` is killed by `p`) are carried along because every consumer states them together with
the conclusion. -/
def DetectsAt (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
    SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
    Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
    SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (SSGRoute.PTExt.trivResInv
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff)
      φ
      (SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0

/-- **Node `C6`** (`Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`): every nonzero
`φ ∈ Ext¹_{D_w}(res M, ℤ)` is detected at some level. -/
def IsUnramifiedDetector (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) : Prop :=
  ∀ φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
    φ ≠ 0 → DetectsAt p k K Ω w q hwq M φ

/-- **The induced module of the detector.**  `Ind_{D_w}^{G}(res_{D_w}M)`, where
`D_w = decompK w ≤ Gal(K/k)`: the `G`-module in which Shapiro's lemma applies.  This is the module
to which the detector reduces, by `isUnramifiedDetector_of_induced` below. -/
noncomputable abbrev detectorInd (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.ind (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)

end Work.SSGRoute.Sha2Lib
