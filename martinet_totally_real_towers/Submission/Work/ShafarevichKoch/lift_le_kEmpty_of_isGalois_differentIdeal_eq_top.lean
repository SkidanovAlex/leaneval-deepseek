import Mathlib
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv

/-!
# `Work.ShafarevichKoch.lift_le_kEmpty_of_isGalois_differentIdeal_eq_top`

**A finite Galois pro-`2` level of `k_S` which is unramified over `F` lies in `k_∅`.**

Given a finite Galois subextension `K / F` of the maximal pro-`2` extension `k_S` of `F` unramified
outside `S`, with pro-`2` Galois group and **trivial relative different** (unramified at every finite
prime), the image of `K` in `k_S` (i.e. `IntermediateField.lift K`) is contained in the image
`kEmptyInS F 2 S` of the maximal everywhere-unramified pro-`2` extension `k_∅` inside `k_S`.

The proof transports the finite level `K ≤ k_S/F` to the algebraic closure
(`M = (lift K).map val`, isomorphic to `K` by `K ≃ lift K ≃ M`), which preserves
finite-dimensionality, Galois-ness, the pro-`2` property of the Galois group
(`AlgEquiv.autCongr`) and triviality of the different
(`Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv`), and then applies
`Work.ShafarevichKoch.le_kSupported_empty_of_unramified` (`M ≤ k_∅`) followed by the
Galois connection `map ⊣ comap` defining `kEmptyInS`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **A finite Galois pro-`2` level `K ≤ k_S` with trivial relative different is contained in the
image of `k_∅`.** -/
theorem lift_le_kEmpty_of_isGalois_differentIdeal_eq_top {F : Type} [Field F] [NumberField F]
    {S : Finset ℕ} {L : IntermediateField F ↥(Work.ShafarevichKoch.kSupported F 2 S)}
    (K : IntermediateField F ↥L) [FiniteDimensional F ↥K] [IsGalois F ↥K] [NumberField ↥K]
    (hpg : IsPGroup 2 (↥K ≃ₐ[F] ↥K))
    (hK : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥K) = ⊤) :
    IntermediateField.lift K ≤ Work.ShafarevichKoch.kEmptyInS F 2 S := by
  classical
  -- the image of `K` inside the algebraic closure of `F`
  let M : IntermediateField F (AlgebraicClosure F) :=
    (IntermediateField.lift K).map (IntermediateField.val (kSupported F 2 S))
  -- `K` is `F`-isomorphic to its image in the algebraic closure
  have e₁ : ↥K ≃ₐ[F] ↥(IntermediateField.lift K) := IntermediateField.liftAlgEquiv K
  have e₂ : ↥(IntermediateField.lift K) ≃ₐ[F] ↥M :=
    IntermediateField.equivMap (IntermediateField.lift K) (IntermediateField.val (kSupported F 2 S))
  let e : ↥K ≃ₐ[F] ↥M := e₁.trans e₂
  -- the three structural properties transfer along the isomorphism
  haveI : FiniteDimensional F ↥M := Module.Finite.of_surjective e.toLinearMap e.surjective
  haveI : IsGalois F ↥M := IsGalois.of_algEquiv e
  haveI : NumberField ↥M := NumberField.of_ringEquiv ↥K ↥M e.toRingEquiv
  have hpgM : IsPGroup 2 (↥M ≃ₐ[F] ↥M) := IsPGroup.of_equiv hpg (AlgEquiv.autCongr e)
  -- and so does triviality of the relative different
  have hunr : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥M) = ⊤ :=
    Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv e hK
  -- hence the image of `K` is inside `k_∅`
  have hMle : M ≤ kSupported F 2 (∅ : Finset ℕ) :=
    le_kSupported_empty_of_unramified (F := F) (p := 2) (L := M) hpgM hunr
  -- `kEmptyInS` is the preimage of `k_∅` under the inclusion of `k_S`, so the Galois connection
  -- `map ⊣ comap` turns the goal into `(lift K).map val ≤ k_∅`
  change IntermediateField.lift K ≤ (kSupported F 2 (∅ : Finset ℕ)).comap
    (IntermediateField.val (kSupported F 2 S))
  rw [← IntermediateField.map_le_iff_le_comap]
  exact hMle

end Work.ShafarevichKoch
