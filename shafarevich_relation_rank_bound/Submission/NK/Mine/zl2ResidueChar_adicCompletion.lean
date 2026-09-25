import Mathlib
import Submission.NK.LocalTame.Inputs
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalCFT.All
import Submission.NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
import Submission.NK.LocalTame.zl2QuotientTransfer

/-!
# Shimizu's residue-characteristic detector at a `𝔭`-adic completion

The target of this file, `NK.Mine.zl2ResidueChar_adicCompletion`, derives Shimizu's
characterisation of the residue characteristic (`NK.LocalTame.Zl2ResidueChar`) at a `𝔭`-adic
completion `κ = K_𝔭` from

* an `ArtinReciprocity` datum `D` for `κ` and a separable closure `K'`, which by
  `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion` yields the infinite-level reciprocity
  isomorphism `κˣ^{∧} ≃* G_κ^{ab}`, where `G_κ^{ab} = Gal(κ^{ab}/κ)` is the *topological*
  abelianisation `Gal(K'/κ) ⧸ closure([G_κ,G_κ])` (`ker_abGalRestrict` below);
* openness of the index-`ℓ` normal subgroups of `G_κ` (Nikolov–Segal);
* the `ℤ_ℓ²`-quotient detector for the profinite completion of the unit group: `hunb` at `ℓ = p`
  and `hoth` for every `ℓ ≠ p`.

The two directions of the detector are therefore

* `ℓ = p`: `(ℤ/p^n)²`-quotients of `κˣ^{∧}` transfer to `Gal(K'/κ)` by composing with the
  surjection `Gal(K'/κ) ↠ G_κ^{ab}` (surjectivity of `AlgEquiv.restrictNormalHom`); this needs no
  openness;
* `ℓ ≠ p`: a surjection `Gal(K'/κ) ↠ (ℤ/ℓ^n)²` has abelian target, hence kills `[G_κ,G_κ]`, and
  its kernel must be closed for the map to descend to `G_κ^{ab}` — this is
  `NK.LocalTame.zl2QuotientTransfer`.
-/

open scoped Classical

namespace NK.Mine

noncomputable section

set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']

/-- **The restriction `Gal(K'/κ) →* G_κ^{ab}`.**  The canonical surjection of the absolute Galois
group onto the Galois group of the maximal abelian subextension `κ^{ab}`. -/
def abGalRestrict : Gal(K'/𝔭.adicCompletion K) →* NK.LocalCFT.AbGal (𝔭.adicCompletion K) K' :=
  AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K')
    ↥(NK.LocalReciprocity.maxAbelianSubext (𝔭.adicCompletion K) K')

/-- The restriction to the maximal abelian subextension is surjective (every element of
`Gal(κ^{ab}/κ)` extends to `K'`, since `K'/κ` is Galois). -/
theorem abGalRestrict_surjective : Function.Surjective (abGalRestrict 𝔭 K') := by
  unfold abGalRestrict
  exact AlgEquiv.restrictNormalHom_surjective (F := 𝔭.adicCompletion K)
    (K₁ := ↥(NK.LocalReciprocity.maxAbelianSubext (𝔭.adicCompletion K) K')) K'

/-- **The kernel of the restriction is the closure of the commutator subgroup**: `G_κ^{ab}` is the
*topological* abelianisation `Gal(K'/κ) ⧸ closure([G_κ,G_κ])`. -/
theorem ker_abGalRestrict : (abGalRestrict 𝔭 K').ker =
    (commutator (Gal(K'/𝔭.adicCompletion K))).topologicalClosure := by
  unfold abGalRestrict
  rw [IntermediateField.restrictNormalHom_ker]
  rw [NK.LocalReciprocity.maxAbelianSubext]
  exact NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
    (commutator (Gal(K'/𝔭.adicCompletion K)))

/-- The isomorphism `Gal(K'/κ) ⧸ closure([G_κ,G_κ]) ≃* G_κ^{ab}` of the topological abelianisation
with the Galois group of the maximal abelian subextension. -/
def quotientTopologicalClosureCommEquivAbGal :
    (Gal(K'/𝔭.adicCompletion K) ⧸
        (commutator (Gal(K'/𝔭.adicCompletion K))).topologicalClosure) ≃*
      NK.LocalCFT.AbGal (𝔭.adicCompletion K) K' :=
  (QuotientGroup.quotientMulEquivOfEq (ker_abGalRestrict 𝔭 K').symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (abGalRestrict 𝔭 K')
      (abGalRestrict_surjective 𝔭 K'))

/-- **The `ℤ_ℓ²`-quotient detector passes from `G_κ^{ab}` up to `G_κ`**: any quotient of the
abelianisation is a quotient of the group, by composition with the restriction map. -/
theorem hasZl2Quotient_of_hasZl2Quotient_abGal {ℓ : ℕ}
    (h : NK.LocalTame.HasZl2Quotient ℓ (NK.LocalCFT.AbGal (𝔭.adicCompletion K) K')) :
    NK.LocalTame.HasZl2Quotient ℓ (Gal(K'/𝔭.adicCompletion K)) :=
  fun n hn => by
    obtain ⟨f, hf⟩ := h n hn
    exact ⟨f.comp (abGalRestrict 𝔭 K'), hf.comp (abGalRestrict_surjective 𝔭 K')⟩

/-- **The `ℤ_ℓ²`-quotient detector passes from the unit completion to `G_κ`** (the `ℓ = p`
direction of `detects`): a quotient of `κˣ^{∧}` is a quotient of `G_κ^{ab}` by infinite-level
reciprocity, and hence of `G_κ`. -/
theorem hasZl2Quotient_of_hasZl2Quotient_completionUnits {ℓ : ℕ}
    (Φ : NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K) ≃*
      NK.LocalCFT.AbGal (𝔭.adicCompletion K) K')
    (h : NK.LocalTame.HasZl2Quotient ℓ
      (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K))) :
    NK.LocalTame.HasZl2Quotient ℓ (Gal(K'/𝔭.adicCompletion K)) := by
  refine hasZl2Quotient_of_hasZl2Quotient_abGal 𝔭 K' ?_
  intro n hn
  obtain ⟨f, hf⟩ := h n hn
  exact ⟨f.comp Φ.symm.toMonoidHom, hf.comp Φ.symm.surjective⟩

/-- **The `ℤ_ℓ²`-quotient detector passes from `G_κ` down to the unit completion** (the `ℓ ≠ p`
direction of `detects`), given openness of the index-`ℓ` normal subgroups: this is the transfer
`NK.LocalTame.zl2QuotientTransfer`, transported along
`Gal(K'/κ) ⧸ closure([G_κ,G_κ]) ≃* G_κ^{ab} ≃* κˣ^{∧}`. -/
theorem hasZl2Quotient_completionUnits_of_hasZl2Quotient {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hopenℓ : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = ℓ → H.Normal →
      IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))))
    (Φ : NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K) ≃*
      NK.LocalCFT.AbGal (𝔭.adicCompletion K) K')
    (h : NK.LocalTame.HasZl2Quotient ℓ (Gal(K'/𝔭.adicCompletion K))) :
    NK.LocalTame.HasZl2Quotient ℓ
      (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) := by
  intro n hn
  obtain ⟨f, hf⟩ :=
    NK.LocalTame.zl2QuotientTransfer (G := Gal(K'/𝔭.adicCompletion K)) hℓ hopenℓ h n hn
  refine ⟨(f.comp (quotientTopologicalClosureCommEquivAbGal 𝔭 K').symm.toMonoidHom).comp
    Φ.toMonoidHom, ?_⟩
  exact (hf.comp (quotientTopologicalClosureCommEquivAbGal 𝔭 K').symm.surjective).comp
    Φ.surjective

theorem zl2ResidueChar_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (D : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')
    (hopen : ∀ (ℓ : ℕ), ℓ.Prime → ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)),
      H.index = ℓ → H.Normal → IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))))
    (hunb : NK.LocalTame.HasZl2Quotient p
      (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)))
    (hoth : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ¬ NK.LocalTame.HasZl2Quotient ℓ
        (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K))) :
    NK.LocalTame.Zl2ResidueChar p (𝔭.adicCompletion K) K' := by
  obtain ⟨Φ⟩ := NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D
  refine ⟨hp, fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · intro hZ
    by_contra hne
    have hbad := hoth ℓ hℓ hne
    obtain ⟨n, hn, hnf⟩ : ∃ n : ℕ, 0 < n ∧
        ¬ ∃ f : NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K) →*
            (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n))),
          Function.Surjective f := by
      by_contra hcon
      exact hbad fun n hn => by
        by_contra h2
        exact hcon ⟨n, hn, h2⟩
    exact hnf (hasZl2Quotient_completionUnits_of_hasZl2Quotient 𝔭 K' hℓ (hopen ℓ hℓ) Φ hZ n hn)
  · rintro rfl
    exact hasZl2Quotient_of_hasZl2Quotient_completionUnits 𝔭 K' Φ hunb

end

end NK.Mine
