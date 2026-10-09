import Mathlib
import Submission.Work.SSGRoute.PT.pt_unramifiedSub
import Submission.Work.SSGRoute.PT.vanishingInertia_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Localisation of a global cocycle into the restricted product of the local `H¹`'s

This module supplies the localisation step of the relaxed Poitou–Tate instantiation
(`Work.SSGRoute.PT.restrictedProduct_relaxation` applied to the arithmetic data): the element of
the restricted product `Πʳ_v [H¹(D_v, M), H¹_ur(D_v, M)]` attached to a global locally constant
cocycle `b`.

**The index type.**  The restricted product must be indexed by the primes of `k`, not by the places
of `Ω`: the cofinite condition "unramified outside a finite set" would be false for the latter,
since the bad set is a union of full `Gal(Ω/k)`-orbits, each infinite as soon as it is non-empty.
Accordingly the index type here is `FinPlaceClass k Ω`, the quotient of the finite places of `Ω` by
`IsConjPlace`, and the local data are read off at the canonical representative `Quot.out i`.  (The
result is independent of the chosen representative, by
`Work.SSGRoute.toClass_mem_unramifiedSub_conj`, `PT/unramifiedSub_conj.lean`.)

**The result.**  For every global locally constant cocycle `b` there is an element `x` of the
restricted product whose `i`-th component is the local class of `b` at the representative of `i`.
The "almost everywhere" condition is exactly `Work.SSGRoute.PT.vanishingInertia_finite` (a global
locally constant cocycle vanishes on the inertia of all but finitely many finite places, up to
conjugacy) fed into the bridge `Work.SSGRoute.toClass_mem_unramifiedSub_of_inertia_eq_zero`.
-/

namespace Work.SSGRoute.PT

set_option linter.unusedSectionVars false

noncomputable section

open scoped RestrictedProduct
open _root_.SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **Conjugacy of finite places of `Ω`**, as a setoid on the subtype of finite places.  Its
quotient is the type of *primes of `k`* (each represented by a place of `Ω` above it). -/
def finPlaceConjSetoid : Setoid {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A} where
  r A B := SSGRoute.IsConjPlace k A.1 B.1
  iseqv := ⟨fun A => isConjPlace_refl A.1, fun h => isConjPlace_symm h,
    fun h₁ h₂ => isConjPlace_trans h₁ h₂⟩

/-- **Localisation of a global locally constant cocycle into the restricted product** over the
finite places of `Ω` up to conjugacy, with the unramified subgroups as the "unramified" family. -/
theorem exists_restrictedProduct_localization {b : (Ω ≃ₐ[k] Ω) → M}
    (hb : b ∈ lcCocycles p k Ω K M ⊤) :
    ∃ x : Πʳ i : Quotient (finPlaceConjSetoid k Ω),
        [H1loc p k Ω K M (SSGRoute.decomp k (Quotient.out i).1),
          unramifiedSub p k Ω K M (Quotient.out i).1],
      ∀ i : Quotient (finPlaceConjSetoid k Ω),
        x i = toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b := by
  classical
  -- a finite set of places, one per class, outside which `b` vanishes on inertia
  obtain ⟨S, hSfin, hSdisj, hS0⟩ :=
    Work.SSGRoute.PT.vanishingInertia_finite k Ω K M b hb.1 hb.2
  -- the finitely many classes represented in `S`
  set F : Finset (Quotient (finPlaceConjSetoid k Ω)) :=
    S.attach.image (fun A => Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩) with hF
  have hgood : ∀ i : Quotient (finPlaceConjSetoid k Ω), i ∉ F →
      toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b ∈
        unramifiedSub p k Ω K M (Quotient.out i).1 := by
    intro i hi
    have hnot : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A (Quotient.out i).1 := by
      intro A hA hconj
      have h1 : Quotient.mk (finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩ =
          Quotient.mk (finPlaceConjSetoid k Ω) (Quotient.out i) := Quotient.sound hconj
      have h2 : Quotient.mk (finPlaceConjSetoid k Ω) (Quotient.out i) = i := Quotient.out_eq i
      exact hi (by
        rw [hF]
        refine Finset.mem_image.mpr ⟨(⟨A, hA⟩ : {A // A ∈ S}), Finset.mem_attach S ⟨A, hA⟩, ?_⟩
        exact h1.trans h2)
    have hmem : b ∈ lcCocycles p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hb.1, isLocConstOn_mono le_top hb.2⟩
    exact toClass_mem_unramifiedSub_of_inertia_eq_zero (p := p) (k := k) (Ω := Ω) (K := K)
      (M := M) (B := (Quotient.out i).1) hmem
      (fun σ hσ => hS0 (Quotient.out i).1 (Quotient.out i).2 hnot σ hσ)
  have hfinite : ({i : Quotient (finPlaceConjSetoid k Ω) |
      toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b ∉
        unramifiedSub p k Ω K M (Quotient.out i).1}).Finite := by
    refine (F.finite_toSet).subset ?_
    intro i hi
    by_contra hcon
    exact hi (hgood i hcon)
  refine ⟨RestrictedProduct.mk
    (R := fun i : Quotient (finPlaceConjSetoid k Ω) =>
      H1loc p k Ω K M (SSGRoute.decomp k (Quotient.out i).1))
    (A := fun i : Quotient (finPlaceConjSetoid k Ω) =>
      (unramifiedSub p k Ω K M (Quotient.out i).1 :
        Set (H1loc p k Ω K M (SSGRoute.decomp k (Quotient.out i).1))))
    (fun i : Quotient (finPlaceConjSetoid k Ω) =>
      toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b)
    ((Filter.eventually_cofinite).mpr hfinite), fun i => ?_⟩
  rw [RestrictedProduct.mk_apply]

/-- **Additivity of the localisation**: the localisation of a sum of two global locally constant
cocycles is the sum of their localisations, componentwise.  (Together with
`exists_restrictedProduct_localization` this says that the localisation is a group homomorphism
`Z¹_loc → Πʳ_v [H¹(D_v, M), H¹_ur(D_v, M)]`.) -/
theorem exists_restrictedProduct_localization_add {b₁ b₂ : (Ω ≃ₐ[k] Ω) → M}
    (h₁ : b₁ ∈ lcCocycles p k Ω K M ⊤) (h₂ : b₂ ∈ lcCocycles p k Ω K M ⊤) :
    ∃ x : Πʳ i : Quotient (finPlaceConjSetoid k Ω),
        [H1loc p k Ω K M (SSGRoute.decomp k (Quotient.out i).1),
          unramifiedSub p k Ω K M (Quotient.out i).1],
      ∀ i : Quotient (finPlaceConjSetoid k Ω),
        x i = toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b₁ +
          toClass p k Ω K M (SSGRoute.decomp k (Quotient.out i).1) b₂ := by
  obtain ⟨x, hx⟩ := exists_restrictedProduct_localization (p := p) (k := k) (Ω := Ω) (K := K)
    (M := M) (b := b₁ + b₂) ((lcCocycles p k Ω K M ⊤).add_mem h₁ h₂)
  refine ⟨x, fun i => ?_⟩
  rw [hx i]
  exact toClass_add p k Ω K M (SSGRoute.decomp k (Quotient.out i).1)
    ⟨isCocycleOn_mono (SSGRoute.res k K) le_top h₁.1,
      isLocConstOn_mono le_top h₁.2⟩
    ⟨isCocycleOn_mono (SSGRoute.res k K) le_top h₂.1,
      isLocConstOn_mono le_top h₂.2⟩

end

end Work.SSGRoute.PT
