import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
import Submission.Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two elementary place-theoretic API lemmas, at a *low* position in the import order

`Work.SSGRoute.TPatom.concentrationClause` needs exactly two elementary facts about places:

* `isInertiaAt_galRes` — inertia descends along the restriction `Gal(L/k) → Gal(K/k)`;
* `decompK_le_fixingSubgroup_iff_split` — the decomposition group at a place lies in the fixing
  subgroup of an intermediate Galois field `F` exactly when `F` splits completely at that place.

On disk both live in `Submission/Work/SSGcrux/noninvariantLevelDatum.lean`, which (**2026-10-07,
11:02**) also imports `Submission.Work.SSGcrux.concentratedLevelData`, and `concentratedLevelData`
imports `TPatom.concentrationClause`: hence a three-module import cycle

    SSGcrux.noninvariantLevelDatum → SSGcrux.concentratedLevelData
      → TPatom.concentrationClause → SSGcrux.noninvariantLevelDatum

which breaks `lake build` for every module whose cone reaches it (including
`Submission.Work.SSGRoute.sha2_image_of_Hm2` and `Submission.Solution`).

This file provides the *same two lemmas*, proved, in the low-level namespace
`Work.SSGRoute.Sha2Lib` — with no dependency on `SSGcrux.noninvariantLevelDatum`,
`SSGcrux.concentratedLevelData` or `TPatom.concentrationClause`.  Swapping

    import Submission.Work.SSGcrux.noninvariantLevelDatum
    ...
    Work.SSGcrux.decompK_le_fixingSubgroup_iff_split

for

    import Submission.Work.SSGRoute.Sha2Lib.noninvariantLevelApi
    ...
    Work.SSGRoute.Sha2Lib.decompK_le_fixingSubgroup_iff_split

in `TPatom/concentrationClause.lean` (the only use of the two names is line 194) breaks the cycle
without changing any mathematics.
-/

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField

/-- **Inertia descends along restriction.**  If `γ ∈ Gal(L/k)` is inertial at a prime `q'` of `L`
lying over the prime `q` of `K`, then its restriction `galRes k K L γ ∈ Gal(K/k)` is inertial at
`q`. -/
theorem isInertiaAt_galRes {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (γ : L ≃ₐ[k] L) (hγ : SSGRoute.PTExt.IsInertiaAt q' γ) :
    SSGRoute.PTExt.IsInertiaAt (k := k) q (SSGRoute.PTExt.galRes k K L γ) := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  exact SSGRoute.E9Nodes.e9_inertia_restrict k K L q q' hq' γ (SSGRoute.PTExt.galRes k K L γ)
    (fun x => (AlgEquiv.restrictNormal_commutes γ K x).symm) hγ

/-- **The decomposition group is contained in the fixing subgroup of `F` iff `F` splits
completely at the place.** -/
theorem decompK_le_fixingSubgroup_iff_split {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [FiniteDimensional K F] [IsGalois K F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hQ : Q.asIdeal.LiesOver q.asIdeal) :
    SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q) ≤ F.fixingSubgroup ↔
      ((Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).ramificationIdx
          (NumberField.RingOfIntegers K) = 1 ∧
        (Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).inertiaDeg
          (NumberField.RingOfIntegers K) = 1) := by
  haveI : Normal K ↥F := inferInstance
  let q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F) :=
    ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥F), inferInstance,
      Ideal.under_ne_bot _ Q.ne_bot⟩
  have hq'eq : q'.asIdeal = Q.asIdeal.under (NumberField.RingOfIntegers ↥F) := rfl
  have hq'q : q'.asIdeal.LiesOver q.asIdeal := by
    haveI : Q.asIdeal.LiesOver q'.asIdeal := by
      rw [hq'eq]; exact Ideal.over_under Q.asIdeal
    haveI : Q.asIdeal.LiesOver q.asIdeal := hQ
    exact Ideal.LiesOver.tower_bot Q.asIdeal q'.asIdeal q.asIdeal
  have hliesF : Q.asIdeal.LiesOver q'.asIdeal := by
    rw [hq'eq]; exact Ideal.over_under Q.asIdeal
  have hbridge : SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q :=
    Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup (K := K) Q
  rw [hbridge]
  have hker : F.fixingSubgroup
      = (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F).ker :=
    (IntermediateField.restrictNormalHom_ker (K := K) F).symm
  rw [hker, ← Subgroup.map_eq_bot_iff]
  have hmap : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q' := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact Commons.NumberTheory.NumberField.Completion.restrictNormalHom_mem_decompositionSubgroup
        F Q q' hq'eq hσ
    · intro τ hτ
      obtain ⟨σ, hσ⟩ :=
        Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
          (K := K) (M := L) F q' Q hq'eq hliesF ⟨τ, hτ⟩
      exact ⟨σ, σ.2, hσ⟩
  rw [hmap,
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) q q' hq'q]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F),
      Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F)]

end Work.SSGRoute.Sha2Lib
