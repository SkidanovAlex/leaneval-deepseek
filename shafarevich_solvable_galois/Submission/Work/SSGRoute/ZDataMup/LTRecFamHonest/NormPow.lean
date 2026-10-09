import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormFinite
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormInfinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A local `p`-th power is a local norm

For a finite Galois extension `L/K` of number fields of prime degree `p` and any place `v` of `K`,
every `p`-th power in the local field `K_vˣ` is a local norm: this is
`mem_localNormSubgroup_of_mem_powRange`.

Consequence used in the `LTRecFamHonest` lane: the local factor `θ_𝔭` of the abelian Artin map
kills a global element which is a local `p`-th power at `𝔭` (`hLocalFactor_eq_one_of_mem_powRange`),
which is the well-definedness of the pairing in the lifts.
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open _root_.SSGRoute
open Classical

noncomputable section

set_option linter.unusedSectionVars false

/-- **A local `p`-th power is a local norm.** -/
theorem mem_localNormSubgroup_of_mem_powRange {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (hcard : Nat.card (L ≃ₐ[K] L) = p) (v : NK.GlobalCFT.Place K)
    (a : (NK.GlobalCFT.Place.localField K v)ˣ)
    (ha : a ∈ (powMonoidHom p :
      (NK.GlobalCFT.Place.localField K v)ˣ →* (NK.GlobalCFT.Place.localField K v)ˣ).range) :
    a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  rcases v with w | Q
  · rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
    obtain ⟨w', hw'⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := L) w
    haveI hw'L : w'.LiesOver w := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w' w).mpr hw'
    refine Subgroup.mem_iSup_of_mem (⟨w', hw'L⟩ :
      {w' : NumberField.InfinitePlace L // w'.LiesOver w}) ?_
    obtain ⟨u, hu⟩ :=
      NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormInfinite
        (K := K) (L := L) Fact.out hcard w w' (x := a) ha
    exact MonoidHom.mem_range.mpr ⟨u, hu⟩
  · rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    refine Subgroup.mem_iSup_of_mem (⟨q, hq⟩ :
      {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
        q.asIdeal.LiesOver Q.asIdeal}) ?_
    obtain ⟨u, hu⟩ :=
      NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow_mem_localNormFinite
        (K := K) (L := L) Fact.out hcard Q q hq (x := a) ha
    exact MonoidHom.mem_range.mpr ⟨u, hu⟩

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
