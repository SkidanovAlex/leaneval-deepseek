import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.chebotarev_place_zpowers_unram_disj
import Submission.Work.SSGRoute.exists_T0_split_generating
import Submission.Work.SSGRoute.placePrime_eq_of_isConjPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `T⁰`-places: finiteness, complete splitting, generation, cyclicity — with disjointness

This file proves `Work.SSGRoute.exists_T0_split_generating_disj`, the refinement of
`Work.SSGRoute.exists_T0_split_generating` in which the places of `T⁰` are moreover pairwise
non-conjugate and in which the inertia groups of the places of `T⁰` are killed by `ψ` (i.e. the
rational primes below the places of `T⁰` are unramified in the field `L` cut out by `ker ψ`).

The construction is the one of `Work.SSGRoute.exists_T0_split_generating`, run along the *elements*
`σ ∈ H_L = (flowEKer.comap ψ).map (restrictNormalHom L)` with Čebotarev *with avoidance*: for
`σ ∈ H_L` one chooses a place `A_σ` whose rational prime is a prime `p_σ` realising `σ` as a
Frobenius element (`Work.SSGRoute.chebotarev_place_zpowers_unram_disj`), at which `σ` is moreover
unramified in `L` (giving the inertia clause) and whose rational prime avoids the primes already
used.  Distinct rational primes give non-conjugate places
(`Work.SSGRoute.placePrime_eq_of_isConjPlace`).

Čebotarev's input in the avoided form is `NK.WeakNU.ChebotarevFrobeniusInput`, which is available
unconditionally from the fundamental class element (`chebotarevFrobeniusInput_hFC`).
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open _root_.SSGRoute

open scoped Pointwise

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- **Čebotarev's theorem in existence form with avoidance**, from the fundamental class element
of global class field theory: for every finite Galois extension `N/ℚ`, every `σ : Gal(N/ℚ)` and
every finite set `T` of rational primes there are a rational prime `p ∉ T`, unramified in `N`, and
a prime `P` of `𝓞 N` above `p` at which `σ` is a Frobenius element. -/
theorem chebotarevFrobeniusInput_hFC (_hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    NK.WeakNU.ChebotarevFrobeniusInput :=
  NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian
    (NK.NUV2.abelianChebotarevDensity_of_freeInputs NK.NUV2.heckeInput_proved
      (NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
        (NK.NUV2.artinReciprocityIdeal_of_auxField
          (fun K L _ _ _ _ _ _ _ _ _ m hm => NK.NUV2.ChebAux.kernelLe_of_auxField K L m hm)
          (fun K L _ _ _ _ _ _ _ _ m hm => NK.CFTLib.ARL.auxField_exists_B K L m hm))))

theorem exists_T0_split_generating_disj (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hLift : SSGRoute.LiftsFlow ψ φ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hsurj : Function.Surjective ψ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T0, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = Work.SSGRoute.flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) ∧
      (∀ A ∈ T0, ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → ψ σ = 1) ∧
      (∀ A ∈ T0, ∀ B ∈ T0, SSGRoute.IsConjPlace ℚ A B → A = B) := by
  classical
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hC : NK.WeakNU.ChebotarevFrobeniusInput :=
    chebotarevFrobeniusInput_hFC NK.CFTLib.fundamentalClassElement
  have hclosed : IsClosed (ψ.ker : Set SSGRoute.GalQ) := Subgroup.isClosed_of_isOpen ψ.ker hopen
  let L : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField ψ.ker
  have hLfix : L.fixingSubgroup = ψ.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [L] using h
  have hLfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) L).mp (hLfix ▸ hopen)
  haveI hLfdI : FiniteDimensional ℚ L := hLfd
  haveI hLgal : IsGalois ℚ L :=
    IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := AlgebraicClosure ℚ) ψ.ker
      (hn := MonoidHom.normal_ker ψ)
  haveI hLnf : NumberField ↥L := inferInstance
  have hrker : (AlgEquiv.restrictNormalHom L).ker = ψ.ker := by
    rw [IntermediateField.restrictNormalHom_ker, hLfix]
  obtain ⟨ψbar, hψbar⟩ := t0_restrictLift L ψ hrker.symm
  let HL : Subgroup (↥L ≃ₐ[ℚ] ↥L) :=
    ((flowEKer p (K ≃ₐ[ℚ] K) n i j).comap ψ).map (AlgEquiv.restrictNormalHom L)
  have hHmap : HL.map ψbar = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
    show Subgroup.map ψbar (Subgroup.map (AlgEquiv.restrictNormalHom L)
      (Subgroup.comap ψ (flowEKer p (K ≃ₐ[ℚ] K) n i j))) =
        flowEKer p (K ≃ₐ[ℚ] K) n i j
    rw [Subgroup.map_map, hψbar, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj,
      top_inf_eq]
  haveI : Fintype (↥L ≃ₐ[ℚ] ↥L) := Fintype.ofFinite _
  -- the recursive choice of the places
  have key : ∀ S : Finset ↥HL, ∃ A : ↥HL → NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar,
      (∀ s ∈ S, ¬ SSGRoute.IsRamifiedIn ℚ L (A s).1) ∧
      (∀ s ∈ S, (SSGRoute.decomp ℚ (A s).1).map (AlgEquiv.restrictNormalHom L) =
        Subgroup.zpowers (s : ↥L ≃ₐ[ℚ] ↥L)) ∧
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
        Work.SSGRoute.placePrime (A s).1 (A s).2 ≠
          Work.SSGRoute.placePrime (A s').1 (A s').2) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · obtain ⟨A₀, hA₀, -, -, -⟩ :=
        chebotarev_place_zpowers_unram_disj hC L (1 : ↥L ≃ₐ[ℚ] ↥L) ∅
      exact ⟨fun _ => ⟨A₀, hA₀⟩, by simp, by simp, by simp⟩
    · intro a S ha ih
      obtain ⟨A, hram, hzp, hdisj⟩ := ih
      set T : Finset ℕ := S.image (fun s => (Work.SSGRoute.placePrime (A s).1 (A s).2).1)
        with hT
      obtain ⟨B, hB, hBprime, hBram, hBzp⟩ :=
        chebotarev_place_zpowers_unram_disj hC L (a : ↥L ≃ₐ[ℚ] ↥L) T
      refine ⟨Function.update A a ⟨B, hB⟩, ?_, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · rw [Function.update_self]; exact hBram
        · rw [Function.update_of_ne (by rintro rfl; exact ha hs)]; exact hram s hs
      · intro s hs
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · rw [Function.update_self]; exact hBzp
        · rw [Function.update_of_ne (by rintro rfl; exact ha hs)]; exact hzp s hs
      · intro s hs s' hs' hne
        rw [Finset.mem_insert] at hs hs'
        rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
        · exact absurd rfl hne
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hs')]
          intro hcontra
          exact hBprime (by
            rw [hT, Finset.mem_image]
            exact ⟨s', hs', congrArg Subtype.val hcontra.symm⟩)
        · rw [Function.update_of_ne (by rintro rfl; exact ha hs), Function.update_self]
          intro hcontra
          exact hBprime (by
            rw [hT, Finset.mem_image]
            exact ⟨s, hs, congrArg Subtype.val hcontra⟩)
        · rw [Function.update_of_ne (by rintro rfl; exact ha hs),
              Function.update_of_ne (by rintro rfl; exact ha hs')]
          exact hdisj s hs s' hs' hne
  obtain ⟨Afun, hram, hzp, hdisj⟩ := key Finset.univ
  refine ⟨Finset.univ.image (fun s : ↥HL => (Afun s).1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨s, -, rfl⟩ := hA
    exact (Afun s).2
  · intro A hA σ hσ
    rw [Finset.mem_image] at hA
    obtain ⟨s, -, rfl⟩ := hA
    have hmem : ψ σ ∈ flowEKer p (K ≃ₐ[ℚ] K) n i j := by
      have hmap : (SSGRoute.decomp ℚ (Afun s).1).map ψ =
          Subgroup.zpowers (ψbar (s : ↥L ≃ₐ[ℚ] ↥L)) := by
        rw [← hψbar, ← Subgroup.map_map, hzp s (Finset.mem_univ s), t0_map_zpowers]
      have h2 : ψ σ ∈ Subgroup.zpowers (ψbar (s : ↥L ≃ₐ[ℚ] ↥L)) := by
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
      exact Subgroup.zpowers_le.mpr (by
        rw [← hHmap]
        exact Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩) h2
    rw [← flowGroupProj_eq_of_liftsFlowAt_SSGRoute p K (hLift σ)]
    exact MonoidHom.mem_ker.mp hmem
  · rw [← Finset.sup_eq_iSup, Finset.sup_image]
    show Finset.univ.sup (fun s : ↥HL => (SSGRoute.decomp ℚ (Afun s).1).map ψ) =
      flowEKer p (K ≃ₐ[ℚ] K) n i j
    have hfun : (fun s : ↥HL => (SSGRoute.decomp ℚ (Afun s).1).map ψ) =
        (fun s : ↥HL => Subgroup.zpowers (ψbar (s : ↥L ≃ₐ[ℚ] ↥L))) := by
      funext s
      rw [← hψbar, ← Subgroup.map_map, hzp s (Finset.mem_univ s), t0_map_zpowers]
    rw [hfun]
    apply le_antisymm
    · apply Finset.sup_le
      intro s _
      exact Subgroup.zpowers_le.mpr (by
        rw [← hHmap]
        exact Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩)
    · intro x hx
      rw [← hHmap, Subgroup.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact Finset.le_sup (f := fun s : ↥HL => Subgroup.zpowers (ψbar (s : ↥L ≃ₐ[ℚ] ↥L)))
        (Finset.mem_univ ⟨s, hs⟩) (Subgroup.mem_zpowers (ψbar (s : ↥L ≃ₐ[ℚ] ↥L)))
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨s, -, rfl⟩ := hA
    rw [← hψbar, ← Subgroup.map_map, hzp s (Finset.mem_univ s), t0_map_zpowers]
    infer_instance
  · intro A hA σ hσ
    rw [Finset.mem_image] at hA
    obtain ⟨s, -, rfl⟩ := hA
    have hfix : σ ∈ L.fixingSubgroup := by
      by_contra hcon
      exact hram s (Finset.mem_univ s) ⟨σ, hσ, hcon⟩
    rw [hLfix] at hfix
    exact MonoidHom.mem_ker.mp hfix
  · intro A hA B hB hconj
    rw [Finset.mem_image] at hA hB
    obtain ⟨s, -, rfl⟩ := hA
    obtain ⟨s', -, rfl⟩ := hB
    by_cases hss : s = s'
    · rw [hss]
    · exact absurd (placePrime_eq_of_isConjPlace (Afun s).2 (Afun s').2 hconj)
        (hdisj s (Finset.mem_univ s) s' (Finset.mem_univ s') hss)

end Work.SSGRoute
