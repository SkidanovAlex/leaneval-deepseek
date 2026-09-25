import Mathlib
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.NKHerbrand
import Submission.Work.CFTLib.subsingleton_tateCohomology_neg_one_localUnitIdeles
import Submission.Work.CFTLib.natCard_tateCohomology_localUnitIdelesRep
import Submission.Work.CFT.Ledger.tateCohomology_coind_zero_card

/-!
# `Ĥ⁰(Gal(K/F), ⊔_w U_w) = 0` for an unramified `K/F`

The target lemma `subsingleton_tateCohomology_localUnitIdeles_zero` states that the Tate
cohomology in degree `0` of the module of *local unit idèles* of `K` — the idèles all of whose
components are local units — vanishes when `K/F` is finite Galois and unramified (at every finite
place, with real places staying real).

This is the degree-`0` companion of `subsingleton_tateCohomology_neg_one_localUnitIdeles`, proved
along the same lines.

The proof decomposes the module of local unit idèles into the product, over the places `v` of
`F`, of the *unit parts of the fibres* `∏_{w | v} U_w`
(`NK.GlobalCFTdeep.fiberUnits v`), using `natCard_tateCohomology_localUnitIdelesRep`, and then
shows `Ĥ⁰` of each fibre vanishes:

* for `v` finite, the fibre is `Coind_{D_q}^G 𝒪_qˣ` (`fiberUnitsRep_iso_coind`) and
  `Ĥ⁰(D_q, 𝒪_qˣ) = 0` because `D_q` is the Galois group of the unramified local extension
  `K_q/F_Q` (`NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one`);
  Shapiro's lemma in degree `0` (`subsingleton_tateCohomology_zero_coind`, from
  `Work.CFT.Ledger.tateCohomology_coind_zero_card`) transfers this to `G`;
* for `v` infinite, the fibre is `∏_{w | v} K_wˣ` and the decomposition groups are trivial
  (unramifiedness at infinity), so Shapiro's lemma reduces to the trivial group, where `Ĥ⁰`
  always vanishes because the norm is the identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Classical
open NumberField NK.GlobalCFT CategoryTheory

noncomputable section

namespace Work.CFTLib

/-! ## Trivial groups have vanishing `Ĥ⁰` -/

/-- **For the trivial group, `Ĥ⁰` vanishes.**  If `G` is a subsingleton finite group and `M` is
any `ℤ[G]`-module, then `Ĥ⁰(G, M) = M^G / N M` is trivial: the norm `N = ∑_{g : G} g` is the
identity, so `M^G = N M = M`. -/
theorem subsingleton_tateCohomology_zero_of_subsingleton_group {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton ↥(tateCohomology M 0) := by
  have hnorm : ∀ y : M.V, Work.CFT.IdeleClassGroup.normMap M y = y := by
    intro y
    rw [Work.CFT.IdeleClassGroup.normMap_apply]
    have hcard : Fintype.card G = 1 := by
      haveI : Nonempty G := ⟨1⟩
      exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => Subsingleton.elim g 1⟩
    calc ∑ g : G, M.ρ g y = ∑ _g : G, y :=
          Finset.sum_congr rfl (fun g _ => by
            rw [Subsingleton.elim g (1 : G), map_one]; rfl)
      _ = Fintype.card G • y := Finset.sum_const y
      _ = y := by rw [hcard, one_smul]
  obtain ⟨e⟩ := Work.CFT.IdeleClassGroup.tateCohomology_zero_iso M
  haveI hquot : Subsingleton (Work.CFT.IdeleClassGroup.invariants M ⧸
      Work.CFT.IdeleClassGroup.norms M) := by
    rw [QuotientAddGroup.subsingleton_iff, eq_top_iff]
    intro x _
    rw [Work.CFT.IdeleClassGroup.norms, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
    exact ⟨x.1, hnorm x.1⟩
  exact e.injective.subsingleton

/-! ## Shapiro's lemma in degree `0`, in the form of vanishing -/

/-- **Vanishing of `Ĥ⁰` passes to a coinduced representation.**  For an injective homomorphism
`φ : G →* H` of finite groups and a `ℤ`-linear representation `A` of `G`, Shapiro's lemma in
degree `0` gives `Ĥ⁰(H, Coind_φ A) ≅ Ĥ⁰(G, A)`; hence `Ĥ⁰(G, A) = 0` implies
`Ĥ⁰(H, Coind_φ A) = 0`. -/
theorem subsingleton_tateCohomology_zero_coind {G H : Type} [Group G] [Group H]
    [Fintype G] [Fintype H] (φ : G →* H) (hφ : Function.Injective φ) (A : Rep ℤ G)
    (h : Subsingleton ↥(tateCohomology A 0)) :
    Subsingleton ↥(tateCohomology (Rep.coind φ A) 0) := by
  have h1 : Nat.card ↥(tateCohomology A 0) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨h, ⟨0⟩⟩
  have h2 := Work.CFT.Ledger.tateCohomology_coind_zero_card φ hφ A
  exact (Nat.card_eq_one_iff_unique.mp (h2.trans h1)).1

/-! ## The fibre at an infinite place has vanishing `Ĥ⁰` -/

/-- **`Ĥ⁰(G, ∏_{w | v} K_wˣ) = 0` for `v` infinite and `K/F` unramified at infinity.**  The
decomposition group `D_w` is trivial, so Shapiro's lemma
(`fiberIdelesRep_iso_coind`, `subsingleton_tateCohomology_zero_coind`) reduces the statement to
the trivial group, where `Ĥ⁰` always vanishes. -/
theorem subsingleton_tateCohomology_zero_fiberUnitsRep_ofInfinite {F K : Type} [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [IsUnramifiedAtInfinitePlaces F K] (v : InfinitePlace F) :
    Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)) 0) := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) v
  have hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v) :=
    NK.GlobalCFT.Place.liesOver_ofInfinite (K := F) (L := K) ⟨by rw [← hw]; rfl⟩
  haveI hsub : Subsingleton (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)) := subsingleton_decompositionSubgroup_ofInfinite w
  letI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)) := Fintype.ofFinite _
  obtain ⟨e2⟩ := NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind (K := F) (L := K)
    (NK.GlobalCFT.Place.ofInfinite v) (NK.GlobalCFT.Place.ofInfinite w) hw'
  haveI hq : Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.localUnitsRep (K := F)
      (L := K) (NK.GlobalCFT.Place.ofInfinite w)) 0) :=
    subsingleton_tateCohomology_zero_of_subsingleton_group _
  haveI : Subsingleton ↥(tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
      (NK.GlobalCFTdeep.localUnitsRep (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w))) 0) :=
    subsingleton_tateCohomology_zero_coind _ (fun a b h => Subtype.ext h) _ hq
  haveI hfid : Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)) 0) :=
    ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) 0).mapIso e2).toLinearEquiv.injective.subsingleton
  obtain ⟨e0⟩ := fiberUnitsRep_iso_fiberIdelesRep_ofInfinite (F := F) (K := K) v
  exact ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) 0).mapIso e0).toLinearEquiv.injective.subsingleton

/-! ## The fibre at a finite unramified place has vanishing `Ĥ⁰` -/

/-- **`Ĥ⁰(G, ∏_{w | v} 𝒪_wˣ) = 0` for a finite unramified place `v`.**  The fibre is the
coinduced module `Coind_{D_q}^G 𝒪_qˣ` (`fiberUnitsRep_iso_coind`), and `Ĥ⁰(D_q, 𝒪_qˣ) = 0` for an
unramified `q`
(`NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one`); Shapiro's
lemma in degree `0` transfers this to `G`. -/
theorem subsingleton_tateCohomology_zero_fiberUnitsRep_ofFinite {F K : Type} [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1) :
    Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite Q)) 0) := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  letI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite q)) := Fintype.ofFinite _
  obtain ⟨e⟩ := NK.GlobalCFTdeep.fiberUnitsRep_iso_coind (K := F) (L := K)
    (NK.GlobalCFT.Place.ofFinite Q) q (NK.GlobalCFT.Place.liesOver_ofFinite hq)
  have h0 : NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.localUnitSubRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one Q q hq hunr
  have h1 : Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite q)) 0) := by
    rw [NK.GlobalCFTdeep.hZero_def] at h0
    exact (Nat.card_eq_one_iff_unique.mp h0).1
  have h2 : Subsingleton ↥(tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (NK.GlobalCFTdeep.localUnitSubRep (K := F) (L := K)
        (NK.GlobalCFT.Place.ofFinite q))) 0) :=
    subsingleton_tateCohomology_zero_coind _ (fun a b h => Subtype.ext h) _ h1
  exact ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) 0).mapIso e).toLinearEquiv.injective.subsingleton

/-! ## The target -/

theorem subsingleton_tateCohomology_localUnitIdeles_zero {F K : Type} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hUnr : CFTLib.IsUnramified F K) :
    Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.localUnitIdelesRep (K := F) (L := K)) 0) := by
  haveI hinf : IsUnramifiedAtInfinitePlaces F K := hUnr.2
  have hprimes : Work.Tower.IsUnramifiedExtensionForallPrimes F K :=
    Work.CFTLib.forallPrimes_of_isUnramified hUnr
  have hfac : ∀ v : NK.GlobalCFT.Place F,
      Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) 0) := by
    intro v
    rcases v with w | Q
    · exact subsingleton_tateCohomology_zero_fiberUnitsRep_ofInfinite w
    · obtain ⟨P₀⟩ := (Ideal.nonempty_primesOver Q.asIdeal :
        Nonempty (Q.asIdeal.primesOver (NumberField.RingOfIntegers K)))
      let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
        ⟨P₀.1, P₀.2.1, Ideal.ne_bot_of_mem_primesOver Q.ne_bot P₀.2⟩
      exact subsingleton_tateCohomology_zero_fiberUnitsRep_ofFinite Q q P₀.2.2
        (hprimes q.asIdeal q.isPrime)
  have hsub : Subsingleton ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) 0) :=
    ⟨fun a b => funext fun v => Subsingleton.elim (a v) (b v)⟩
  have hne : Nonempty ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) 0) :=
    ⟨fun _ => 0⟩
  have h1 : Nat.card ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) 0) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩
  have hcard := natCard_tateCohomology_localUnitIdelesRep (K := F) (L := K) 0
  exact (Nat.card_eq_one_iff_unique.mp (hcard.trans h1)).1

end Work.CFTLib
