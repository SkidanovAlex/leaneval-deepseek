import Mathlib
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.NKHerbrand
import Submission.Work.CFTLib.subsingleton_tateCohomology_neg_one_coind
import Submission.Work.CFTLib.subsingleton_tateCohomology_neg_one_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.Work.CFTLib.natCard_tateCohomology_localUnitIdelesRep

/-!
# `Ĥ⁻¹(Gal(K/F), ⊔_w U_w) = 0` for an unramified `K/F`

The target lemma `subsingleton_tateCohomology_neg_one_localUnitIdeles` states that the Tate
cohomology in degree `-1` of the module of *local unit idèles* of `K` — the idèles all of whose
components are local units — vanishes when `K/F` is finite Galois and unramified (at every finite
place, with real places staying real).

The proof decomposes the module of local unit idèles into the product, over the places `v` of `F`,
of the *unit parts of the fibres* `∏_{w | v} U_w` (which is `NK.GlobalCFTdeep.fiberUnits v`), and
then shows `Ĥ⁻¹` of each fibre vanishes:

* for `v` finite, the fibre is `Coind_{D_q}^G 𝒪_qˣ` (`fiberUnitsRep_iso_coind`) and
  `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` because `D_q` is cyclic (unramified local extension) and
  `Ĥ¹(D_q, 𝒪_qˣ) = 0` (H¹ of the units of an unramified local extension);
* for `v` infinite, the fibre is `∏_{w | v} K_wˣ` and the decomposition groups are trivial
  (unramifiedness at infinity), so Shapiro's lemma reduces to the trivial group.

The decomposition over the places of `F` (`natCard_tateCohomology_localUnitIdelesRep`), Shapiro's
lemma in degree `-1` (`subsingleton_tateCohomology_neg_one_coind`) and the local finite-place
vanishing (`subsingleton_tateCohomology_neg_one_localUnitSubRep_of_ramificationIdx_eq_one`) are
proved separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical
open NumberField NK.GlobalCFT CategoryTheory

noncomputable section

namespace Work.CFTLib

/-! ## Trivial decomposition groups at infinite places -/

/-- **The decomposition group of an infinite place is trivial when `K/F` is unramified at
infinity.**  An infinite place of `K` is unramified over `F` exactly when its stabiliser in
`Gal(K/F)` is trivial (`NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one`), and
the stabiliser of an infinite place *is* its decomposition group. -/
theorem subsingleton_decompositionSubgroup_ofInfinite {F K : Type} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [IsUnramifiedAtInfinitePlaces F K] (w : InfinitePlace K) :
    Subsingleton (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)) := by
  have hstab : MulAction.stabilizer (K ≃ₐ[F] K) w =
      NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w) := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, NK.GlobalCFTdeep.mem_decompositionSubgroup,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
  have hcard : Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)) = 1 := by
    rw [← hstab]
    exact (NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one
      (k := F) (K := K) (w := w)).mp (NumberField.InfinitePlace.isUnramified F w)
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

/-- **For the trivial group, `Ĥ⁻¹` vanishes.**  If `G` is a subsingleton finite group and `M` is
any `ℤ[G]`-module, then `Hm1Quotient M = ker N ⧸ I_G M` is trivial: the norm is the identity and
`I_G M = 0`. -/
theorem subsingleton_hm1Quotient_of_subsingleton_group {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton (Work.CFT.Ledger.Hm1Quotient M) := by
  have hker : ∀ x : ↥(Work.CFT.IdeleClassGroup.normMap M).ker, (x : M.V) = 0 := by
    intro x
    have hx := x.2
    rw [AddMonoidHom.mem_ker] at hx
    rw [Work.CFT.IdeleClassGroup.normMap_apply] at hx
    have hcard : Fintype.card G = 1 := by
      haveI : Nonempty G := ⟨1⟩
      exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => Subsingleton.elim g 1⟩
    have hx2 : (∑ g : G, (M.ρ g) (x : M.V)) = (x : M.V) := by
      calc ∑ g : G, (M.ρ g) (x : M.V) = ∑ _g : G, (x : M.V) :=
            Finset.sum_congr rfl (fun g _ => by
              rw [Subsingleton.elim g (1 : G), map_one]; rfl)
        _ = Fintype.card G • (x : M.V) := Finset.sum_const (x : M.V)
        _ = (x : M.V) := by rw [hcard, one_smul]
    rw [hx2] at hx
    exact hx
  exact QuotientAddGroup.subsingleton_iff.mpr (by
    rw [eq_top_iff]
    rintro x -
    rw [show x = 0 from Subtype.ext (hker x)]
    exact (Work.CFT.Ledger.Hm1Sub M).zero_mem)

/-! ## The unit part of a fibre at an infinite place -/

/-- At an infinite place, every element of the local field is a local unit, so the unit part of
the fibre coincides with the full fibre of the idèles. -/
theorem fiberUnits_eq_fiberIdeles_ofInfinite {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] (v : InfinitePlace F) :
    NK.GlobalCFTdeep.fiberUnits (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite v) =
      NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite v) := by
  ext x
  rw [NK.GlobalCFTdeep.mem_fiberUnits, NK.GlobalCFTdeep.mem_fiberIdeles]
  refine ⟨fun h => h.1, fun h => ⟨h, fun w => ?_⟩⟩
  rcases w with w | q
  · rw [NK.GlobalCFT.Place.localUnits_ofInfinite]; exact Subgroup.mem_top _
  · rw [NK.GlobalCFT.Place.localUnits_ofFinite,
      h (NK.GlobalCFT.Place.ofFinite q) (fun hc => absurd
        ((NK.GlobalCFT.Place.isFinite_of_liesOver hc).mp
          (NK.GlobalCFT.Place.isFinite_ofFinite q)) (by simp))]
    exact Subgroup.one_mem _

/-- **The unit part of the fibre at an infinite place is the full fibre**, as
`ℤ[Gal(K/F)]`-modules. -/
theorem fiberUnitsRep_iso_fiberIdelesRep_ofInfinite {F K : Type} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (v : InfinitePlace F) :
    Nonempty (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite v) ≅
      NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite v)) := by
  have h := fiberUnits_eq_fiberIdeles_ofInfinite (F := F) (K := K) v
  let e : Additive ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite v)) ≃ₗ[ℤ]
      Additive ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite v)) :=
    { toFun := fun x => Additive.ofMul
        ⟨((Additive.toMul x : ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
            (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K), h ▸ (Additive.toMul x).2⟩
      invFun := fun x => Additive.ofMul
        ⟨((Additive.toMul x : ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
            (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K), h.symm ▸ (Additive.toMul x).2⟩
      left_inv := fun x => by
        apply Additive.toMul.injective
        exact Subtype.ext rfl
      right_inv := fun x => by
        apply Additive.toMul.injective
        exact Subtype.ext rfl
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show (((Additive.toMul (x + y) : ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
          (NK.GlobalCFT.Place.ofInfinite v)))) : NK.GlobalCFT.Idele K) = _
        rw [toMul_add]
        rfl
      map_smul' := fun n x => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show (((Additive.toMul (n • x) : ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
          (NK.GlobalCFT.Place.ofInfinite v)))) : NK.GlobalCFT.Idele K) = _
        rw [toMul_zsmul]
        rfl }
  have he : ∀ (x : Additive ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v))),
      ((Additive.toMul (e x) : ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K) =
      ((Additive.toMul x : ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K) := fun x => rfl
  refine ⟨Rep.mkIso (Representation.Equiv.mk e ?_)⟩
  intro σ
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  show (((Additive.toMul (e ((NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)).ρ σ x)) : ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)))) : NK.GlobalCFT.Idele K) =
    (((Additive.toMul ((NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)).ρ σ (e x)) : ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)))) : NK.GlobalCFT.Idele K)
  rw [NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_ρ_apply, NK.GlobalCFTdeep.fiberIdelesRep_ρ_apply]
  change σ • ((Additive.toMul x : ↥(NK.GlobalCFTdeep.fiberUnits (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K) =
    σ • ((Additive.toMul (e x) : ↥(NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v))) : NK.GlobalCFT.Idele K)
  rw [he x]

/-! ## The fibre at an infinite place has vanishing `Ĥ⁻¹` -/

/-- **`Ĥ⁻¹(G, ∏_{w | v} K_wˣ) = 0` for `v` infinite and `K/F` unramified at infinity.**  The
decomposition group `D_w` is trivial, so Shapiro's lemma
(`fiberIdelesRep_iso_coind`, `Hm1Quotient_coind_nonempty`) reduces the statement to the trivial
group, where `Ĥ⁻¹` always vanishes. -/
theorem subsingleton_tateCohomology_neg_one_fiberUnitsRep_ofInfinite {F K : Type} [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [IsUnramifiedAtInfinitePlaces F K] (v : InfinitePlace F) :
    Subsingleton (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)) (-1)) := by
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
  haveI hq : Subsingleton (Work.CFT.Ledger.Hm1Quotient (NK.GlobalCFTdeep.localUnitsRep (K := F)
      (L := K) (NK.GlobalCFT.Place.ofInfinite w))) :=
    subsingleton_hm1Quotient_of_subsingleton_group _
  obtain ⟨ec⟩ := Work.CFT.Ledger.Hm1Quotient_coind_nonempty
    (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)).subtype
    (NK.GlobalCFTdeep.localUnitsRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite w))
    (fun a b h => Subtype.ext h)
  haveI hq2 : Subsingleton (Work.CFT.Ledger.Hm1Quotient (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
      (NK.GlobalCFTdeep.localUnitsRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite w)))) :=
    ec.symm.injective.subsingleton
  obtain ⟨e1⟩ := Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient (Rep.coind
    (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite w)).subtype
    (NK.GlobalCFTdeep.localUnitsRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite w)))
  haveI hcoind : Subsingleton (tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
      (NK.GlobalCFTdeep.localUnitsRep (K := F) (L := K) (NK.GlobalCFT.Place.ofInfinite w))) (-1)) :=
    e1.injective.subsingleton
  haveI hfid : Subsingleton (tateCohomology (NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofInfinite v)) (-1)) :=
    ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) (-1)).mapIso e2).toLinearEquiv.injective.subsingleton
  obtain ⟨e0⟩ := fiberUnitsRep_iso_fiberIdelesRep_ofInfinite (F := F) (K := K) v
  exact ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) (-1)).mapIso e0).toLinearEquiv.injective.subsingleton


/-! ## The fibre at a finite unramified place has vanishing `Ĥ⁻¹` -/

/-- **`Ĥ⁻¹(G, ∏_{w | v} 𝒪_wˣ) = 0` for a finite unramified place `v`.**  The fibre is the
coinduced module `Coind_{D_q}^G 𝒪_qˣ` (`fiberUnitsRep_iso_coind`), and `Ĥ⁻¹(D_q, 𝒪_qˣ) = 0` for an
unramified `q` (`subsingleton_tateCohomology_neg_one_localUnitSubRep_of_ramificationIdx_eq_one`);
Shapiro's lemma in degree `-1` transfers this to `G`. -/
theorem subsingleton_tateCohomology_neg_one_fiberUnitsRep_ofFinite {F K : Type} [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1) :
    Subsingleton (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite Q)) (-1)) := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  letI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite q)) := Fintype.ofFinite _
  obtain ⟨e⟩ := NK.GlobalCFTdeep.fiberUnitsRep_iso_coind (K := F) (L := K)
    (NK.GlobalCFT.Place.ofFinite Q) q (NK.GlobalCFT.Place.liesOver_ofFinite hq)
  have h1 : Subsingleton (tateCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := F) (L := K)
      (NK.GlobalCFT.Place.ofFinite q)) (-1)) :=
    subsingleton_tateCohomology_neg_one_localUnitSubRep_of_ramificationIdx_eq_one Q q hunr
  have h2 : Subsingleton (tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype
      (NK.GlobalCFTdeep.localUnitSubRep (K := F) (L := K)
        (NK.GlobalCFT.Place.ofFinite q))) (-1)) :=
    subsingleton_tateCohomology_neg_one_coind _ (fun a b h => Subtype.ext h) _ h1
  exact ((tateCohomologyFunctor (R := ℤ) (G := K ≃ₐ[F] K) (-1)).mapIso e).toLinearEquiv.injective.subsingleton

/-! ## The target -/

theorem subsingleton_tateCohomology_neg_one_localUnitIdeles {F K : Type} [Field F]
    [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (hUnr : CFTLib.IsUnramified F K) :
    Subsingleton ↥(tateCohomology (NK.GlobalCFTdeep.localUnitIdelesRep (K := F) (L := K)) (-1)) := by
  haveI hinf : IsUnramifiedAtInfinitePlaces F K := hUnr.2
  have hprimes : Work.Tower.IsUnramifiedExtensionForallPrimes F K :=
    Work.CFTLib.forallPrimes_of_isUnramified hUnr
  have hfac : ∀ v : NK.GlobalCFT.Place F,
      Subsingleton (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1)) := by
    intro v
    rcases v with w | Q
    · exact subsingleton_tateCohomology_neg_one_fiberUnitsRep_ofInfinite w
    · obtain ⟨P₀⟩ := (Ideal.nonempty_primesOver Q.asIdeal :
        Nonempty (Q.asIdeal.primesOver (NumberField.RingOfIntegers K)))
      let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
        ⟨P₀.1, P₀.2.1, Ideal.ne_bot_of_mem_primesOver Q.ne_bot P₀.2⟩
      exact subsingleton_tateCohomology_neg_one_fiberUnitsRep_ofFinite Q q P₀.2.2
        (hprimes q.asIdeal q.isPrime)
  have hsub : Subsingleton ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1)) :=
    ⟨fun a b => funext fun v => Subsingleton.elim (a v) (b v)⟩
  have hne : Nonempty ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1)) :=
    ⟨fun _ => 0⟩
  have h1 : Nat.card ((v : NK.GlobalCFT.Place F) →
      tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩
  have hcard := natCard_tateCohomology_localUnitIdelesRep (K := F) (L := K) (-1)
  exact (Nat.card_eq_one_iff_unique.mp (hcard.trans h1)).1

end Work.CFTLib
