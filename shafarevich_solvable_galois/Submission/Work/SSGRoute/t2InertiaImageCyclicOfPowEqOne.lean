import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.Work.SSGRoute.step4_local_target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

open scoped IsMulCommutative

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- **The abstract group-theoretic core, with exponent `p ^ k`.**  Let `V ◁ G` be pro-`ℓ`,
`I ≤ G` such that `I/V` is pro-cyclic, and let `φ : G →* X` be a homomorphism into a group of
exponent dividing `p ^ k`, with `ℓ ≠ p` prime and `φ.ker` of finite index.  Then `V ≤ φ.ker`
(a finite quotient of a pro-`ℓ` group inside a group of exponent `p ^ k` is trivial: its order
divides both a power of `ℓ` and `p ^ k`, hence is `1`) and the image of `I` is a finite quotient
of the pro-cyclic group `I/V`, hence cyclic.

This is `Work.SSGRoute.isCyclic_map_of_proCyclic_quotient` with `x ^ p = 1` replaced by
`x ^ (p ^ k) = 1`; that proof uses the exponent hypothesis only in the single step where a prime
`ℓ ≠ p` dividing the order of an element is shown to divide `p`. -/
theorem isCyclic_map_of_proCyclic_quotient_pow (ℓ p k : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime)
    (hne : ℓ ≠ p)
    {G X : Type*} [Group G] [Group X] (V I : Subgroup G) [V.Normal]
    (hVpro : NK.LocalTame.IsProP ℓ ↥V)
    (hprocyc : NK.LocalTame.IsProCyclic (↥I ⧸ V.subgroupOf I))
    (φ : G →* X) (hexp : ∀ x : X, x ^ (p ^ k) = 1) (hfin : φ.ker.FiniteIndex) :
    IsCyclic ↥(I.map φ) := by
  classical
  -- the image of `V` in `X` is trivial
  have hVker : V ≤ φ.ker := by
    let g : ↥V →* X := φ.comp V.subtype
    have hgker : g.ker.FiniteIndex := by
      have h1 : g.ker = φ.ker.subgroupOf V := rfl
      rw [h1]
      infer_instance
    haveI hgkerI : g.ker.FiniteIndex := hgker
    haveI : Finite (↥V ⧸ g.ker) := inferInstance
    obtain ⟨d, hd⟩ := hVpro g.ker hgker
    have hcard : Nat.card (↥V ⧸ g.ker) = ℓ ^ d := by
      rw [← Subgroup.index_eq_card, hd]
    have hd0 : d = 0 := by
      by_contra hd0
      have hdvd : ℓ ∣ Nat.card (↥V ⧸ g.ker) := by
        rw [hcard]
        exact dvd_pow_self _ hd0
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥V ⧸ g.ker) ℓ hdvd
      have hyp : y ^ (p ^ k) = 1 := by
        apply (QuotientGroup.quotientKerEquivRange g).injective
        rw [map_pow, map_one]
        exact Subtype.ext (hexp (((QuotientGroup.quotientKerEquivRange g) y : ↥g.range) : X))
      have hdiv : ℓ ∣ p ^ k := by
        rw [← hy]
        exact orderOf_dvd_iff_pow_eq_one.mpr hyp
      exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hdiv))
    rw [hd0, pow_zero] at hcard
    have htop : g.ker = ⊤ := by
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card, hcard]
    intro v hv
    have hmem : (⟨v, hv⟩ : ↥V) ∈ g.ker := by rw [htop]; trivial
    exact MonoidHom.mem_ker.mp hmem
  -- the induced map `I/V →* X` has the same image as `I →* X`
  have hker' : V.subgroupOf I ≤ (φ.comp I.subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show φ ↑x = 1
    exact MonoidHom.mem_ker.mp (hVker (Subgroup.mem_subgroupOf.mp hx))
  let h' : (↥I ⧸ V.subgroupOf I) →* X :=
    QuotientGroup.lift (V.subgroupOf I) (φ.comp I.subtype) hker'
  have hrange : h'.range = I.map φ := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf I) x
      exact Subgroup.mem_map.mpr ⟨i, i.2,
        (QuotientGroup.lift_mk' (N := V.subgroupOf I) hker' i).symm⟩
    · rintro y ⟨i, hi, rfl⟩
      exact ⟨QuotientGroup.mk' (V.subgroupOf I) ⟨i, hi⟩,
        QuotientGroup.lift_mk' (N := V.subgroupOf I) hker' ⟨i, hi⟩⟩
  have hfin' : h'.ker.FiniteIndex := by
    haveI : Nonempty ↥h'.range := ⟨⟨1, Subgroup.one_mem _⟩⟩
    haveI hFr : Finite ↥φ.range := finite_range_of_finiteIndex φ hfin
    have hle : h'.range ≤ φ.range := by
      rw [hrange]
      exact Subgroup.map_le_range φ I
    haveI : Finite ↥h'.range := Finite.of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [Subgroup.finiteIndex_iff, Subgroup.index_ker]
    exact (Finite.card_pos).ne'
  have hcycQuot : IsCyclic ((↥I ⧸ V.subgroupOf I) ⧸ h'.ker) := hprocyc h'.ker hfin'
  rw [← hrange]
  exact (QuotientGroup.quotientKerEquivRange h').isCyclic.mp hcycQuot

/-- **The image of the inertia subgroup of a finite place under a homomorphism into a group of
exponent dividing `p ^ k` is cyclic**, for a finite place `A'` of `ℚ̄` whose residue characteristic
is not `p`.  This is `Work.SSGRoute.step4_inertia_image_cyclic` with `x ^ p = 1` replaced by
`x ^ (p ^ k) = 1`. -/
theorem step4_inertia_image_cyclic_pow (p : ℕ) (hp : p.Prime) (k : ℕ)
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (hAp : ¬ A'.1.valuation (p : SSGRoute.QBar) < 1)
    {X : Type*} [Group X] (hexp : ∀ x : X, x ^ (p ^ k) = 1)
    (f : ↥(SSGRoute.decomp ℚ A'.1) →* X) (hfin : f.ker.FiniteIndex) :
    IsCyclic ↥((ValuationSubring.inertiaSubgroup ℚ A'.1).map f) := by
  classical
  -- the residue characteristic `ℓ` is a prime different from `p`
  have hℓ : (Work.SSGRoute.residueChar A').Prime := Work.SSGRoute.residueChar_prime A'
  have hne : Work.SSGRoute.residueChar A' ≠ p := by
    intro h
    exact hAp ((Work.SSGRoute.residueChar_dvd_iff_valuation_lt_one A' p).mp (h ▸ dvd_refl p))
  -- the local structure theory at the place and the local/global identification
  have hT : NK.LocalTame.TameData (Work.SSGRoute.residueChar A')
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
      (NK.FrobeniusBridge.localField A') (NK.FrobeniusBridge.localClosure A') :=
    Work.SSGRoute.localTameData A'
  have hq : NK.ResidueFrob.ResidueCardMatches A'
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2)) :=
    Work.SSGRoute.residueCardMatches_localStructure A'
  let κ := NK.FrobeniusBridge.localField A'
  let K' := NK.FrobeniusBridge.localClosure A'
  let e : ↥(SSGRoute.decomp ℚ A'.1) ≃* Gal(K'/κ) := NK.FrobeniusBridge.localGaloisEquiv A'
  let Vκ : Subgroup Gal(K'/κ) := NK.LocalTame.wildInertiaSubgroup (Work.SSGRoute.residueChar A')
  let Iκ : Subgroup Gal(K'/κ) := NK.LocalAnabelian.inertiaSubgroup (Work.SSGRoute.residueChar A')
  let Fhom : Gal(K'/κ) →* X := f.comp e.symm.toMonoidHom
  haveI hVκN : Vκ.Normal := by
    show (NK.LocalTame.wildInertiaSubgroup (Work.SSGRoute.residueChar A')).Normal
    infer_instance
  -- (i) the global and the local inertia subgroups correspond under `e`
  have hS : ∀ σ : ↥(SSGRoute.decomp ℚ A'.1),
      σ ∈ ValuationSubring.inertiaSubgroup ℚ A'.1 ↔ e σ ∈ Iκ := by
    intro σ
    rw [isInertia_iff_mem_inertiaSubgroup]
    exact ⟨fun h => inertia_of_isInertia A' (Work.SSGRoute.residueChar A')
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
        hT hq rfl σ h,
      fun h => isInertia_of_mem_inertia A' (Work.SSGRoute.residueChar A')
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
        hT hq rfl σ h⟩
  have hmapI : (ValuationSubring.inertiaSubgroup ℚ A'.1).map e.toMonoidHom = Iκ := by
    ext y
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hS σ).mp hσ
    · intro hy
      exact ⟨e.symm y, (hS (e.symm y)).mpr (by simpa using hy), by simp⟩
  -- (ii) the goal transfers: the image of `Iκ` under `Fhom = f ∘ e⁻¹`
  have hgoal : Iκ.map Fhom = (ValuationSubring.inertiaSubgroup ℚ A'.1).map f := by
    rw [← hmapI, Subgroup.map_map]
    congr 1
    ext σ
    simp [Fhom]
  -- (iii) `Fhom` has finite index kernel
  have hFker : Fhom.ker.FiniteIndex := by
    have hker : Fhom.ker = Subgroup.comap e.symm.toMonoidHom f.ker :=
      (MonoidHom.comap_ker f e.symm.toMonoidHom).symm
    rw [Subgroup.finiteIndex_iff, hker,
      Subgroup.index_comap_of_surjective (H := f.ker) (f := e.symm.toMonoidHom) e.symm.surjective]
    exact hfin.index_ne_zero
  -- (iv) `Iκ/Vκ` is pro-cyclic
  have hprocyc : NK.LocalTame.IsProCyclic (↥Iκ ⧸ Vκ.subgroupOf Iκ) := by
    have hker_eq : ((QuotientGroup.mk' Vκ).comp Iκ.subtype).ker = Vκ.subgroupOf Iκ := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hrange_eq : ((QuotientGroup.mk' Vκ).comp Iκ.subtype).range
        = NK.LocalTame.quotientImage Vκ Iκ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have e1 : (↥Iκ ⧸ Vκ.subgroupOf Iκ) ≃* ↥(NK.LocalTame.quotientImage Vκ Iκ) :=
      (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
        ((QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' Vκ).comp Iκ.subtype)).trans
          (MulEquiv.subgroupCongr hrange_eq))
    exact (NK.LocalTame.isProCyclic_congr e1).mpr hT.structure_input.isTameInertia.2.2.1
  -- (v) conclude
  have hcycI : IsCyclic ↥(Iκ.map Fhom) :=
    isCyclic_map_of_proCyclic_quotient_pow (Work.SSGRoute.residueChar A') p k hℓ hp hne
      Vκ Iκ (NK.LocalTame.wildInertiaSubgroup_isProP (Work.SSGRoute.residueChar A'))
      hprocyc Fhom hexp hFker
  rw [← hgoal]
  exact hcycI

/-- **The image of the global inertia group `I_A` under a homomorphism into a group of exponent
dividing `p ^ k` is cyclic**, for a finite place `A` of `ℚ̄` whose residue characteristic is not `p`.

The wild inertia `V_A` is pro-`ℓ` with `ℓ ≠ p` (so it maps to `1`, because the target has exponent
`p ^ k` and the image of `V_A` is finite by `hfin`, hence a finite `ℓ`-group inside a `p`-group),
while the tame inertia `I_A/V_A` is pro-cyclic (the field `isTameInertia` of
`NK.LocalTame.TameStructureInput`) and `f(I_A)` is a finite quotient of it, hence cyclic.

This is `Work.SSGRoute.step4_inertia_image_cyclic` with the hypothesis `x ^ p = 1` replaced by
`x ^ (p ^ k) = 1`: that proof uses the exponent hypothesis only through the step "a finite
`ℓ`-group inside a group of exponent a power of `p` is trivial"
(`Work.SSGRoute.isCyclic_map_of_proCyclic_quotient`), which generalises immediately, and the rest
is the transport of `↥(SSGRoute.decomp ℚ A)` to `Gal(κ̄/κ)` along
`NK.FrobeniusBridge.localGaloisEquiv` together with `Work.SSGRoute.inertia_of_isInertia` and
`Work.SSGRoute.isInertia_of_mem_inertia`. -/
theorem t2InertiaImageCyclicOfPowEqOne (p : ℕ) (hp : p.Prime) (k : ℕ) {X : Type*} [Group X]
    (hexp : ∀ x : X, x ^ (p ^ k) = 1)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hAp : ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (f : ↥(SSGRoute.decomp ℚ A) →* X) (hfin : f.ker.FiniteIndex) :
    IsCyclic ↥((ValuationSubring.inertiaSubgroup ℚ A).map f) :=
  step4_inertia_image_cyclic_pow p hp k ⟨A, hA⟩ hAp hexp f hfin

end Work.SSGRoute
