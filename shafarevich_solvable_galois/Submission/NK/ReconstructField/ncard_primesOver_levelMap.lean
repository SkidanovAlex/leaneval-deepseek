import Mathlib
import Submission.NK.ReconstructField.Basic
import Submission.NK.ReconstructField.splitsCompletely_levelMap_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

open scoped Pointwise

set_option linter.style.haveILetI false

/-! ### Auxiliary lemmas for the counting form of the prime correspondence

The proof of `ncard_primesOver_levelMap` rests on two facts, both proved below for a general
finite Galois level `L` of a number field `K` inside a Galois extension `K'`:

* `ncard_primesOver_eq_index_decompositionSubgroup`: the number of primes of `𝓞 L` over a prime
  `p` of `K` is the index of the decomposition subgroup (in the relative Galois group
  `Gal(L/K)`) of any prime of `𝓞 L` over `p` — the orbit-stabiliser form of the fibre–torsor
  argument;
* `sup_fixingSubgroup_eq_comap_decompositionSubgroup`: in the absolute group `Gal(K'/K)`, the
  preimage of that decomposition subgroup is `Gal(K'/L) ⊔ D_A`, where `A` is a place of `K'`
  over `p` and `D_A` its decomposition group.

Since `ϕ` maps `Gal(K₁'/L)` onto `Gal(K₂'/L₂)` and `D_A` onto `D_{a.placeMap A}`, the two finite
indices agree, and the counting statement follows.
-/

/-- **The stabiliser of the prime ideal of a finite place is its decomposition subgroup.** -/
theorem stabilizer_asIdeal_eq_decompositionSubgroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer Gal(L/K) w.asIdeal =
      Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w := by
  have elem : ∀ (σ : Gal(L/K)) (x : NumberField.RingOfIntegers L),
      (σ • x : NumberField.RingOfIntegers L) =
        galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x := by
    intro σ x
    apply Subtype.ext
    exact ((algebraMap_galRestrict_apply (NumberField.RingOfIntegers K) σ x).trans rfl).symm
  have hring : ∀ σ : Gal(L/K),
      (MulSemiringAction.toRingHom Gal(L/K) (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) =
      (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) :=
    fun σ => RingHom.ext (fun x => elem σ x)
  ext σ
  rw [MulAction.mem_stabilizer_iff, Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
  have hmap : σ • w.asIdeal = Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
      NumberField.RingOfIntegers L) w.asIdeal := by
    rw [Ideal.pointwise_smul_def, hring σ]
  have hiff : (Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
      NumberField.RingOfIntegers L) w.asIdeal = w.asIdeal) ↔
      (Submission.NeukirchUchida.Local.placeSmul σ w = w) := by
    rw [← Submission.NeukirchUchida.Local.placeSmul_asIdeal σ w]
    exact ⟨fun h => IsDedekindDomain.HeightOneSpectrum.ext h,
      fun h => congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h⟩
  rw [hmap, hiff]

/-- **The number of primes above `p` is the index of the decomposition subgroup** (orbit-stabiliser
form of the fibre–torsor argument: `Gal(L/K)` acts transitively on the primes of `𝓞 L` over `p`,
and the stabiliser of a prime is its decomposition group). -/
theorem ncard_primesOver_eq_index_decompositionSubgroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : w.asIdeal.LiesOver p.asIdeal) :
    (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard =
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w).index := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  rw [← stabilizer_asIdeal_eq_decompositionSubgroup w]
  have horb : (MulAction.orbit Gal(L/K) w.asIdeal).ncard =
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard :=
    congrArg Set.ncard (Algebra.IsInvariant.orbit_eq_primesOver (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) Gal(L/K) p.asIdeal w.asIdeal)
  refine horb.symm.trans ?_
  rw [← Nat.card_coe_set_eq, Subgroup.index_eq_card]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Gal(L/K) w.asIdeal)

/-- **The preimage in the absolute Galois group of the decomposition subgroup of the induced
place of a finite level**: for a place `A` of `K'` over `p` and the induced place
`w = placeOf p A hA L` of the level `L`,

`Gal(K'/L) ⊔ D_A = ρ⁻¹(D_w)`, where `ρ : Gal(K'/K) →* Gal(L/K)` is the restriction.

The inclusion `⊆` is the compatibility of the projective system of decomposition groups; the
reverse inclusion uses the surjectivity of `D_A → D_w` on the finite level
(`exists_mem_stabilizer_restrictNormalHom_eq`). -/
theorem sup_fixingSubgroup_eq_comap_decompositionSubgroup {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    L.fixingSubgroup ⊔ MulAction.stabilizer Gal(K'/K) A =
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K)
        (Submission.NeukirchUchida.Local.placeOf p A hA L)).comap
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) := by
  have hw : A.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
        (Submission.NeukirchUchida.Local.placeOf p A hA L) :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p A hA L
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro h hh
      rw [Subgroup.mem_comap]
      have hker : h ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L).ker := by
        rw [IntermediateField.restrictNormalHom_ker (K := K) L]; exact hh
      rw [MonoidHom.mem_ker.mp hker]
      exact Subgroup.one_mem _
    · intro σ hσ
      rw [Subgroup.mem_comap]
      exact Submission.NeukirchUchida.Local.restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer
        A L _ hw σ hσ
  · intro g hg
    rw [Subgroup.mem_comap] at hg
    obtain ⟨σ, hσ, hσg⟩ :=
      Submission.NeukirchUchida.Local.exists_mem_stabilizer_restrictNormalHom_eq p A hA L
        (⟨_, hg⟩ : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K)
          (Submission.NeukirchUchida.Local.placeOf p A hA L))
    have hmem : σ⁻¹ * g ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (K := K) L, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hσg]
      exact inv_mul_cancel _
    have h1 : σ * (σ⁻¹ * g) ∈ MulAction.stabilizer Gal(K'/K) A ⊔ L.fixingSubgroup :=
      Subgroup.mul_mem_sup hσ hmem
    rw [show σ * (σ⁻¹ * g) = g from by group] at h1
    rwa [sup_comm]

/-- **The number of primes above a prime is preserved at corresponding levels** (the finite-level
prime correspondence of CoNF XII §12.2, in counting form).

Let `ϕ` be a homeomorphic isomorphism with local correspondence `a`, `L ⊆ K₁'` a finite normal level
which is a number field, and `L₂ = levelMap ϕ L` its image level.  Then, for every prime `p` of
`K₁`, the number of primes of `𝓞 L` above `p` equals the number of primes of `𝓞 L₂` above
`a.primeMap p`.

Proof route (the fibre-torsor argument): the places of `K₁'` over `p` map onto the primes of `L`
above `p` (a place goes to its trace on `L`), and the fibres of this restriction map are exactly the
orbits of `Gal(K₁'/L)`; moreover `a.placeMap` maps the places of `K₁'` over `p` bijectively onto
those of `K₂'` over `a.primeMap p` (`a.primeMap_spec`), equivariantly with respect to `ϕ` and
`ϕ(Gal(K₁'/L)) = Gal(K₂'/L₂)` (`NK.Reconstruct.fixingSubgroup_levelMap`).  Hence the orbit sets
are in bijection, and counting gives the claim.  (The special case of a prime splitting completely,
i.e. the equality of the extreme values of these counts, is
`NK.ReconstructField.splitsCompletely_levelMap_iff`.) -/
theorem ncard_primesOver_levelMap
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (p : NK.Chebotarev.PrimeIdeal K₁) :
    (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard =
      ((a.primeMap p).asIdeal.primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))).ncard := by
  classical
  haveI : IsGalois K₁ K₁' := IsSepClosure.isGalois
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  -- the image level
  let L₂ : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ L
  haveI hL₂fd : FiniteDimensional K₂ L₂ :=
    ‹FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)›
  haveI hL₂nf : Normal K₂ L₂ := ‹Normal K₂ (NK.Reconstruct.levelMap ϕ L)›
  haveI hL₂num : NumberField ↥L₂ := ‹NumberField ↥(NK.Reconstruct.levelMap ϕ L)›
  -- a place of `K₁'` over `p` and its image under the local correspondence
  let A : NK.Reconstruct.FinitePlaceOf K₁ K₁' := Submission.NeukirchUchida.placeOver p
  have hA : A.1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ p :=
    Submission.NeukirchUchida.placeOver_spec p
  let B : NK.Reconstruct.FinitePlaceOf K₂ K₂' := a.placeMap A
  have hB : B.1.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ (a.primeMap p) := by
    have hprime : Submission.NeukirchUchida.primeOf A.1 A.2 = p :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (R := NumberField.RingOfIntegers K₁)
        (by rw [← Submission.NeukirchUchida.primeOf_spec A.1 A.2, hA])
    rw [← hprime, a.primeMap_spec A]
    exact Submission.NeukirchUchida.primeOf_spec B.1 B.2
  -- the primes of the two levels cut out by `A` and `B`
  let w₁ := Submission.NeukirchUchida.Local.placeOf p A.1 hA L
  let w₂ := Submission.NeukirchUchida.Local.placeOf (a.primeMap p) B.1 hB L₂
  -- the number of primes over a prime is the index of the decomposition subgroup
  have hn₁ : (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard =
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K₁) w₁).index :=
    ncard_primesOver_eq_index_decompositionSubgroup p w₁
      (Submission.NeukirchUchida.Local.placeOf_liesOver p A.1 hA L)
  have hn₂ : ((a.primeMap p).asIdeal.primesOver (NumberField.RingOfIntegers ↥L₂)).ncard =
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K₂) w₂).index :=
    ncard_primesOver_eq_index_decompositionSubgroup (a.primeMap p) w₂
      (Submission.NeukirchUchida.Local.placeOf_liesOver (a.primeMap p) B.1 hB L₂)
  -- the preimage of the decomposition subgroup in the absolute Galois group
  have hE₁ := sup_fixingSubgroup_eq_comap_decompositionSubgroup (K := K₁) (K' := K₁') p A.1 hA L
  have hE₂ := sup_fixingSubgroup_eq_comap_decompositionSubgroup (K := K₂) (K' := K₂')
    (a.primeMap p) B.1 hB L₂
  have hsurj₁ : Function.Surjective
      ⇑(AlgEquiv.restrictNormalHom (F := K₁) (K₁ := K₁') L) :=
    AlgEquiv.restrictNormalHom_surjective (F := K₁) (K₁ := ↥L) (E := K₁')
  have hsurj₂ : Function.Surjective
      ⇑(AlgEquiv.restrictNormalHom (F := K₂) (K₁ := K₂') L₂) :=
    AlgEquiv.restrictNormalHom_surjective (F := K₂) (K₁ := ↥L₂) (E := K₂')
  have hidx₁ : (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard =
      (L.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₁'/K₁) A.1).index := by
    have hc := Subgroup.index_comap_of_surjective
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K₁) w₁) hsurj₁
    rw [hn₁, hE₁, hc]
  have hidx₂ : ((a.primeMap p).asIdeal.primesOver (NumberField.RingOfIntegers ↥L₂)).ncard =
      (L₂.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₂'/K₂) B.1).index := by
    have hc := Subgroup.index_comap_of_surjective
      (Submission.NeukirchUchida.Local.decompositionSubgroup (K := K₂) w₂) hsurj₂
    rw [hn₂, hE₂, hc]
  -- `ϕ` carries the first subgroup onto the second
  have hmap : (L.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₁'/K₁) A.1).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      L₂.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₂'/K₂) B.1 := by
    rw [Subgroup.map_sup, ← NK.Reconstruct.fixingSubgroup_levelMap hϕ L]
    congr 1
    have hd := a.map_decomp A
    simpa only [Submission.NeukirchUchida.decompositionGroup] using hd
  -- assemble
  calc (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard
      = (L.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₁'/K₁) A.1).index := hidx₁
    _ = ((L.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₁'/K₁) A.1).map
          (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))).index :=
        (Subgroup.index_map_equiv _ ϕ).symm
    _ = (L₂.fixingSubgroup ⊔ MulAction.stabilizer Gal(K₂'/K₂) B.1).index := by rw [hmap]
    _ = ((a.primeMap p).asIdeal.primesOver (NumberField.RingOfIntegers ↥L₂)).ncard :=
        hidx₂.symm

end NK.ReconstructField
