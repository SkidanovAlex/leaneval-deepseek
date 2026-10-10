import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.NK.HassePrinciple.exists_unitsLevelMapCoeff
import Submission.NK.NUV2.ABHN.solvable_algEquiv_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace NK.NUV2.ABHN

/-! ## The coefficient-ring transfer for `H²`

`groupCohomology` of a representation depends on the coefficient ring only through the underlying
additive group and the action: a `k[G]`-module and a `k'[G]`-module with the same underlying
additive group and the same `G`-action have abstractly isomorphic second cohomology.  The proof
uses Mathlib's low-degree description `H2π : cocycles₂ → H²` (surjective with kernel the
coboundaries) and the ring-agnostic cocycle identities of `NK.HassePrinciple.H2π_eq_zero_transfer`.
-/

/-- **The coefficient-ring transfer for `H²`.**  If `V` carries both a `k`-module and a `k'`-module
structure compatible with the same `G`-action, then the second cohomology of the associated
representations have the same cardinality. -/
theorem natCard_groupCohomology_two_coeffTransfer {k k' G V : Type} [CommRing k] [CommRing k']
    [Group G] [AddCommGroup V] [Module k V] [Module k' V] [DistribMulAction G V]
    [SMulCommClass G k V] [SMulCommClass G k' V] :
    Nat.card (↥(groupCohomology (Rep.ofDistribMulAction k G V) 2)) =
    Nat.card (↥(groupCohomology (Rep.ofDistribMulAction k' G V) 2)) := by
  have hsurj : Function.Surjective (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurj' : Function.Surjective (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  -- the two cocycle modules have the same underlying type; `cast₁`, `cast₂` move between them
  let cast₁ : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)) →
      ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)) := fun z => z
  let cast₂ : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)) →
      ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)) := fun z => z
  have wd : ∀ x x' : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)),
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) x =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) x' →
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x) =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x') := by
    intro x x' h
    have hsub : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (x - x') = 0 := by
      rw [map_sub, h, sub_self]
    have h1 : ⇑(x - x') ∈ groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k G V) :=
      (groupCohomology.H2π_eq_zero_iff (x - x')).mp hsub
    have h2 : ⇑(cast₁ (x - x')) ∈
        groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k' G V) := h1
    have h3 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ (x - x')) = 0 :=
      (groupCohomology.H2π_eq_zero_iff (cast₁ (x - x'))).mpr h2
    have h4 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x) -
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x') = 0 := by
      rw [← map_sub]
      exact h3
    exact sub_eq_zero.mp h4
  have wd' : ∀ x x' : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)),
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) x =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) x' →
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x) =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x') := by
    intro x x' h
    have hsub : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (x - x') = 0 := by
      rw [map_sub, h, sub_self]
    have h1 : ⇑(x - x') ∈ groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k' G V) :=
      (groupCohomology.H2π_eq_zero_iff (x - x')).mp hsub
    have h2 : ⇑(cast₂ (x - x')) ∈
        groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k G V) := h1
    have h3 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ (x - x')) = 0 :=
      (groupCohomology.H2π_eq_zero_iff (cast₂ (x - x'))).mpr h2
    have h4 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x) -
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x') = 0 := by
      rw [← map_sub]
      exact h3
    exact sub_eq_zero.mp h4
  refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
  · exact fun y => (groupCohomology.H2π (Rep.ofDistribMulAction k' G V))
      (cast₁ (Function.surjInv hsurj y))
  · exact fun y => (groupCohomology.H2π (Rep.ofDistribMulAction k G V))
      (cast₂ (Function.surjInv hsurj' y))
  · intro y
    have hX := Function.surjInv_eq hsurj' ((⇑(groupCohomology.H2π
      (Rep.ofDistribMulAction k' G V))) (cast₁ (Function.surjInv hsurj y)))
    exact (wd' _ _ hX).trans (Function.surjInv_eq hsurj y)
  · intro y
    have hX := Function.surjInv_eq hsurj ((⇑(groupCohomology.H2π
      (Rep.ofDistribMulAction k G V))) (cast₂ (Function.surjInv hsurj' y)))
    exact (wd _ _ hX).trans (Function.surjInv_eq hsurj' y)

/-! ## The level dictionary at the top level

For `V = ⊤` the restriction `LevelGroup ⊤ L →* Gal(↥L/K)` is bijective — its kernel is
`Gal(K'/L)`, which is exactly the subgroup being quotiented out — and the level representation is
`Rep.res` of the units representation along it.  This identifies `UnitsLevelH2 ⊤ L` with the second
cohomology of the units of `↥L` as a `Gal(↥L/K)`-module. -/

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The restriction `LevelGroup ⊤ L →* Gal(↥L/K)` is injective: its kernel is the subgroup
`Gal(K'/L)` by which the level group is defined as a quotient. -/
theorem levelGroupRestrictHom_top_injective (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
    (L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(K'/K))) x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    (L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(K'/K))) y
  change (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L)
      (QuotientGroup.mk v) =
    (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L)
      (QuotientGroup.mk w) at hxy
  rw [NK.HassePrinciple.levelGroupRestrictHom_mk] at hxy
  rw [NK.HassePrinciple.levelGroupRestrictHom_mk] at hxy
  have hker : (v⁻¹ * w) ∈
      (NK.HassePrinciple.levelRestrictHom (⊤ : Subgroup Gal(K'/K)) L).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    rw [show (NK.HassePrinciple.levelRestrictHom (⊤ : Subgroup Gal(K'/K)) L) v
        = NK.HassePrinciple.levelRestrict L (v : Gal(K'/K)) from rfl]
    rw [show (NK.HassePrinciple.levelRestrictHom (⊤ : Subgroup Gal(K'/K)) L) w
        = NK.HassePrinciple.levelRestrict L (w : Gal(K'/K)) from rfl]
    rw [hxy, inv_mul_cancel]
  have hmem : (v⁻¹ * w) ∈ L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(K'/K)) := by
    rwa [NK.HassePrinciple.levelRestrictHom_ker] at hker
  change QuotientGroup.mk v = QuotientGroup.mk w
  rw [QuotientGroup.eq]
  exact hmem

/-- The restriction `LevelGroup ⊤ L →* Gal(↥L/K)` is surjective: every `K`-automorphism of `L`
extends to the separable closure. -/
theorem levelGroupRestrictHom_top_surjective (L : FiniteGaloisIntermediateField K K') :
    Function.Surjective (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L) := by
  intro σ
  obtain ⟨τ, hτ⟩ := (AlgEquiv.restrictNormalHom_surjective K' :
    Function.Surjective (NK.HassePrinciple.levelRestrict L)) σ
  exact ⟨QuotientGroup.mk ⟨τ, Subgroup.mem_top τ⟩, by
    rw [NK.HassePrinciple.levelGroupRestrictHom_mk]; exact hτ⟩

/-- **The level dictionary at the top level**: `UnitsLevelH2 ⊤ L` is, up to the change of
coefficient ring `CoeffInt → ℤ`, the second cohomology `H²(Gal(↥L/K), ↥Lˣ)`. -/
theorem natCard_unitsLevelH2_top_eq (L : FiniteGaloisIntermediateField K K') :
    Nat.card (↥(NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') ⊤ L)) =
    Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits K ↥L) 2)) := by
  let e : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L ≃* (↥L ≃ₐ[K] ↥L) :=
    MulEquiv.ofBijective (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L)
      ⟨levelGroupRestrictHom_top_injective L, levelGroupRestrictHom_top_surjective L⟩
  have h1 := Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
    e (NK.HassePrinciple.unitsRep K ↥L) 2
  have he : e.toMonoidHom = NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L :=
    MonoidHom.ext fun _ => rfl
  have h3 : Nat.card (↥(groupCohomology (Rep.res
      (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L)
      (NK.HassePrinciple.unitsRep K ↥L)) 2)) =
      Nat.card (↥(groupCohomology (NK.HassePrinciple.unitsRep K ↥L) 2)) := by
    rw [← he]
    exact h1
  have h4 : Nat.card (↥(groupCohomology (NK.HassePrinciple.unitsRep K ↥L) 2)) =
      Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits K ↥L) 2)) := by
    rw [show NK.HassePrinciple.unitsRep K ↥L =
        Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt (↥L ≃ₐ[K] ↥L) (Additive (↥L)ˣ)
        from rfl]
    rw [show Rep.ofAlgebraAutOnUnits K ↥L =
        Rep.ofDistribMulAction ℤ (↥L ≃ₐ[K] ↥L) (Additive (↥L)ˣ) from rfl]
    exact natCard_groupCohomology_two_coeffTransfer
  exact h3.trans h4


/-! ## Local reciprocity for completions of number fields

Every finite Galois extension `E` of the `𝔮`-adic completion `K_𝔮` of a number field is the
completion of a *Galois* extension `L'/K` of number fields (`exists_galois_realization`).  For that
global extension the workspace has

* the existence of a fundamental class of order `[L'_q : K_𝔮]`
  (`exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`), giving
  `[E : K_𝔮] ∣ |H²(Gal(E/K_𝔮), Eˣ)|`, and
* the upper bound `|H²(Gal(L'_q/K_𝔮), L'_qˣ)| ≤ [L'_q : K_𝔮]`
  (`natCard_groupCohomology_two_units_le_finrank_of_solvable`), the solvable dévissage, for which
  the solvability of the local Galois group is `solvable_algEquiv_adicCompletion`.

Since `H²` and `finrank` are both invariant under the `K_𝔮`-algebra isomorphism `E ≃ₐ L'_q`, the two
bounds squeeze the cardinality to the degree.
-/

open IsDedekindDomain in
theorem natCard_groupCohomology_two_units_adicCompletion_eq_finrank
    {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (𝔮.adicCompletion K) E]
    [FiniteDimensional (𝔮.adicCompletion K) E] [IsGalois (𝔮.adicCompletion K) E] :
    Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits (𝔮.adicCompletion K) E) 2)) =
      Module.finrank (𝔮.adicCompletion K) E := by
  classical
  obtain ⟨L', hL'f, hL'nf, hL'a, q, hq, hgal, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_realization (K := K) 𝔮 (E := E)
  letI : Field L' := hL'f
  letI : NumberField L' := hL'nf
  letI : Algebra K L' := hL'a
  haveI : IsGalois K L' := hgal
  letI : Algebra (𝔮.adicCompletion K) (q.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔮 q hq)
  haveI : FiniteDimensional (𝔮.adicCompletion K) (q.adicCompletion L') :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion 𝔮 q hq
  haveI : IsGalois (𝔮.adicCompletion K) (q.adicCompletion L') :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion 𝔮 q hq
  have hcard :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv e
  have hfr : Module.finrank (𝔮.adicCompletion K) E =
      Module.finrank (𝔮.adicCompletion K) (q.adicCompletion L') :=
    e.toLinearEquiv.finrank_eq
  haveI : Finite ↥(groupCohomology
      (Rep.ofAlgebraAutOnUnits (𝔮.adicCompletion K) (q.adicCompletion L')) 2) :=
    Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois
      𝔮 q hq
  have hub :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable
      𝔮 (NK.NUV2.ABHN.solvable_algEquiv_adicCompletion (Q := 𝔮) (q := q) hq)
  obtain ⟨α, hα⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
      𝔮 q hq
  have hdvd : Module.finrank (𝔮.adicCompletion K) (q.adicCompletion L') ∣
      Nat.card ↥(groupCohomology
        (Rep.ofAlgebraAutOnUnits (𝔮.adicCompletion K) (q.adicCompletion L')) 2) := by
    rw [← hα]
    exact addOrderOf_dvd_natCard α
  have heq : Nat.card ↥(groupCohomology
        (Rep.ofAlgebraAutOnUnits (𝔮.adicCompletion K) (q.adicCompletion L')) 2) =
      Module.finrank (𝔮.adicCompletion K) (q.adicCompletion L') :=
    le_antisymm hub (Nat.le_of_dvd Nat.card_pos hdvd)
  rw [hcard, heq]
  exact hfr.symm


/-! ## The target -/

/-- **`unitsLevelH2_card`**: the second cohomology of the units at the top level is cyclic of
order the degree — `|H²(Gal(L/K_𝔮), Lˣ)| = [L : K_𝔮]` — for `L` a finite Galois intermediate field
of the separable closure of the `𝔮`-adic completion of a number field `K`. -/
theorem unitsLevelH2_card
    (K : Type) [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K)
      (SeparableClosure (𝔮.adicCompletion K))) :
    Nat.card (NK.HassePrinciple.UnitsLevelH2
      (K := 𝔮.adicCompletion K) (K' := SeparableClosure (𝔮.adicCompletion K)) ⊤ L)
      = Module.finrank (𝔮.adicCompletion K) ↥L := by
  rw [natCard_unitsLevelH2_top_eq (K := 𝔮.adicCompletion K)
    (K' := SeparableClosure (𝔮.adicCompletion K)) L]
  exact natCard_groupCohomology_two_units_adicCompletion_eq_finrank 𝔮

end NK.NUV2.ABHN
