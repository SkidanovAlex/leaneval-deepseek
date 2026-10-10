import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_of_commute
import Submission.Commons.RepresentationTheory.TateCohomology.nonempty_mulEquiv_quotient_units_range_norm_tateCohomology_zero

open CategoryTheory Representation

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable

namespace Commons.NumberTheory.NumberField.Completion
namespace ArtinMap

/-- **Tate's theorem, isomorphism form.** -/
theorem addEquiv_tateCohomology_of_fundamental_class {G : Type} [Group G] [Fintype G]
    [Group.IsSolvable G] (C : Rep.{0,0,0} ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) :
    Nonempty (tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ tateCohomology C 0) := by
  obtain ⟨z, hzα, hz⟩ := NU.exists_normalized_cocycle C α
  have hacyc := NU.subsingleton_tateCohomology_Sprint C z hz α hzα hα h1 h2
  have hA1 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ (-1)) := hacyc (-1)
  have hA2 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ ((-1 : ℤ) + 1)) :=
    hacyc ((-1 : ℤ) + 1)
  obtain ⟨e2⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.AShortZ C z hz) (NU.AShortZ_shortExact C z hz) (-1) hA1 hA2
  have hL1 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ (-2)) :=
    NU.subsingleton_tateCohomology_leftRegular G (-2)
  have hL2 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ ((-2 : ℤ) + 1)) :=
    NU.subsingleton_tateCohomology_leftRegular G ((-2 : ℤ) + 1)
  obtain ⟨e1⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.IShort (G := G)) (NU.IShort_shortExact (G := G)) (-2) hL1 hL2
  exact ⟨(e1.trans e2).toAddEquiv⟩




theorem nonempty_mulEquiv_tateCohomology_neg_two {G : Type} [Group G] [Fintype G]
    (hcomm : ∀ a b : G, a * b = b * a) :
    Nonempty (Multiplicative ↥(tateCohomology (Rep.trivial ℤ G ℤ) (-2)) ≃* G) := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  obtain ⟨e⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization G
  exact ⟨(AddEquiv.toMultiplicative e).trans (Abelianization.equivOfComm).symm⟩




/-- The abstract core: a fundamental class of order `#Gal(E/B)` gives the reciprocity
isomorphism `Bˣ ⧸ N ⧸ ≃* Gal(E/B)`. -/
theorem exists_mulEquiv_quotient_units_range_norm_of_fundamental_class
    {B E : Type} [Field B] [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    (h1 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1))
    (h2 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) = Nat.card H)
    (α : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
    (hα : addOrderOf α = Nat.card (E ≃ₐ[B] E)) :
    Nonempty ((Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) ≃*
      (E ≃ₐ[B] E)) := by
  letI : CommGroup (E ≃ₐ[B] E) := { (inferInstance : Group (E ≃ₐ[B] E)) with mul_comm := hcomm }
  haveI : Group.IsSolvable (E ≃ₐ[B] E) := inferInstance
  obtain ⟨e0⟩ := Commons.RepresentationTheory.TateCohomology.nonempty_mulEquiv_quotient_units_range_norm_tateCohomology_zero B E
  obtain ⟨e1⟩ := addEquiv_tateCohomology_of_fundamental_class
    (Rep.ofAlgebraAutOnUnits B E) h1 h2 α hα
  obtain ⟨e2⟩ := nonempty_mulEquiv_tateCohomology_neg_two hcomm
  exact ⟨e0.trans ((AddEquiv.toMultiplicative e1).symm.trans e2)⟩



/-- **The `Type 0` local Artin map, conditional on the fundamental class.** -/
theorem exists_surjective_ker_norm_of_fundamental_class
    (hfund : ∀ {K : Type} [Field K] [NumberField K]
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      {F E : Type} [Field F] [Field E]
      [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) F E]
      [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
      [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E],
      ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
        addOrderOf α = Module.finrank F E)
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    ∃ Φ : (Q.adicCompletion K)ˣ →* (E ≃ₐ[Q.adicCompletion K] E),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        E →* Q.adicCompletion K)) := by
  have h1 : ∀ H : Subgroup (E ≃ₐ[Q.adicCompletion K] E),
      Subsingleton (groupCohomology (Rep.res H.subtype
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E)) 1) :=
    fun H => Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units H
  have h2 : ∀ H : Subgroup (E ≃ₐ[Q.adicCompletion K] E),
      Nat.card (groupCohomology (Rep.res H.subtype
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E)) 2) = Nat.card H := by
    intro H
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.natCard_groupCohomology_two_res_units H]
    let L : IntermediateField (Q.adicCompletion K) E := IntermediateField.fixedField H
    have hcommH : ∀ a b : E ≃ₐ[↥L] E, a * b = b * a := by
      have hHcomm : ∀ x y : ↥H, x * y = y * x := fun x y => Subtype.ext (by
        show (x : E ≃ₐ[Q.adicCompletion K] E) * (y : E ≃ₐ[Q.adicCompletion K] E)
          = (y : E ≃ₐ[Q.adicCompletion K] E) * (x : E ≃ₐ[Q.adicCompletion K] E)
        exact hcomm x y)
      intro a b
      have hH : (IntermediateField.subgroupEquivAlgEquiv H).symm (a * b)
          = (IntermediateField.subgroupEquivAlgEquiv H).symm (b * a) := by
        rw [map_mul, map_mul]
        exact hHcomm _ _
      exact (IntermediateField.subgroupEquivAlgEquiv H).symm.injective hH
    haveI : IsMulCommutative (E ≃ₐ[Q.adicCompletion K] E) := IsMulCommutative.of_comm hcomm
    haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
    have hle := Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
      (Q := Q) (B := ↥L) (E := E) hcommH
    have hge := Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
      (Q := Q) (F := ↥L) (E := E)
    rw [le_antisymm hle hge, ← IsGalois.card_aut_eq_finrank ↥L E]
    exact Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv H).symm.toEquiv
  obtain ⟨α, hα⟩ := hfund (Q := Q) (F := Q.adicCompletion K) (E := E)
  rw [← IsGalois.card_aut_eq_finrank (Q.adicCompletion K) E] at hα
  obtain ⟨ψ⟩ := exists_mulEquiv_quotient_units_range_norm_of_fundamental_class hcomm h1 h2 α hα
  refine ⟨ψ.toMonoidHom.comp (QuotientGroup.mk'
    (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K)))), ?_, ?_⟩
  · exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [← MonoidHom.comap_ker ψ.toMonoidHom (QuotientGroup.mk' _),
      MonoidHom.ker_eq_bot ψ.toMonoidHom ψ.injective, MonoidHom.comap_bot,
      QuotientGroup.ker_mk']



/-- Norm compatibility: a compatible pair of ring isomorphisms transports the field norm. -/
theorem norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] [FiniteDimensional B E] [FiniteDimensional B₀ E₀]
    [IsGalois B E] [IsGalois B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (y : E) :
    eB (Algebra.norm B y) = Algebra.norm B₀ (eE y) := by
  refine FaithfulSMul.algebraMap_injective B₀ E₀ ?_
  rw [← h]
  have key : eE (algebraMap B E (Algebra.norm B y))
      = ∏ σ : E ≃ₐ[B] E,
          (Commons.NumberTheory.NumberField.Completion.algEquivConjUniv eB eE h σ) (eE y) := by
    rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [Commons.NumberTheory.NumberField.Completion.algEquivConjUniv_apply,
      RingEquiv.symm_apply_apply]
  rw [key, Algebra.norm_eq_prod_automorphisms (K := B₀) (L := E₀) (x := eE y)]
  refine Fintype.prod_bijective
    (Commons.NumberTheory.NumberField.Completion.algEquivConjEquivUniv eB eE h)
    (Commons.NumberTheory.NumberField.Completion.algEquivConjEquivUniv eB eE h).bijective _ _
    (fun σ => rfl)

open Commons.NumberTheory.NumberField.Completion in
/-- Transport of the Artin-map statement along a compatible pair of ring isomorphisms. -/
theorem exists_surjective_ker_norm_of_ringEquiv
    {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] [FiniteDimensional B E] [FiniteDimensional B₀ E₀]
    [IsGalois B E] [IsGalois B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x))
    (h₀ : ∃ Φ₀ : B₀ˣ →* (E₀ ≃ₐ[B₀] E₀),
      Function.Surjective Φ₀ ∧
      MonoidHom.ker Φ₀ = MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) :
    ∃ Φ : Bˣ →* (E ≃ₐ[B] E),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = MonoidHom.range (Units.map (Algebra.norm B : E →* B)) := by
  obtain ⟨Φ₀, hsurj, hker⟩ := h₀
  have hf_inj : Function.Injective (Units.map eB.toMulEquiv.toMonoidHom) := by
    intro a b hab
    apply Units.ext
    have h' := congrArg (fun t : B₀ˣ => (t : B₀)) hab
    rw [Units.coe_map, Units.coe_map] at h'
    exact eB.injective h'
  have hf_surj : Function.Surjective (Units.map eB.toMulEquiv.toMonoidHom) := by
    intro z
    refine ⟨Units.map eB.toMulEquiv.symm.toMonoidHom z, ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.coe_map]
    exact eB.apply_symm_apply (z : B₀)
  have hΨ_inj : Function.Injective ((algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom) := by
    intro a b hab
    have h' := congrArg (fun σ : E ≃ₐ[B] E => algEquivConjUniv eB eE h σ) hab
    have ha : algEquivConjUniv eB eE h
        ((algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom a) = a :=
      algEquivConjUniv_algEquivConjSymmUniv eB eE h a
    have hb : algEquivConjUniv eB eE h
        ((algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom b) = b :=
      algEquivConjUniv_algEquivConjSymmUniv eB eE h b
    rw [ha, hb] at h'
    exact h'
  have hΨ_surj : Function.Surjective ((algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom) := by
    intro σ
    exact ⟨algEquivConjUniv eB eE h σ, algEquivConjSymmUniv_algEquivConjUniv eB eE h σ⟩
  have hnorm : ∀ u : Eˣ,
      Units.map eB.toMulEquiv.toMonoidHom (Units.map (Algebra.norm B : E →* B) u)
        = Units.map (Algebra.norm B₀ : E₀ →* B₀)
            (Units.map eE.toMulEquiv.toMonoidHom u) := by
    intro u
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact norm_eq_of_ringEquiv eB eE h (u : E)
  have hrange : Subgroup.map (Units.map eB.toMulEquiv.toMonoidHom)
        (MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
      = MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hfw⟩ := Subgroup.mem_map.mp hz
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hw
      refine MonoidHom.mem_range.mpr ⟨Units.map eE.toMulEquiv.toMonoidHom u, ?_⟩
      apply Units.ext
      rw [← hnorm u]
      exact congrArg (fun t : B₀ˣ => (t : B₀)) hfw
    · intro hz
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hz
      refine Subgroup.mem_map.mpr
        ⟨Units.map (Algebra.norm B : E →* B) (Units.map eE.toMulEquiv.symm.toMonoidHom u),
          MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
      apply Units.ext
      have h2 : (Units.map eE.toMulEquiv.toMonoidHom
          (Units.map eE.toMulEquiv.symm.toMonoidHom u) : E₀ˣ) = u := by
        apply Units.ext
        rw [Units.coe_map, Units.coe_map]
        exact eE.apply_symm_apply (u : E₀)
      rw [hnorm, h2, hu]
  refine ⟨(algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom.comp
    (Φ₀.comp (Units.map eB.toMulEquiv.toMonoidHom)), ?_, ?_⟩
  · exact hΨ_surj.comp (hsurj.comp hf_surj)
  · rw [← MonoidHom.comap_ker ((algEquivConjMulEquivUniv eB eE h).symm.toMonoidHom)
        (Φ₀.comp (Units.map eB.toMulEquiv.toMonoidHom)),
      MonoidHom.ker_eq_bot _ hΨ_inj, MonoidHom.comap_bot,
      ← MonoidHom.comap_ker Φ₀ (Units.map eB.toMulEquiv.toMonoidHom), hker, ← hrange]
    exact Subgroup.comap_map_eq_self_of_injective
      (f := Units.map eB.toMulEquiv.toMonoidHom)
      (H := MonoidHom.range (Units.map (Algebra.norm B : E →* B))) hf_inj



/-- **The local fundamental class at an arbitrary `p`-adic base**
(Milne, *CFT*, III.2): for `F` a finite extension of the `p`-adic field `Q.adicCompletion K`
(`K` a number field, `Q` a finite place) and `E / F` finite Galois, there is
`α ∈ H²(Gal(E/F), Eˣ)` of additive order `[E : F]`.

(Obtained from the number-field form
`exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion` by realising `F` and then
`E` as completions of number fields and transporting along the `AddEquiv`s
`addEquiv_groupCohomology_two_units_baseRingEquiv`, `addEquiv_groupCohomology_two_units_topAlgEquiv`.)
-/
theorem exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E]
    [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E] :
    ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
      addOrderOf α = Module.finrank F E := by
  obtain ⟨L : Type, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (Q := Q) (B := F)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (q.adicCompletion L) E := ((algebraMap F E).comp e.symm.toRingHom).toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) E).comp e.toRingHom = algebraMap F E := by
    ext x
    show algebraMap (q.adicCompletion L) E (e x) = algebraMap F E x
    rw [show algebraMap (q.adicCompletion L) E = (algebraMap F E).comp e.symm.toRingHom from rfl]
    simp [RingHom.comp_apply]
  haveI : FiniteDimensional (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.finiteDimensional_transport e.toRingEquiv hhe
  haveI : IsGalois (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.isGalois_transport e.toRingEquiv hhe
  obtain ⟨L' : Type, hL'f, hL'n, hL'a, q', hq', hgal', ⟨e'⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
      (Q := q) (B := E)
  letI : Algebra L L' := hL'a
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  haveI : IsGalois L L' := hgal'
  obtain ⟨α', hα'⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
      (L := L) (L' := L') q q' hq'
  obtain ⟨h₂⟩ :=
    Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_topAlgEquiv
      (F := q.adicCompletion L) e'
  obtain ⟨h₁⟩ :=
    Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
      (M := F) (M' := q.adicCompletion L) (E := E) e.toRingEquiv hhe
  refine ⟨h₁.symm (h₂.symm α'), ?_⟩
  rw [AddEquiv.addOrderOf_eq, AddEquiv.addOrderOf_eq, hα',
    ← Commons.NumberTheory.NumberField.Completion.finrank_eq_of_algebraMap_eq
      (E := E) e.toRingEquiv hhe,
    (AlgEquiv.toLinearEquiv e').finrank_eq]


/-- **The universe bridge**: the `Type 0` Artin map statement implies the statement in
arbitrary universes. -/
theorem exists_surjective_artinMap_of_abelian_local_universe_bridge
    (h0 : ∀ {K : Type} [Field K] [NumberField K]
        (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
        [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
        (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a),
        ∃ Φ : (Q.adicCompletion K)ˣ →* (E ≃ₐ[Q.adicCompletion K] E),
          Function.Surjective Φ ∧
          MonoidHom.ker Φ = MonoidHom.range
            (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K)))
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    ∃ Φ : (Q.adicCompletion K)ˣ →* (E ≃ₐ[Q.adicCompletion K] E),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K)) := by
  classical
  -- (1) a `Type 0` model `K₀` of the number field, with its canonical `ℚ`-algebra structure
  obtain ⟨K₀, hK₀f, ⟨eKr⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.S31.exists_typeZero_field_ringEquiv K
  haveI : CharZero K₀ := by
    refine ⟨fun m n hmn => ?_⟩
    have h2 : ((m : K)) = ((n : K)) := by
      have h := congrArg eKr.symm hmn
      simpa using h
    exact Nat.cast_injective h2
  haveI : FiniteDimensional ℚ K₀ :=
    Module.Finite.of_surjective ((eKr.toRatAlgEquiv).toLinearEquiv.toLinearMap)
      (eKr.toRatAlgEquiv).toLinearEquiv.surjective
  haveI : NumberField K₀ := NumberField.mk
  have eK : K ≃ₐ[ℚ] K₀ := eKr.toRatAlgEquiv
  -- (2) transport the completion
  obtain ⟨Q₀, Φ, hΦ⟩ :=
    Commons.NumberTheory.NumberField.completion_ringEquiv_of_algEquiv eK Q
  -- (3) the `F₀`-algebra structure on `E`
  let g : Q₀.adicCompletion K₀ →+* E :=
    (algebraMap (Q.adicCompletion K) E).comp Φ.symm.toRingHom
  letI : Algebra (Q₀.adicCompletion K₀) E := g.toAlgebra
  have hΦc : ∀ x : Q.adicCompletion K, g (Φ x) = algebraMap (Q.adicCompletion K) E x := by
    intro x
    show (algebraMap (Q.adicCompletion K) E) (Φ.symm (Φ x)) = algebraMap (Q.adicCompletion K) E x
    rw [Φ.symm_apply_apply]
  have hcompat : ∀ x : Q.adicCompletion K,
      (RingEquiv.refl E) (algebraMap (Q.adicCompletion K) E x)
        = algebraMap (Q₀.adicCompletion K₀) E (Φ x) := by
    intro x
    show algebraMap (Q.adicCompletion K) E x = g (Φ x)
    rw [hΦc]
  haveI hfdE : FiniteDimensional (Q₀.adicCompletion K₀) E :=
    Commons.Algebra.Module.moduleFinite_of_ringEquiv Φ (RingEquiv.refl E) hcompat
  haveI hgalE : IsGalois (Q₀.adicCompletion K₀) E :=
    Commons.FieldTheory.Galois.isGalois_of_ringEquiv Φ (RingEquiv.refl E) hcompat
  -- (4) a `Type 0` model `E₀` of `E` over `F₀`
  obtain ⟨E₀, hE₀f, hE₀a, hE₀fd, ⟨eE⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_type_zero_field_of_finiteDimensional
      (F := Q₀.adicCompletion K₀) (E := E)
  letI : Algebra (Q₀.adicCompletion K₀) E₀ := hE₀a
  letI : FiniteDimensional (Q₀.adicCompletion K₀) E₀ := hE₀fd
  haveI hgalE₀ : IsGalois (Q₀.adicCompletion K₀) E₀ := IsGalois.of_algEquiv eE
  -- (5) the compatibility of the two transports
  have hcomp2 : ∀ x : Q.adicCompletion K,
      eE.toRingEquiv (algebraMap (Q.adicCompletion K) E x)
        = algebraMap (Q₀.adicCompletion K₀) E₀ (Φ x) := by
    intro x
    have h : algebraMap (Q.adicCompletion K) E x = g (Φ x) := (hΦc x).symm
    rw [h]
    show eE (algebraMap (Q₀.adicCompletion K₀) E (Φ x))
      = algebraMap (Q₀.adicCompletion K₀) E₀ (Φ x)
    exact eE.commutes (Φ x)
  -- (6) commutativity transports
  have hcomm₀ : ∀ a b : E₀ ≃ₐ[Q₀.adicCompletion K₀] E₀, a * b = b * a :=
    Commons.NumberTheory.NumberField.Completion.commute_of_commute_ringEquiv
      Φ eE.toRingEquiv hcomp2 hcomm
  -- (7) the `Type 0` statement and the transport back
  exact exists_surjective_ker_norm_of_ringEquiv Φ eE.toRingEquiv hcomp2
    (h0 (K := K₀) Q₀ hcomm₀)
end ArtinMap

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

/-- **The local Artin map of an abelian local extension** (the local reciprocity law, in the form
used in the proof of the Neukirch–Uchida theorem).

For a finite *abelian* Galois extension `L / K` of number fields, a finite place `Q` of `K` and a
place `q` of `L` lying over `Q`, there is a surjective group homomorphism from the unit group of
the `Q`-adic completion `K_Q` onto the Galois group of the local extension `L_q / K_Q` whose kernel
is exactly the group `N_{L_q/K_Q}(L_qˣ)` of norms of units. -/
theorem exists_mulEquiv_artinMap_of_commute {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ Φ : (Q.adicCompletion K)ˣ →* (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      Function.Surjective Φ ∧
        MonoidHom.ker Φ = MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  have hcomm' : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a :=
    Commons.NumberTheory.NumberField.Completion.localCommute_of_commute Q q hq hcomm
  refine ArtinMap.exists_surjective_artinMap_of_abelian_local_universe_bridge ?_ Q hcomm'
  intro K₀ hK₀f hK₀nf Q₀ E₀ hE₀f hAlg hFd hGal hcomm₀
  exact ArtinMap.exists_surjective_ker_norm_of_fundamental_class
    ArtinMap.exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux Q₀ hcomm₀

end Commons.NumberTheory.NumberField.Completion
