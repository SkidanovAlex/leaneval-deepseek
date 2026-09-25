import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_neg_two_of_commutative
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.map_eq_zero_of_mono_valuation
import Submission.Commons.RepresentationTheory.GroupCohomology.mono_map_of_isZero_kernel
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_quotientToInvariants_le_of_twist
import Submission.Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units
import Submission.Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field_of_type_zero
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_topAlgEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory Representation
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

/-- **The invariant map for unramified extensions, cardinality form.**  Let `L / K` be a finite
Galois extension of number fields and `q | Q` a prime with ramification index `e = 1`, so that the
local extension `L_q / K_Q` is unramified (hence cyclic Galois).  Then the second group cohomology
of the units of `L_q` has cardinality `[L_q : K_Q]`.

This is Milne, *Class Field Theory*, III.1.7 (the invariant map `H²(L_q/K_Q) ≅ (1/f)ℤ/ℤ`),
obtained here from the cyclic periodicity
(`natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic`), the identification of
`Ĥ⁰` with the norm quotient (`natCard_tateCohomology_zero_units`) and the unramified norm index
theorem (`..._of_ramificationIdx_eq_one`). -/
theorem natCard_groupCohomology_two_units_of_ramificationIdx_eq_one
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 2) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  haveI hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one Q q hq h1
  letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
  calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 2)
      = Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 0) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic g hg _
    _ = Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) :=
        Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units (Q.adicCompletion K) (q.adicCompletion L)
    _ = Nat.card (Abelianization (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) :=
        Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_ramificationIdx_eq_one Q q hq h1
    _ = Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
        rw [Nat.card_congr (Abelianization.equivOfComm).symm.toEquiv]
        exact IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (q.adicCompletion L)





/-- **Tate's theorem gives the norm index theorem from the existence of a fundamental class.**

Let `E / B` be a finite *abelian* Galois extension of fields.  If
`H¹(Gal(E/B), Eˣ) = 0`, if `|H²(Gal(N/B), Nˣ)| = |Gal(N/B)|` for every intermediate field `N`
(equivalently, for every subgroup of `Gal(E/B)`) and if `α ∈ H²(Gal(E/B), Eˣ)` has order
`[E : B]` (a *fundamental class*), then the norm index theorem holds:
`|Bˣ ⧸ N_{E/B}(Eˣ)| = [E : B]`.

This is the assembly step of the local norm index theorem: the deep input is the existence of
`α` (the fundamental class of local class field theory); the passage to the norm index is Tate's
theorem `natCard_tateCohomology_eq_of_fundamental_class` combined with
`natCard_tateCohomology_zero_units` and `Ĥ^{-2}(G,ℤ) ≅ Gᵃᵇ`. -/
theorem natCard_quotient_units_range_norm_eq_card_of_fundamental_class
    {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    (h1 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1))
    (h2 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) = Nat.card H)
    (α : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
    (hα : addOrderOf α = Nat.card (E ≃ₐ[B] E)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (E ≃ₐ[B] E) := by
  letI : CommGroup (E ≃ₐ[B] E) := { (inferInstance : Group (E ≃ₐ[B] E)) with mul_comm := hcomm }
  haveI : Group.IsSolvable (E ≃ₐ[B] E) := inferInstance
  have hTate :=
    Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
      (Rep.ofAlgebraAutOnUnits B E) h1 h2 α hα
  have hzero := Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units B E
  have hneg :=
    Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_neg_two_of_commutative
      (E ≃ₐ[B] E) hcomm
  rw [← hzero, ← hTate, hneg]

section OrdMaps

open CategoryTheory Representation

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The underlying map of the order map is surjective.**  The valuation `(L_q)ˣ → ℤ` is
surjective.  (The full `Rep`-level morphism `unitsValRepHom : Rep.ofAlgebraAutOnUnits K L ⟶
Rep.trivial ℤ Gal(L_q/K_Q) ℤ` is the "order map" `ord` of the unramified twist; see
`NOTE_session27_twist_route.md` §2 for the exact elaboration problem met when trying to build it:
the carrier `↥(Rep.ofAlgebraAutOnUnits R M)` is definitionally but not syntactically
`Additive (Mˣ)`, which defeats the `rw [Rep.ofMulDistribMulAction_ρ_apply_apply]` step of the
intertwining proof.  Note that both
`(Rep.ofAlgebraAutOnUnits K L).ρ g v = Additive.ofMul (g • v.toMul)` and
`Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g v) = g • v.toMul`
are `rfl` in a context where `v : Additive Lˣ` is *syntactically* typed.) -/
theorem unitsValLogRepHom_surj_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Function.Surjective (fun u : Additive (q.adicCompletion L)ˣ =>
      Multiplicative.toAdd (Commons.NumberTheory.NumberField.Completion.unitsValLog
        (q.adicCompletion L) u.toMul)) := by
  intro n
  obtain ⟨u, hu⟩ :=
    Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective L q
      (Multiplicative.ofAdd n)
  exact ⟨Additive.ofMul u, by simp [hu]⟩

end OrdMaps


section TwistFactorization

open CategoryTheory.Limits

/-- **Variables-first form of the factorization** (`map_comp`, backward).

For normal subgroups `M`, `N` (no nesting), a `ℤ[G ⧸ M]`-representation `A'`, a `ℤ[G]`-module `B`,
a `ℤ[N]`-module `C` and morphisms `φ : Rep.res (mk' M) A' ⟶ B`, `ψ : Rep.res N.subtype B ⟶ C`,
the composite `map (mk' M) φ 2 ≫ map N.subtype ψ 2` equals `map (N ↪ G ⧸ M) (φ_* ≫ ψ) 2`.

Because `φ` and `ψ` are *variables*, this elaboration never unfolds the `Rep.res` instance
diamonds (which is what makes the specialised form expensive). -/
theorem map_comp_infNatTrans_resNatTrans
    {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    {A' : Rep.{0,0,0} ℤ (G ⧸ M)} {B : Rep.{0,0,0} ℤ G} {C : Rep.{0,0,0} ℤ N}
    (φ : Rep.res (QuotientGroup.mk' M) A' ⟶ B) (ψ : Rep.res N.subtype B ⟶ C) :
    CategoryStruct.comp (groupCohomology.map (QuotientGroup.mk' M) φ 2)
        (groupCohomology.map N.subtype ψ 2)
      = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype)
          (Rep.resMap N.subtype φ ≫ ψ) 2 :=
  (groupCohomology.map_comp (QuotientGroup.mk' M) N.subtype φ ψ 2).symm

variable {G : Type} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal] (A : Rep.{0,0,0} ℤ G)

noncomputable local instance instAV2 : Module ℤ A.V := A.hV2

noncomputable local instance instInv2 :
    Module ℤ ↥(Representation.invariants (MonoidHom.comp A.ρ M.subtype)) :=
  (Representation.invariants (MonoidHom.comp A.ρ M.subtype)).module

set_option maxHeartbeats 4000000 in
/-- The factorization for the twist, by ascribing the coefficient morphisms. -/
theorem resNatTrans_comp_infNatTrans_eq_map
    :
    CategoryStruct.comp ((groupCohomology.infNatTrans ℤ M 2).app A)
        ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A)
      = groupCohomology.map ((QuotientGroup.mk' M).comp N.subtype)
          (Rep.resMap N.subtype (Rep.ofHom (A.ρ.quotientToInvariants_lift M))) 2 := by
  rw [groupCohomology.infNatTrans_app, groupCohomology.resNatTrans_app]
  exact (map_comp_infNatTrans_resNatTrans M N
      (φ := (Rep.ofHom (A.ρ.quotientToInvariants_lift M) :
        Rep.res (QuotientGroup.mk' M) (A.quotientToInvariants M) ⟶ A))
      (ψ := (𝟙 (Rep.res N.subtype A) :
        Rep.res N.subtype A ⟶ Rep.res N.subtype A))).trans
    (by rw [Category.comp_id]; rfl)


/-- **Functoriality of `map f` in the coefficient, for an arbitrary group homomorphism.**

For `f : H →* K`, `φ : Rep.res f A ⟶ B` and `ψ : Rep.res (MonoidHom.id H) B ⟶ C` (note
`Rep.res (MonoidHom.id H) B = B` definitionally, so `ψ` may be any morphism of `H`-representations
with source `B`), `map f (φ ≫ ψ) n = map f φ n ≫ map (MonoidHom.id H) ψ n`.

This is `groupCohomology.map_comp` with the second homomorphism specialised to the identity, moved
across by `groupCohomology.map_congr` (which compares coefficient morphisms through their underlying
linear maps, so the `Rep.res`-shape is never inverted).  It is the form in which the unramified twist
consumes the `ord`-comparison. -/
theorem map_comp_of_res {H K : Type} [Group H] [Group K] (f : H →* K)
    {A : Rep ℤ K} {B C : Rep ℤ H}
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res (MonoidHom.id H) B ⟶ C) (n : ℕ) :
    groupCohomology.map f (φ ≫ ψ) n
      = groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id H) ψ n := by
  have hcomp := groupCohomology.map_comp f (MonoidHom.id H) φ ψ n
  have hcongr : groupCohomology.map (f.comp (MonoidHom.id H))
        (Rep.resMap (MonoidHom.id H) φ ≫ ψ) n
      = groupCohomology.map f (φ ≫ ψ) n :=
    groupCohomology.map_congr (MonoidHom.comp_id f) (by rfl) n
  exact hcongr.symm.trans hcomp

end TwistFactorization


/-- **The fundamental class at an arbitrary `p`-adic base** (Milne, *CFT*, III.2): for `F` a
finite extension of `Q.adicCompletion K` (`K` a number field, `Q` a finite place) and `E / F`
finite Galois, there is `α ∈ H²(Gal(E/F), Eˣ)` of order `[E : F]`.

This is obtained from the published number-field form
`exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion` by realising `F` and then
`E` as completions of number fields (`exists_algEquiv_adicCompletion_of_finiteDimensional`,
`exists_galois_adicCompletion_of_finiteDimensional`) and transporting along the `AddEquiv`s
`addEquiv_groupCohomology_two_units_baseRingEquiv`, `addEquiv_groupCohomology_two_units_topAlgEquiv`
(`addOrderOf` is preserved by `AddEquiv.addOrderOf_eq`, and the two `finrank`s agree by
`finrank_eq_of_algebraMap_eq` and `AlgEquiv.toLinearEquiv_finrank_eq`).  Declared `private` so as
not to clash with the public commons lemma of the same name that is being proved in parallel. -/
private theorem exists_addOrderOf_eq_finrank_groupCohomology_two_units
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
  letI : Field L := hLf
  letI : NumberField L := hLn
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
  letI : Field L' := hL'f
  letI : NumberField L' := hL'n
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

/-- Any intermediate field of a finite *abelian* Galois extension is Galois over the base. -/
private lemma isGalois_intermediateField {B E : Type*} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) : IsGalois B ↥M := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  haveI h : IsGalois B ↥(IntermediateField.fixedField M.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup M.fixingSubgroup
  exact (IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M) ▸ h

/-- The Galois group of an intermediate field of a finite *abelian* Galois extension is
commutative. -/
private lemma commute_intermediateField {B E : Type*} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) :
    ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI hH : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  let e := IsGalois.normalAutEquivQuotient (K := B) (L := E) M.fixingSubgroup
  have hq : ∀ x y : (E ≃ₐ[B] E) ⧸ M.fixingSubgroup, x * y = y * x := by
    intro x y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x' y']
  have key : ∀ a b : ↥(IntermediateField.fixedField M.fixingSubgroup) ≃ₐ[B]
      ↥(IntermediateField.fixedField M.fixingSubgroup), a * b = b * a := by
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul, hq]
  rw [IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M] at key
  exact key

/-- **The target at universe 0** (all of `K, B, E` in `Type`). -/
private theorem target_univ0
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    ∀ (M : IntermediateField B E) (p : ℕ), IsPGroup p (M ≃ₐ[B] M) →
      Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B))) =
        Nat.card (M ≃ₐ[B] M) := by

  intro M p hp
  haveI hgalM : IsGalois B ↥M := isGalois_intermediateField hcomm M
  haveI hfdMt : FiniteDimensional (Q.adicCompletion K) ↥M :=
    FiniteDimensional.trans (Q.adicCompletion K) B ↥M
  have hcommM : ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a := commute_intermediateField hcomm M
  haveI : IsMulCommutative (↥M ≃ₐ[B] ↥M) := IsMulCommutative.of_comm hcommM
  have h1 : ∀ H : Subgroup (↥M ≃ₐ[B] ↥M),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B ↥M)) 1) :=
    fun H => subsingleton_groupCohomology_one_res_units H
  have h2 : ∀ H : Subgroup (↥M ≃ₐ[B] ↥M),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B ↥M)) 2) =
        Nat.card H := by
    intro H
    rw [NatCardP9.natCard_groupCohomology_two_res_units H]
    let L : IntermediateField B ↥M := IntermediateField.fixedField H
    have hcommH : ∀ a b : ↥M ≃ₐ[↥L] ↥M, a * b = b * a := by
      have hHcomm : ∀ x y : ↥H, x * y = y * x := fun x y => Subtype.ext (by
        show (x : ↥M ≃ₐ[B] ↥M) * (y : ↥M ≃ₐ[B] ↥M) = (y : ↥M ≃ₐ[B] ↥M) * (x : ↥M ≃ₐ[B] ↥M)
        exact hcommM x y)
      intro a b
      have hH : (IntermediateField.subgroupEquivAlgEquiv H).symm (a * b)
          = (IntermediateField.subgroupEquivAlgEquiv H).symm (b * a) := by
        rw [map_mul, map_mul]
        exact hHcomm _ _
      exact (IntermediateField.subgroupEquivAlgEquiv H).symm.injective hH
    haveI htower : IsScalarTower (Q.adicCompletion K) ↥L ↥M :=
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B ↥L x]
        rw [← IsScalarTower.algebraMap_apply B ↥L ↥M]
        exact IsScalarTower.algebraMap_apply (Q.adicCompletion K) B ↥M x
    haveI hfdL : FiniteDimensional (Q.adicCompletion K) ↥L :=
      FiniteDimensional.trans (Q.adicCompletion K) B ↥L
    haveI hfdE : FiniteDimensional (Q.adicCompletion K) ↥M :=
      FiniteDimensional.trans (Q.adicCompletion K) B ↥M
    have hle := natCard_groupCohomology_two_units_le_finrank_of_abelian (Q := Q)
      (B := ↥L) (E := ↥M) hcommH
    have hge := groupCohomology_two_units_ge_finrank (Q := Q) (F := ↥L) (E := ↥M)
    rw [le_antisymm hle hge, ← IsGalois.card_aut_eq_finrank ↥L ↥M]
    exact Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv H).symm.toEquiv
  obtain ⟨α, hα⟩ := exists_addOrderOf_eq_finrank_groupCohomology_two_units (Q := Q) (F := B) (E := ↥M)
  rw [← IsGalois.card_aut_eq_finrank B ↥M] at hα
  exact natCard_quotient_units_range_norm_eq_card_of_fundamental_class hcommM h1 h2 α hα


theorem natCard_quotient_units_range_norm_pgroup_intermediate_field
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    ∀ (M : IntermediateField B E) (p : ℕ), IsPGroup p (M ≃ₐ[B] M) →
      Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B))) =
        Nat.card (M ≃ₐ[B] M) :=
  natCard_quotient_units_range_norm_pgroup_intermediate_field_of_type_zero
    target_univ0 (Q := Q) hcomm


end Commons.NumberTheory.NumberField.Completion
