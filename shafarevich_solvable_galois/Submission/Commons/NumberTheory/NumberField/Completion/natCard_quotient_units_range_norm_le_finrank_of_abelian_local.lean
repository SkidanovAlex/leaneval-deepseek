import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_of_isGalois
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic

open scoped NumberField WithZero Valued
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Group-theoretic preliminaries -/

/-- For `CommGroup`s `A`, `B`, `C` and monoid homs `f : A →* C`, `g : B →* A`: the quotient
`C ⧸ range (f.comp g)` has cardinality at most the product of the cardinalities of
`C ⧸ range f` and `A ⧸ range g` (assuming `A ⧸ range g` is finite).  This is the elementary
"multiplicativity" of the norm index along a tower. -/
lemma natCard_quotient_range_comp_le {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    (f : A →* C) (g : B →* A) [Finite (A ⧸ MonoidHom.range g)] :
    Nat.card (C ⧸ MonoidHom.range (f.comp g)) ≤
      Nat.card (C ⧸ MonoidHom.range f) * Nat.card (A ⧸ MonoidHom.range g) := by
  set X : Subgroup C := MonoidHom.range (f.comp g)
  set Y : Subgroup C := MonoidHom.range f
  have hle : X ≤ Y := by
    rintro x ⟨b, rfl⟩
    exact ⟨g b, rfl⟩
  let φY : A →* Y :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a b) }
  have hXle : MonoidHom.range g ≤ ((QuotientGroup.mk' (X.subgroupOf Y)).comp φY).ker := by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨b, rfl⟩
  let ψ : A ⧸ MonoidHom.range g →* Y ⧸ X.subgroupOf Y :=
    QuotientGroup.lift (MonoidHom.range g) ((QuotientGroup.mk' (X.subgroupOf Y)).comp φY) hXle
  have hψsurj : Function.Surjective ψ := by
    intro y
    induction y using Quotient.inductionOn with
    | h z =>
      obtain ⟨a, ha⟩ : ∃ a, f a = (z : Y) := z.2
      refine ⟨QuotientGroup.mk a, ?_⟩
      change ((QuotientGroup.mk' (X.subgroupOf Y)).comp φY) a = QuotientGroup.mk z
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext ha
  calc Nat.card (C ⧸ X) = X.index := (Subgroup.index_eq_card X).symm
    _ = X.relIndex Y * Y.index := (Subgroup.relIndex_mul_index hle).symm
    _ = Nat.card (Y ⧸ X.subgroupOf Y) * Nat.card (C ⧸ Y) := by
          rw [Subgroup.relIndex, Subgroup.index_eq_card Y, Subgroup.index_eq_card]
    _ ≤ Nat.card (A ⧸ MonoidHom.range g) * Nat.card (C ⧸ Y) :=
          Nat.mul_le_mul_right _ (Nat.card_le_card_of_surjective ψ hψsurj)
    _ = Nat.card (C ⧸ MonoidHom.range f) * Nat.card (A ⧸ MonoidHom.range g) := by
          rw [Nat.mul_comm]

/-- A finite abelian group `G ≠ 1` has a proper subgroup `H < ⊤` with `G ⧸ H` cyclic. -/
lemma exists_maximal_subgroup_quotient_cyclic (G : Type*) [Group G] [IsMulCommutative G]
    [Finite G] [Nontrivial G] :
    ∃ H : Subgroup G, H < ⊤ ∧ IsCyclic (G ⧸ H) := by
  classical
  haveI : Finite (Subgroup G) := inferInstance
  have hne : ({H : Subgroup G | H < ⊤} : Set (Subgroup G)).Nonempty :=
    ⟨⊥, by simpa using (bot_lt_top : (⊥ : Subgroup G) < ⊤)⟩
  obtain ⟨H, hHmax⟩ :=
    (Set.toFinite _ : ({H : Subgroup G | H < ⊤} : Set (Subgroup G)).Finite).exists_maximal hne
  haveI : H.Normal := Subgroup.normal_of_isMulCommutative H
  have hHlt : H < ⊤ := hHmax.1
  have hstep : ∀ K : Subgroup G, H ≤ K → K ≤ H ∨ K = ⊤ := by
    intro K hK
    by_cases hKt : K < ⊤
    · left
      exact hHmax.2 (by simpa using hKt) hK
    · right
      have htop : (⊤ : Subgroup G) ≤ K := by
        by_contra h
        exact hKt (lt_of_le_of_ne le_top (fun hEq => h (le_of_eq hEq.symm)))
      exact le_antisymm le_top htop
  haveI : Nontrivial (G ⧸ H) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    haveI : Subsingleton (G ⧸ H) := hsub
    have hGal : H = ⊤ := by
      rw [eq_top_iff]
      intro x
      have h1 : (QuotientGroup.mk x : G ⧸ H) = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.eq_one_iff] at h1
      simpa using h1
    exact absurd hGal (ne_of_lt hHlt)
  obtain ⟨t, ht⟩ := exists_ne (1 : G ⧸ H)
  refine ⟨H, hHlt, ?_⟩
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨t, ?_⟩
  by_contra hN
  let K : Subgroup G := (Subgroup.zpowers t).comap (QuotientGroup.mk' H)
  have hHK : H ≤ K := by
    intro x hx
    simp only [K, Subgroup.mem_comap]
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  rcases hstep K hHK with hKH | hKtop
  · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H t
    have hgK : g ∈ K := by
      simp only [K, Subgroup.mem_comap]
      rw [hg]
      exact Subgroup.mem_zpowers t
    have hgH : g ∈ H := hKH hgK
    rw [← hg, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).mpr hgH] at ht
    exact ht rfl
  · apply hN
    rw [eq_top_iff]
    intro c hc
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H c
    have hgK : g ∈ K := by rw [hKtop]; trivial
    simp only [K, Subgroup.mem_comap] at hgK
    exact hgK

/-! ## Realization of finite Galois extensions of `adicCompletion`s -/

universe u

/-- Every finite Galois extension `E` of `Q.adicCompletion K` is isomorphic, as a
`Q.adicCompletion K`-algebra, to a completion `q.adicCompletion L` of a finite Galois extension
`L / K` of number fields at a place `q` lying over `Q`. -/
theorem exists_realization {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      Nonempty (E ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  obtain ⟨f, hf0, hfsep, ⟨e₁⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adjoin_rootSet_of_isGalois
      (F := Q.adicCompletion K) (E := E)
  obtain ⟨ε, hεpos, hε⟩ :=
    Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close (K := Q.adicCompletion K) f hf0 hfsep
  obtain ⟨g, hgsup, hgdeg⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_map_supNorm_lt (K := K)
      (F := Q.adicCompletion K)
      (fun c ε hε => Commons.NumberTheory.NumberField.Completion.exists_dist_algebraMap_lt Q c ε hε)
      f ε hεpos
  set L : IntermediateField K (AlgebraicClosure (Q.adicCompletion K)) :=
    IntermediateField.adjoin K (g.rootSet (AlgebraicClosure (Q.adicCompletion K))) with hLdef
  set E' : IntermediateField (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)) :=
    IntermediateField.adjoin (Q.adicCompletion K)
      (g.rootSet (AlgebraicClosure (Q.adicCompletion K))) with hE'def
  have heq : IntermediateField.adjoin (Q.adicCompletion K)
      (f.rootSet (AlgebraicClosure (Q.adicCompletion K))) = E' := by
    rw [hE'def, ← Commons.NumberTheory.NumberField.Completion.map_rootSet_eq
      (K := K) (F := Q.adicCompletion K)
      (Fbar := AlgebraicClosure (Q.adicCompletion K)) g]
    exact hε (g.map (algebraMap K (Q.adicCompletion K))) hgdeg hgsup
  have e₂ : E ≃ₐ[Q.adicCompletion K] ↥E' := e₁.trans (IntermediateField.equivOfEq heq)
  haveI hLfd : FiniteDimensional K ↥L := by
    rw [hLdef]
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact IsAlgebraic.isIntegral (isAlgebraic_of_mem_rootSet hx)
  haveI hLnf : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hLgal : IsGalois K ↥L := by
    rw [hLdef]
    have hsplit : Polynomial.IsSplittingField K
        (↥(IntermediateField.adjoin K
          (g.rootSet (AlgebraicClosure (Q.adicCompletion K))))) g := by
      rw [IntermediateField.isSplittingField_iff]
      refine ⟨?_, rfl⟩
      exact (IntermediateField.splits_iff_mem (IsAlgClosed.splits _)).mpr
        (fun x hx => IntermediateField.subset_adjoin K _ hx)
    haveI : Normal K (↥(IntermediateField.adjoin K
        (g.rootSet (AlgebraicClosure (Q.adicCompletion K))))) :=
      Normal.of_isSplittingField (p := g) (hFEp := hsplit)
    exact Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hfinB : FiniteDimensional (Q.adicCompletion K) ↥E' := by
    refine IntermediateField.finiteDimensional_adjoin (fun x hx => ?_)
    exact IsAlgebraic.isIntegral (isAlgebraic_of_mem_rootSet
      (show x ∈ (g.map (algebraMap K (Q.adicCompletion K))).rootSet
          (AlgebraicClosure (Q.adicCompletion K)) from
        (Commons.NumberTheory.NumberField.Completion.map_rootSet_eq (K := K)
          (F := Q.adicCompletion K) (Fbar := AlgebraicClosure (Q.adicCompletion K)) g).symm ▸ hx))
  obtain ⟨φ, hφ⟩ :=
    Commons.NumberTheory.NumberField.Completion.surjective_tensorProduct_adjoin_rootSet
      (K := K) (F := Q.adicCompletion K) g
  letI : Algebra (Q.adicCompletion K) (TensorProduct K ↥L (Q.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI hfin : Fintype {q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥L) // q.asIdeal.LiesOver Q.asIdeal} :=
    Fintype.ofEquiv (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥L))
      (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q).symm
  letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) //
      q.asIdeal.LiesOver Q.asIdeal},
      Algebra (Q.adicCompletion K) (q.1.adicCompletion ↥L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  obtain ⟨ψ⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
      K ↥L Q
  have hsurj : Function.Surjective (φ.comp ψ.symm.toAlgHom) := fun y =>
    let ⟨x, hx⟩ := hφ y
    ⟨ψ x, by rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, hx]⟩
  obtain ⟨q, ⟨e_q⟩⟩ := Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
    (fun q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) //
        q.asIdeal.LiesOver Q.asIdeal} => q.1.adicCompletion ↥L)
    (φ.comp ψ.symm.toAlgHom) hsurj
  refine ⟨↥L, inferInstance, inferInstance, inferInstance, q.1, q.2, ?_⟩
  exact ⟨e₂.trans e_q.symm⟩

/-! ## Base-change transport along a ring isomorphism -/

section Transport
variable {M M' E : Type*} [Field M] [Field M'] [Field E] [Algebra M E] [Algebra M' E]

/-- `Module.finrank` is invariant under changing the base field along a ring isomorphism
(keeping the same total algebra). -/
lemma finrank_eq_of_algebraMap_eq (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    Module.finrank M' E = Module.finrank M E := by
  have hrank : Module.rank M E = Module.rank M' E :=
    Algebra.rank_eq_of_equiv_equiv φ (RingEquiv.refl E)
      (by first | (rw [RingEquiv.toRingHom_refl, RingHom.id_comp]; exact he) | exact he)
  unfold Module.finrank
  rw [hrank]

/-- The Galois groups `E ≃ₐ[M] E` and `E ≃ₐ[M'] E` are canonically isomorphic when the two
`M`- and `M'`-algebra structures are related by a ring isomorphism `φ : M ≃+* M'`. -/
def algEquiv_cast {φ : M ≃+* M'}
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    (E ≃ₐ[M] E) ≃* (E ≃ₐ[M'] E) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => by
    have hx : algebraMap M' E x = algebraMap M E (φ.symm x) := by
      simpa using RingHom.congr_fun he (φ.symm x)
    rw [hx]
    exact σ.commutes (φ.symm x))
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => by
    have hx : algebraMap M E x = algebraMap M' E (φ x) := (RingHom.congr_fun he x).symm
    rw [hx]
    exact σ.commutes (φ x))
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- `FiniteDimensional` transfers across a change of base ring along an isomorphism. -/
lemma finiteDimensional_transport [FiniteDimensional M E] (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) : FiniteDimensional M' E := by
  letI : Algebra M' M := φ.symm.toRingHom.toAlgebra
  have hAM : ∀ x : M', algebraMap M' E x = algebraMap M E (algebraMap M' M x) := by
    intro x
    have hx : (algebraMap M' M) x = φ.symm x := by rw [RingHom.algebraMap_toAlgebra]; rfl
    rw [hx]
    have h := RingHom.congr_fun he (φ.symm x)
    simpa using h
  haveI : IsScalarTower M' M E := IsScalarTower.of_algebraMap_eq hAM
  have hsurj : Function.Surjective (Algebra.linearMap M' M) := by
    intro y
    refine ⟨φ y, ?_⟩
    rw [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    exact φ.symm_apply_apply y
  haveI hfinM : Module.Finite M' M := Module.Finite.of_surjective (Algebra.linearMap M' M) hsurj
  exact Module.Finite.trans M E

/-- `IsGalois` transfers across a change of base ring along an isomorphism. -/
lemma isGalois_transport [FiniteDimensional M E] [IsGalois M E] (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) : IsGalois M' E := by
  haveI : FiniteDimensional M' E := finiteDimensional_transport φ he
  refine IsGalois.of_card_aut_eq_finrank M' E ?_
  rw [← Nat.card_congr (algEquiv_cast he).toEquiv, IsGalois.card_aut_eq_finrank M E,
    finrank_eq_of_algebraMap_eq (E := E) φ he]

/-- Commutativity of the Galois group transfers across a change of base ring along an
isomorphism. -/
lemma commute_transport (φ : M ≃+* M')
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E)
    (hcomm : ∀ a b : E ≃ₐ[M] E, a * b = b * a) :
    ∀ a b : E ≃ₐ[M'] E, a * b = b * a := by
  intro a b
  let u := algEquiv_cast (E := E) he
  calc a * b = u (u.symm a) * u (u.symm b) := by rw [u.apply_symm_apply, u.apply_symm_apply]
    _ = u (u.symm a * u.symm b) := by rw [map_mul]
    _ = u (u.symm b * u.symm a) := by rw [hcomm (u.symm a) (u.symm b)]
    _ = u (u.symm b) * u (u.symm a) := by rw [map_mul]
    _ = b * a := by rw [u.apply_symm_apply, u.apply_symm_apply]

/-- The range of the unit norm is transported by the unit isomorphism induced by `φ`. -/
lemma range_norm_map_eq {φ : M ≃+* M'}
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    (MonoidHom.range (Units.map (Algebra.norm M : E →* M))).map
        (Units.mapEquiv φ.toMulEquiv).toMonoidHom =
      MonoidHom.range (Units.map (Algebra.norm M' : E →* M')) := by
  have hnorm : ∀ x : E, φ (Algebra.norm M x) = Algebra.norm M' x :=
    fun x => Algebra.norm_eq_of_ringEquiv φ (by ext y; exact RingHom.congr_fun he y) x
  ext y; constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, by ext; simp only [Units.coe_map]; exact (hnorm (u : E)).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Units.map (Algebra.norm M) u, ⟨u, rfl⟩, by
      ext; simp only [Units.coe_map]; exact hnorm (u : E)⟩

/-- The quotients of the units by the range of the norm are canonically isomorphic under a
change of base ring. -/
def quotEquiv_norm_of_cast {φ : M ≃+* M'}
    (he : (algebraMap M' E).comp φ.toRingHom = algebraMap M E) :
    (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) ≃*
    (M'ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M' : E →* M'))) :=
  QuotientGroup.congr _ _ (Units.mapEquiv φ.toMulEquiv) (range_norm_map_eq he)

end Transport

/-! ## The main induction -/

/-- **Induction statement.**  For an abelian finite Galois extension `E` of the local field
`Q.adicCompletion K` of local degree `n`, the norm index of the units is at most `n`. -/
theorem main_aux : ∀ n : ℕ, ∀ (K : Type u) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (E : Type*) [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E],
    (∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) →
    Module.finrank (Q.adicCompletion K) E = n →
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ Q E _ _ _ _ hcomm hdeg
    let F := Q.adicCompletion K
    let G := E ≃ₐ[F] E
    haveI : IsMulCommutative G := IsMulCommutative.of_comm hcomm
    by_cases hnt : Nontrivial G
    · obtain ⟨H, hHlt, hHcyc⟩ := exists_maximal_subgroup_quotient_cyclic G
      haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
      let M := IntermediateField.fixedField H
      haveI hMgal : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
      haveI hMfd : FiniteDimensional F M := inferInstance
      haveI hMcyc : IsCyclic (M ≃ₐ[F] M) := (IsGalois.normalAutEquivQuotient H).isCyclic.mp hHcyc
      -- cyclic input for `M / F`
      have hcycCase : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : M →* F))) =
          Nat.card (M ≃ₐ[F] M) :=
        natCard_quotient_units_range_norm_eq_card_of_cyclic (Q := Q) (E := M)
      have hcardM : Nat.card (M ≃ₐ[F] M) = Nat.card (G ⧸ H) :=
        (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
      -- realize `M` over `F`
      have hcommM : ∀ a b : E ≃ₐ[M] E, a * b = b * a := by
        intro a b
        have h := hcomm (AlgEquiv.restrictScalars F a) (AlgEquiv.restrictScalars F b)
        apply AlgEquiv.ext; intro x
        have hx := congr_fun (congrArg (fun g : E ≃ₐ[F] E => (g : E → E)) h) x
        simpa [AlgEquiv.mul_apply] using hx
      obtain ⟨L', hLf, hLn, hLa, q', hq', ⟨φ⟩⟩ := exists_realization (Q := Q) (E := M)
      letI : Algebra (Q.adicCompletion K) (q'.adicCompletion L') :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q' hq')
      -- new base algebra structure on `E`
      letI : Algebra (q'.adicCompletion L') E :=
        ((algebraMap M E).comp φ.symm.toRingHom).toAlgebra
      have hhe : (algebraMap (q'.adicCompletion L') E).comp φ.toRingHom = algebraMap M E := by
        ext x
        show algebraMap (q'.adicCompletion L') E (φ x) = algebraMap M E x
        rw [show algebraMap (q'.adicCompletion L') E =
          (algebraMap M E).comp φ.symm.toRingHom from rfl]
        simp [RingHom.comp_apply]
      haveI : FiniteDimensional (q'.adicCompletion L') E :=
        finiteDimensional_transport φ.toRingEquiv hhe
      haveI : IsGalois (q'.adicCompletion L') E := isGalois_transport φ.toRingEquiv hhe
      have hcomm' : ∀ a b : E ≃ₐ[q'.adicCompletion L'] E, a * b = b * a :=
        commute_transport φ.toRingEquiv hhe hcommM
      have hfinrank' : Module.finrank (q'.adicCompletion L') E = Nat.card H := by
        rw [finrank_eq_of_algebraMap_eq φ.toRingEquiv hhe,
          IntermediateField.finrank_fixedField_eq_card H]
      -- Lagrange / strict decrease
      have hcardG : Nat.card G = n := by
        rw [IsGalois.card_aut_eq_finrank F E, hdeg]
      haveI : Nontrivial (G ⧸ H) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton (G ⧸ H) := hsub
        have hGal : H = ⊤ := by
          rw [eq_top_iff]
          intro x
          have h1 : (QuotientGroup.mk x : G ⧸ H) = 1 := Subsingleton.elim _ _
          rw [QuotientGroup.eq_one_iff] at h1
          simpa using h1
        exact absurd hGal (ne_of_lt hHlt)
      have h1lt : 1 < Nat.card (G ⧸ H) := by
        haveI : Finite (G ⧸ H) := Quotient.finite _
        haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hHlt_n : Nat.card H < n := by
        rw [← hcardG, ← Subgroup.card_mul_index H, Subgroup.index_eq_card]
        calc Nat.card H = Nat.card H * 1 := (Nat.mul_one _).symm
          _ < Nat.card H * Nat.card (G ⧸ H) := Nat.mul_lt_mul_of_pos_left h1lt Nat.card_pos
      -- IH for the extension `E / M`
      have hIH := ih (Nat.card H) hHlt_n L' q' E hcomm' hfinrank'
      have htransport : Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) =
          Nat.card ((q'.adicCompletion L')ˣ ⧸ MonoidHom.range
            (Units.map (Algebra.norm (q'.adicCompletion L') : E →* q'.adicCompletion L'))) :=
        Nat.card_congr (quotEquiv_norm_of_cast (φ := φ.toRingEquiv) hhe).toEquiv
      haveI hfin' : Finite ((q'.adicCompletion L')ˣ ⧸ MonoidHom.range
          (Units.map (Algebra.norm (q'.adicCompletion L') : E →* q'.adicCompletion L'))) :=
        finite_quotient_units_range_norm_of_isGalois q'
      haveI hfinM : Finite (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) := by
        have hne : Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) ≠ 0 := by
          rw [htransport]
          exact Nat.card_ne_zero.mpr ⟨inferInstance, hfin'⟩
        exact (Nat.card_ne_zero.mp hne).2
      -- group inequality
      have hcomp : (Units.map (Algebra.norm F : M →* F)).comp
            (Units.map (Algebra.norm M : E →* M)) =
          Units.map (Algebra.norm F : E →* F) := by
        ext u
        simp only [MonoidHom.comp_apply, Units.coe_map]
        exact congrArg (fun z : F => z.toCompletion)
          (Algebra.norm_norm (R := F) (S := M) (A := E) (a := (u : E)))
      have hgrp := natCard_quotient_range_comp_le
        (Units.map (Algebra.norm F : M →* F)) (Units.map (Algebra.norm M : E →* M))
      rw [hcomp] at hgrp
      calc Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F)))
          ≤ Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : M →* F))) *
              Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) := hgrp
        _ = Nat.card (M ≃ₐ[F] M) * Nat.card (Mˣ ⧸
              MonoidHom.range (Units.map (Algebra.norm M : E →* M))) := by rw [hcycCase]
        _ = Nat.card (G ⧸ H) * Nat.card (Mˣ ⧸
              MonoidHom.range (Units.map (Algebra.norm M : E →* M))) := by rw [hcardM]
        _ ≤ Nat.card (G ⧸ H) * Nat.card H :=
              Nat.mul_le_mul_left _ (le_trans (le_of_eq htransport) hIH)
        _ = Nat.card G := by
              rw [← Subgroup.card_mul_index H, Subgroup.index_eq_card, Nat.mul_comm]
        _ = n := by rw [IsGalois.card_aut_eq_finrank F E, hdeg]
    · -- trivial Galois group
      haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
      have hcardG : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      have hfin1 : Module.finrank F E = 1 := by
        rw [← IsGalois.card_aut_eq_finrank F E, hcardG]
      have hrange : MonoidHom.range (Units.map (Algebra.norm F : E →* F)) = ⊤ := by
        rw [eq_top_iff]
        rintro y -
        refine ⟨Units.map (algebraMap F E).toMonoidHom y, Units.ext ?_⟩
        show Algebra.norm F ((algebraMap F E) (y : F)) = (y : F)
        rw [Algebra.norm_algebraMap, hfin1, pow_one]
      have hq : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) = 1 := by
        rw [hrange, ← Subgroup.index_eq_card (⊤ : Subgroup Fˣ), Subgroup.index_top]
      rw [hq, ← hdeg, hfin1]

/-! ## The requested lemma -/

theorem natCard_quotient_units_range_norm_le_finrank_of_abelian_local
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) ≤
      Module.finrank (Q.adicCompletion K) E :=
  main_aux (Module.finrank (Q.adicCompletion K) E) K Q E hcomm rfl

end Commons.NumberTheory.NumberField.Completion
