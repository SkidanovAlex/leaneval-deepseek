import Mathlib
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Norm.norm_map_algEquiv
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close
import Submission.Commons.Analysis.Polynomial.supNorm_lt_iff
import Submission.Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Polynomial
open scoped TensorProduct
open scoped NumberField WithZero
open scoped Valued
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## Auxiliary lemmas -/

/-- A finite-dimensional commutative algebra over a field which is an integral domain is a
field: multiplication by a nonzero element is an injective linear map, hence surjective. -/
private lemma isField_of_isDomain_of_finiteDimensional {F R : Type*} [Field F] [CommRing R]
    [Algebra F R] [IsDomain R] [FiniteDimensional F R] : IsField R := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  have hinj : Function.Injective (LinearMap.mulLeft F a) := by
    intro x y hxy
    have h : a * (x - y) = 0 := by
      rw [mul_sub, show a * x = a * y from hxy, sub_self]
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 ha
    · exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective (LinearMap.mulLeft F a) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨b, hb⟩ := hsurj 1
  exact ⟨b, hb⟩

/-- Approximation of the coefficients of a polynomial over `F` by coefficients in a dense
subfield `K`: for every `ε > 0` there is `g : K[X]` whose image in `F[X]` has the same degree
bound as `f` and is `ε`-close to `f` in the sup norm. -/
lemma exists_map_supNorm_lt {K F : Type*} [Field K] [NontriviallyNormedField F] [Algebra K F]
    (hd : ∀ c : F, ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖c - algebraMap K F k‖ < ε)
    (f : F[X]) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : K[X], (f - g.map (algebraMap K F)).supNorm < ε ∧
      (g.map (algebraMap K F)).natDegree ≤ f.natDegree := by
  classical
  choose k hk using fun i => hd (f.coeff i) ε hε
  refine ⟨∑ j ∈ f.support, C (k j) * X ^ j, ?_, ?_⟩
  · rw [Commons.Analysis.Polynomial.supNorm_lt_iff]
    intro i
    have hgcoeff : (∑ j ∈ f.support, C (k j) * X ^ j : K[X]).coeff i =
        if i ∈ f.support then k i else 0 := by
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      by_cases hi : i ∈ f.support
      · rw [if_pos hi, Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          simp [Ne.symm hji]
        · intro hi'; exact absurd hi hi'
      · rw [if_neg hi, Finset.sum_eq_zero]
        intro j hj
        rw [if_neg (show ¬ (i = j) from fun h => hi (h ▸ hj))]
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hgcoeff]
    by_cases hi : i ∈ f.support
    · rw [if_pos hi]; exact hk i
    · rw [if_neg hi, map_zero]
      simp [Polynomial.notMem_support_iff.mp hi, hε]
  · refine le_trans (Polynomial.natDegree_map_le (f := algebraMap K F) (p := _)) ?_
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro j hj
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (k j) j)
      (Polynomial.le_natDegree_of_mem_supp _ hj)

/-- The root set of a polynomial does not change when the coefficients are extended to a larger
field. -/
lemma map_rootSet_eq {K F Fbar : Type*} [Field K] [Field F] [Field Fbar] [Algebra K F]
    [Algebra K Fbar] [Algebra F Fbar] [IsScalarTower K F Fbar] (g : K[X]) :
    (g.map (algebraMap K F)).rootSet Fbar = g.rootSet Fbar := by
  ext x
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_ne_zero_iff (algebraMap K Fbar).injective]
      intro hg0
      exact h1 (by rw [hg0, Polynomial.map_zero, Polynomial.map_zero])
    · rwa [Polynomial.aeval_map_algebraMap F x g] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_ne_zero_iff (algebraMap F Fbar).injective,
        Polynomial.map_ne_zero_iff (algebraMap K F).injective]
      intro hg0
      exact h1 (by rw [hg0, Polynomial.map_zero])
    · rwa [Polynomial.aeval_map_algebraMap F x g]

/-- A finite Galois extension is the splitting field of the minimal polynomial of a primitive
element: it is isomorphic to the intermediate field generated by the roots of that polynomial
in the algebraic closure. -/
lemma exists_algEquiv_adjoin_rootSet_of_isGalois {F : Type*} [Field F] {E : Type*} [Field E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    ∃ f : F[X], f ≠ 0 ∧ f.Separable ∧
      Nonempty (E ≃ₐ[F] ↥(IntermediateField.adjoin F (f.rootSet (AlgebraicClosure F)))) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  refine ⟨minpoly F α, minpoly.ne_zero (Algebra.IsIntegral.isIntegral α), ?_, ?_⟩
  · exact Algebra.IsSeparable.isSeparable F α
  · have hsplit : Polynomial.IsSplittingField F E (minpoly F α) := by
      rw [isSplittingField_iff_intermediateField]
      refine ⟨?_, ?_⟩
      · exact (IsGalois.to_normal (F := F) (E := E)).splits α
      · rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
        exact IntermediateField.subset_adjoin F _
          ((minpoly.monic (Algebra.IsIntegral.isIntegral α)).mem_rootSet.mpr (minpoly.aeval _ _))
    haveI : IsAlgClosed (AlgebraicClosure F) := inferInstance
    set j : E →ₐ[F] AlgebraicClosure F :=
      IsAlgClosed.lift (R := F) (S := E) (M := AlgebraicClosure F) with hj
    have hrange : Algebra.adjoin F ((minpoly F α).rootSet (AlgebraicClosure F)) = j.range :=
      IsSplittingField.adjoin_rootSet_eq_range E (minpoly F α) j
    have hfieldRange : j.fieldRange =
        IntermediateField.adjoin F ((minpoly F α).rootSet (AlgebraicClosure F)) := by
      apply IntermediateField.toSubalgebra_injective
      rw [AlgHom.fieldRange_toSubalgebra, ← hrange,
        IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => isAlgebraic_of_mem_rootSet hx)]
    exact ⟨j.equivFieldRange.trans (IntermediateField.equivOfEq hfieldRange)⟩

/-- The tensor product surjectivity lemma: the number field generated by the roots of `g` over
`K` maps onto the splitting field of `g` over `F`, via the natural `F`-algebra map
`L ⊗[K] F → E'`. -/
theorem surjective_tensorProduct_adjoin_rootSet
    {K F : Type*} [Field K] [Field F] [Algebra K F] (g : K[X]) :
    let Fbar := AlgebraicClosure F
    let S : Set Fbar := g.rootSet Fbar
    let L : IntermediateField K Fbar := IntermediateField.adjoin K S
    let E' : IntermediateField F Fbar := IntermediateField.adjoin F S
    letI : Algebra F (TensorProduct K L F) := Algebra.TensorProduct.rightAlgebra
    ∃ φ : TensorProduct K L F →ₐ[F] ↥E', Function.Surjective φ := by
  intro Fbar S L E'
  letI : Algebra F (TensorProduct K L F) := Algebra.TensorProduct.rightAlgebra
  have hLE : (L : Set Fbar) ⊆ (E' : Set Fbar) := by
    have h : L ≤ IntermediateField.restrictScalars K E' := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact IntermediateField.subset_adjoin F S hx
    intro x hx
    exact h hx
  let incl : L →ₐ[K] ↥E' :=
    { toFun := fun l => ⟨l.1, hLE l.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl
      map_zero' := rfl
      map_add' := fun a b => rfl
      commutes' := fun c => Subtype.ext (by
        rw [IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply K F ↥E',
          IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply K F Fbar]) }
  let ψ : TensorProduct K F L →ₐ[F] ↥E' :=
    Algebra.TensorProduct.lift (Algebra.ofId F ↥E') incl (fun x y => Commute.all _ _)
  have hψ_tmul : ∀ (f : F) (l : L), ψ (f ⊗ₜ[K] l) = algebraMap F ↥E' f * incl l := by
    intro f l
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  let flip : TensorProduct K L F ≃ₐ[F] TensorProduct K F L :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K L F).toRingEquiv) (by
      intro c
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      change (Algebra.TensorProduct.comm K L F) (1 ⊗ₜ[K] c) = _
      rw [Algebra.TensorProduct.comm_tmul, Algebra.algebraMap_eq_smul_one,
        Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  let φ : TensorProduct K L F →ₐ[F] ↥E' := ψ.comp flip.toAlgHom
  have hflip : ∀ (l : L) (f : F), flip (l ⊗ₜ[K] f) = f ⊗ₜ[K] l := by
    intro l f
    change (Algebra.TensorProduct.comm K L F) (l ⊗ₜ[K] f) = f ⊗ₜ[K] l
    rw [Algebra.TensorProduct.comm_tmul]
  have hφ_tmul : ∀ (l : L) (f : F), φ (l ⊗ₜ[K] f) = incl l * algebraMap F ↥E' f := by
    intro l f
    change ψ (flip (l ⊗ₜ[K] f)) = incl l * algebraMap F ↥E' f
    rw [hflip, hψ_tmul, mul_comm]
  refine ⟨φ, ?_⟩
  have hrange : ∀ x : Fbar, ∀ hx : x ∈ (E' : Set Fbar), ∃ y : TensorProduct K L F,
      φ y = (⟨x, hx⟩ : ↥E') := by
    intro x hx
    revert hx
    refine IntermediateField.adjoin_induction (F := F) (s := S)
      (p := fun x hx => ∃ y : TensorProduct K L F, φ y = (⟨x, hx⟩ : ↥E')) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hxL : x ∈ L := IntermediateField.subset_adjoin K S hx
      refine ⟨(⟨x, hxL⟩ : L) ⊗ₜ[K] (1 : F), ?_⟩
      rw [hφ_tmul, map_one, mul_one]
      exact Subtype.ext rfl
    · intro c
      refine ⟨(1 : L) ⊗ₜ[K] c, ?_⟩
      rw [hφ_tmul, map_one, one_mul]
      exact Subtype.ext (by simp)
    · intro a b ha hb ⟨ya, hya⟩ ⟨yb, hyb⟩
      exact ⟨ya + yb, by rw [map_add, hya, hyb]; exact Subtype.ext (by simp)⟩
    · intro a ha ⟨y, hy⟩
      by_cases h0 : a = 0
      · refine ⟨0, ?_⟩
        rw [map_zero]
        apply Subtype.ext
        simp only [ZeroMemClass.coe_zero]
        rw [h0, inv_zero]
      · haveI : FiniteDimensional F ↥E' := by
          apply IntermediateField.finiteDimensional_adjoin
          intro x hx
          exact IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
        haveI hfield : IsField ↥(φ.range) :=
          isField_of_isDomain_of_finiteDimensional (F := F)
        have hmem : (⟨a, ha⟩ : ↥E') ∈ φ.range := ⟨y, hy⟩
        let Aa : ↥(φ.range) := ⟨⟨a, ha⟩, hmem⟩
        have hne : Aa ≠ 0 := by
          intro hc
          refine h0 (Subtype.ext_iff.mp (Subtype.ext_iff.mp hc))
        obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
        obtain ⟨y', hy'⟩ := b.2
        have hy'' : φ y' = (b : ↥E') := hy'
        refine ⟨y', ?_⟩
        rw [hy'']
        have hb' : (⟨a, ha⟩ : ↥E') * (b : ↥E') = 1 := by
          have := congrArg (fun z : ↥(φ.range) => (z : ↥E')) hb
          simpa using this
        have hb'' : (b : ↥E') = (⟨a, ha⟩ : ↥E')⁻¹ := eq_inv_of_mul_eq_one_right hb'
        rw [hb'']
        exact Subtype.ext rfl
    · intro a b ha hb ⟨ya, hya⟩ ⟨yb, hyb⟩
      exact ⟨ya * yb, by rw [map_mul, hya, hyb]; exact Subtype.ext (by simp)⟩
  intro y
  obtain ⟨x, hx⟩ := hrange (y : Fbar) y.2
  exact ⟨x, hx⟩


/-- The embedding of `K` in its `Q`-adic completion is dense, in the quantitative form needed for
the approximation of coefficients. -/
lemma exists_dist_algebraMap_lt {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : Q.adicCompletion K) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : K, ‖c - algebraMap K (Q.adicCompletion K) k‖ < ε := by
  have hd : DenseRange (algebraMap K (Q.adicCompletion K)) := Q.denseRange_algebraMap K
  have hmem : c ∈ closure (Set.range (algebraMap K (Q.adicCompletion K))) := hd c
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ := hmem ε hε
  exact ⟨k, by simpa [dist_eq_norm] using hy⟩


/-- Conjugation by an `F`-algebra equivalence is a group isomorphism between the automorphism
groups. -/
def algEquivAutMulEquiv {F E B : Type*} [Field F] [Field E] [Field B] [Algebra F E] [Algebra F B]
    (e : E ≃ₐ[F] B) : (E ≃ₐ[F] E) ≃* (B ≃ₐ[F] B) where
  toFun σ := e.symm.trans (σ.trans e)
  invFun τ := e.trans (τ.trans e.symm)
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp [AlgEquiv.mul_apply]

/-- The range of the norm does not change under an `F`-algebra equivalence, so the cardinality of
the norm quotient of the units is an invariant of the isomorphism class of `F`-algebras. -/
lemma natCard_quotient_units_range_norm_eq_of_algEquiv {F E B : Type*} [Field F] [Field E]
    [Field B] [Algebra F E] [Algebra F B] [FiniteDimensional F E] [FiniteDimensional F B]
    (e : E ≃ₐ[F] B) :
    Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) =
      Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : B →* F))) := by
  have hrange : MonoidHom.range (Units.map (Algebra.norm F : E →* F)) =
      MonoidHom.range (Units.map (Algebra.norm F : B →* F)) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Units.map e u, ?_⟩
      ext
      simp [Units.coe_map, Commons.FieldTheory.Norm.norm_map_algEquiv e]
    · rintro ⟨u, rfl⟩
      refine ⟨Units.map e.symm u, ?_⟩
      ext
      simp [Units.coe_map, Commons.FieldTheory.Norm.norm_map_algEquiv e.symm]
  rw [hrange]


/-- **The cyclic case of the local norm index theorem.**

For a finite cyclic Galois extension `E` of the local field `F = Q.adicCompletion K` (the
completion of a number field `K` at a finite place `Q`), the quotient of the units of `F` by the
norms from `E` has the cardinality of the Galois group.

The proof reduces the statement to the analogous statement for the completion of a finite Galois
extension `L / K` of number fields:

* `E` is the splitting field of the minimal polynomial `f` of a primitive element
  (`exists_algEquiv_adjoin_rootSet_of_isGalois`);
* by Krasner's lemma in the form `Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close`, a small
  perturbation `g ∈ K[X]` of `f` has the same splitting field over `F`;
* the number field `L = K(g.rootSet)` generated by the roots of `g` satisfies `L ⊗[K] F ≅ ∏ L_q`
  (`exists_algEquiv_tensor_adicCompletion_prod`), and the natural map `L ⊗[K] F → E` is surjective
  (`surjective_tensorProduct_adjoin_rootSet`), so `E ≅ L_q` for some place `q` of `L` over `Q`
  (`Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi`);
* the statement for `L_q` is the shared-commons theorem
  `natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic`. -/
theorem natCard_quotient_units_range_norm_eq_card_of_cyclic
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    [IsCyclic (E ≃ₐ[Q.adicCompletion K] E)] :
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
  -- ## Step 1: `E` is the splitting field of the minimal polynomial of a primitive element
  obtain ⟨f, hf0, hfsep, ⟨e₁⟩⟩ :=
    exists_algEquiv_adjoin_rootSet_of_isGalois (F := Q.adicCompletion K) (E := E)
  -- ## Step 2: Krasner's lemma: small perturbations have the same splitting field
  obtain ⟨ε, hεpos, hε⟩ :=
    Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close (K := Q.adicCompletion K) f hf0 hfsep
  -- ## Step 3: approximate the coefficients of `f` by coefficients in `K`
  obtain ⟨g, hgsup, hgdeg⟩ := exists_map_supNorm_lt (K := K) (F := Q.adicCompletion K)
    (fun c ε hε => exists_dist_algebraMap_lt Q c ε hε) f ε hεpos
  -- ## Step 4: the number field generated by the roots of `g` and the local splitting field
  set L : IntermediateField K (AlgebraicClosure (Q.adicCompletion K)) :=
    IntermediateField.adjoin K (g.rootSet (AlgebraicClosure (Q.adicCompletion K))) with hLdef
  set E' : IntermediateField (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)) :=
    IntermediateField.adjoin (Q.adicCompletion K)
      (g.rootSet (AlgebraicClosure (Q.adicCompletion K))) with hE'def
  have heq : IntermediateField.adjoin (Q.adicCompletion K)
      (f.rootSet (AlgebraicClosure (Q.adicCompletion K))) = E' := by
    rw [hE'def, ← map_rootSet_eq (K := K) (F := Q.adicCompletion K)
      (Fbar := AlgebraicClosure (Q.adicCompletion K)) g]
    exact hε (g.map (algebraMap K (Q.adicCompletion K))) hgdeg hgsup
  have e₂ : E ≃ₐ[Q.adicCompletion K] ↥E' := e₁.trans (IntermediateField.equivOfEq heq)
  -- ## Step 5: `L` is a number field, finite Galois over `K`
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
  -- ## Step 6: the natural map `L ⊗[K] F → E'` is surjective
  obtain ⟨φ, hφ⟩ := surjective_tensorProduct_adjoin_rootSet (K := K)
    (F := Q.adicCompletion K) g
  -- ## Step 7: the tensor product decomposes as the product of the completions `L_q`
  letI : Algebra (Q.adicCompletion K) (TensorProduct K ↥L (Q.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI hfin : Fintype {q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥L) // q.asIdeal.LiesOver Q.asIdeal} :=
    Fintype.ofEquiv (Q.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)) (primesOverEquiv Q).symm
  letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) //
      q.asIdeal.LiesOver Q.asIdeal},
      Algebra (Q.adicCompletion K) (q.1.adicCompletion ↥L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  obtain ⟨ψ⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
      K ↥L Q
  -- ## Step 8: a surjection from a product of fields onto `E'` factors through a projection
  have hsurj : Function.Surjective (φ.comp ψ.symm.toAlgHom) := fun y =>
    let ⟨x, hx⟩ := hφ y
    ⟨ψ x, by rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, hx]⟩
  obtain ⟨q, ⟨e_q⟩⟩ := Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
    (fun q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) //
        q.asIdeal.LiesOver Q.asIdeal} => q.1.adicCompletion ↥L)
    (φ.comp ψ.symm.toAlgHom) hsurj
  -- ## Step 9: transfer the statement to the completion of `L`
  letI : Algebra (Q.adicCompletion K) (q.1.adicCompletion ↥L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  haveI hfd' : FiniteDimensional (Q.adicCompletion K) (q.1.adicCompletion ↥L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q.1 q.2
  have e₃ : E ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L := e₂.trans e_q.symm
  haveI hcyc : IsCyclic (q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L) :=
    (algEquivAutMulEquiv e₃).isCyclic.mp inferInstance
  have hkey :=
    natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic
      (K := K) (L := ↥L) Q q.1 q.2 hcyc
  -- ## Step 10: put the pieces together
  have hA : Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) =
      Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.1.adicCompletion ↥L →* Q.adicCompletion K))) :=
    natCard_quotient_units_range_norm_eq_of_algEquiv e₃
  have hN : Nat.card (Abelianization
        (q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L)) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
    have hcomm : ∀ a b : q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L,
        a * b = b * a := by
      obtain ⟨σ, hσ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
      intro a b
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (show a ∈ Subgroup.zpowers σ by rw [hσ]; trivial)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (show b ∈ Subgroup.zpowers σ by rw [hσ]; trivial)
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self σ m n).eq
    haveI : IsMulCommutative (q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L) :=
      IsMulCommutative.of_comm hcomm
    have hbot : commutator (q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L) = ⊥ :=
      commutator_eq_bot _
    change Nat.card ((q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L) ⧸
      commutator (q.1.adicCompletion ↥L ≃ₐ[Q.adicCompletion K] q.1.adicCompletion ↥L)) =
        Nat.card (E ≃ₐ[Q.adicCompletion K] E)
    rw [hbot, Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
    exact Nat.card_congr (algEquivAutMulEquiv e₃).symm.toEquiv
  rw [hA, hkey, hN]

end Commons.NumberTheory.NumberField.Completion
