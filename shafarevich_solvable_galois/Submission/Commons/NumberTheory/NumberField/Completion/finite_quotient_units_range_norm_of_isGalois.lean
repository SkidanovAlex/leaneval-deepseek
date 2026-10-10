import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
import Submission.Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.FieldTheory.Norm.norm_map_algEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.exists_polynomial_map_close_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero Valued TensorProduct
open IsDedekindDomain.HeightOneSpectrum Polynomial IntermediateField

namespace Commons.NumberTheory.NumberField.Completion

noncomputable section
attribute [local instance] Algebra.TensorProduct.rightAlgebra


/-- The range of the norm on units is unchanged by an `F`-algebra isomorphism. -/
lemma range_norm_units_eq_of_algEquiv {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] [Module.Finite F E] [Module.Finite F E']
    (σ : E ≃ₐ[F] E') :
    MonoidHom.range (Units.map (Algebra.norm F : E →* F)) =
      MonoidHom.range (Units.map (Algebra.norm F : E' →* F)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map σ.toRingEquiv.toMonoidHom u, ?_⟩
    apply Units.ext
    simp only [Units.coe_map]
    simpa using (Commons.FieldTheory.Norm.norm_map_algEquiv σ (u : E))
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map σ.symm.toRingEquiv.toMonoidHom u, ?_⟩
    apply Units.ext
    simp only [Units.coe_map]
    simpa using (Commons.FieldTheory.Norm.norm_map_algEquiv σ.symm (u : E'))

/-- Finiteness of the quotient by the norm group transfers across an `F`-algebra isomorphism. -/
lemma finite_quotient_units_range_norm_of_algEquiv {F E E' : Type*} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] [Module.Finite F E] [Module.Finite F E']
    (σ : E ≃ₐ[F] E') :
    Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) →
    Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E' →* F))) := by
  intro h
  rwa [range_norm_units_eq_of_algEquiv σ] at h


section

variable {K : Type*} [Field K] [NumberField K]
  (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

local notation "F" => (Q.adicCompletion K)

private theorem finite_quotient_units_range_norm_of_isGalois_aux
    {E : Type*} [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) := by
  classical
  haveI hchar : CharZero F := Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  -- primitive element and its minimal polynomial
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element F E
  have hfsep : (minpoly F β).Separable := Algebra.IsSeparable.isSeparable F β
  have hfne : minpoly F β ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral β)
  have hfdeg : (minpoly F β).natDegree = Module.finrank F E :=
    (Field.primitive_element_iff_minpoly_natDegree_eq F β).mp hβ
  -- `E` is the splitting field of `minpoly F β`
  have eEA : E ≃ₐ[F]
      ↥(IntermediateField.adjoin F ((minpoly F β).rootSet (AlgebraicClosure F))) := by
    have hroot : β ∈ (minpoly F β).rootSet E :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral β)).mem_rootSet.mpr (minpoly.aeval F β)
    have hsplitE : (minpoly F β).IsSplittingField F E := by
      rw [isSplittingField_iff_intermediateField]
      refine ⟨Normal.splits' β, ?_⟩
      rw [eq_top_iff, ← hβ, adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact subset_adjoin F _ hroot
    have hsplitA : (minpoly F β).IsSplittingField F
        ↥(IntermediateField.adjoin F ((minpoly F β).rootSet (AlgebraicClosure F))) :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    exact (Polynomial.IsSplittingField.algEquiv E (minpoly F β)).trans
      (Polynomial.IsSplittingField.algEquiv
        ↥(IntermediateField.adjoin F ((minpoly F β).rootSet (AlgebraicClosure F)))
        (minpoly F β)).symm
  -- perturbation threshold
  obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
    Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close (minpoly F β) hfne hfsep
  have hεpos : 0 < min ε₁ (1 / 2 : ℝ) := lt_min hε₁pos (by norm_num)
  obtain ⟨g, hgdeg, hgclose⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_polynomial_map_close_adicCompletion Q
      (minpoly F β) (minpoly F β).natDegree le_rfl hεpos
  have hgmapdeg : (g.map (algebraMap K F)).natDegree ≤ (minpoly F β).natDegree :=
    le_trans Polynomial.natDegree_map_le hgdeg
  have hAB : IntermediateField.adjoin F ((minpoly F β).rootSet (AlgebraicClosure F)) =
      IntermediateField.adjoin F ((g.map (algebraMap K F)).rootSet (AlgebraicClosure F)) :=
    hε₁ (g.map (algebraMap K F)) hgmapdeg (lt_of_lt_of_le hgclose (min_le_left _ _))
  -- the two root sets agree
  have hrootset : (g.map (algebraMap K F)).rootSet (AlgebraicClosure F) =
      g.rootSet (AlgebraicClosure F) := by
    ext x
    rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K F (AlgebraicClosure F)] at h1
      · rwa [Polynomial.aeval_map_algebraMap F x g] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K F (AlgebraicClosure F)]
      · rw [Polynomial.aeval_map_algebraMap F x g]; exact h2
  -- the number field `L` and the local field `B`
  let S : Set (AlgebraicClosure F) := g.rootSet (AlgebraicClosure F)
  let Lint : IntermediateField K (AlgebraicClosure F) := IntermediateField.adjoin K S
  let Bint : IntermediateField F (AlgebraicClosure F) := IntermediateField.adjoin F S
  have hBint_eq : Bint = IntermediateField.adjoin F
      ((g.map (algebraMap K F)).rootSet (AlgebraicClosure F)) := by
    unfold Bint S
    rw [hrootset]
  have eEB : E ≃ₐ[F] ↥Bint := by
    rw [hBint_eq]
    exact eEA.trans (IntermediateField.equivOfEq hAB)
  haveI hfinL : FiniteDimensional K ↥Lint := by
    refine IntermediateField.finiteDimensional_adjoin (fun x hx => ?_)
    exact IsAlgebraic.isIntegral (isAlgebraic_of_mem_rootSet hx)
  haveI hnumL : NumberField ↥Lint :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField Lint
  haveI hgalL : IsGalois K ↥Lint := by
    haveI hsplit : g.IsSplittingField K ↥Lint :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    haveI hnorm : Normal K ↥Lint := Normal.of_isSplittingField g
    exact Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hfinB : FiniteDimensional F ↥Bint := by
    refine IntermediateField.finiteDimensional_adjoin (fun x hx => ?_)
    exact IsAlgebraic.isIntegral (isAlgebraic_of_mem_rootSet
      (show x ∈ (g.map (algebraMap K F)).rootSet (AlgebraicClosure F) from hrootset.symm ▸ hx))

  -- `Lint` is generated by `S`
  have hLint_eq : Lint = IntermediateField.adjoin K S := rfl
  -- `Lint` viewed inside `Bint`
  have hLsubB : (Lint : Set (AlgebraicClosure F)) ⊆ (Bint : Set (AlgebraicClosure F)) := by
    have h : Lint ≤ IntermediateField.restrictScalars K Bint := by
      rw [hLint_eq, IntermediateField.adjoin_le_iff]
      intro x hx
      exact (IntermediateField.mem_restrictScalars K).mpr (subset_adjoin F S hx)
    intro x hx
    exact (IntermediateField.mem_restrictScalars K).mp (h hx)
  -- the multiplication map `L ⊗[K] F →ₐ[F] C`
  let mulMap : (↥Lint) ⊗[K] F →ₐ[F] (AlgebraicClosure F) :=
    (Algebra.TensorProduct.lift (Algebra.ofId F (AlgebraicClosure F))
        (IntermediateField.val Lint)
        (fun x y => mul_comm ((Algebra.ofId F (AlgebraicClosure F)) x)
          ((IntermediateField.val Lint) y))).comp
      (Algebra.TensorProduct.commRight K F ↥Lint).symm.toAlgHom
  have hmulMap_tmul : ∀ (l : ↥Lint) (f : F), mulMap (l ⊗ₜ[K] f) =
      (algebraMap F (AlgebraicClosure F) f) * (l : AlgebraicClosure F) := by
    intro l f
    show (Algebra.TensorProduct.lift (Algebra.ofId F (AlgebraicClosure F))
        (IntermediateField.val Lint)
        (fun x y => mul_comm ((Algebra.ofId F (AlgebraicClosure F)) x)
          ((IntermediateField.val Lint) y)))
        ((Algebra.TensorProduct.commRight K F ↥Lint).symm (l ⊗ₜ[K] f)) =
      (algebraMap F (AlgebraicClosure F) f) * (l : AlgebraicClosure F)
    rw [Algebra.TensorProduct.commRight_symm_tmul]
    exact Algebra.TensorProduct.lift_tmul _ _ _ f l
  -- the range of `mulMap` is contained in `Bint`
  have hmem : ∀ z : (↥Lint) ⊗[K] F, mulMap z ∈ Bint.toSubalgebra := by
    intro z
    refine TensorProduct.induction_on (motive := fun z => mulMap z ∈ Bint.toSubalgebra) z ?_ ?_ ?_
    · simp
    · intro l f
      rw [hmulMap_tmul]
      exact mul_mem (IntermediateField.algebraMap_mem Bint f) (hLsubB l.2)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  have hrange_le : mulMap.range ≤ Bint.toSubalgebra := by
    intro y hy
    obtain ⟨z, rfl⟩ := (AlgHom.mem_range mulMap).mp hy
    exact hmem z
  -- conversely, `Bint ⊆ mulMap.range`, using that the range is a finite-dimensional
  -- subalgebra of a field, hence a field
  have hle_range : Bint.toSubalgebra ≤ mulMap.range := by
    let T : IntermediateField F (AlgebraicClosure F) :=
      mulMap.range.toIntermediateField (fun x hx =>
        Subalgebra.inv_mem_of_algebraic mulMap.range (x := ⟨x, hx⟩)
          (Algebra.IsAlgebraic.isAlgebraic x))
    have hcarrier : T.toSubalgebra = mulMap.range := toSubalgebra_toIntermediateField _ _
    have hBT : Bint ≤ T := by
      rw [show Bint = IntermediateField.adjoin F S from rfl, IntermediateField.adjoin_le_iff]
      intro x hx
      have hxL : x ∈ (Lint : Set (AlgebraicClosure F)) := subset_adjoin K S hx
      have hmem2 : mulMap ((⟨x, hxL⟩ : ↥Lint) ⊗ₜ[K] (1 : F)) = x := by
        rw [hmulMap_tmul, map_one, one_mul]
      have : x ∈ mulMap.range := ⟨_, hmem2⟩
      rw [← hcarrier] at this
      exact this
    intro x hx
    have hxT : x ∈ T := hBT ((IntermediateField.mem_toSubalgebra Bint x).mp hx)
    have : x ∈ T.toSubalgebra := (IntermediateField.mem_toSubalgebra T x).mpr hxT
    rwa [hcarrier] at this
  have hrange_eq : mulMap.range = Bint.toSubalgebra := le_antisymm hrange_le hle_range
  -- the resulting map `L ⊗ F ↠ B`
  let mulB : (↥Lint) ⊗[K] F →ₐ[F] ↥Bint := mulMap.codRestrict Bint.toSubalgebra hmem
  have hmulB_surj : Function.Surjective mulB := by
    intro y
    have hy : (y : AlgebraicClosure F) ∈ mulMap.range := by
      rw [hrange_eq]
      exact y.2
    obtain ⟨z, hz⟩ := (AlgHom.mem_range mulMap).mp hy
    exact ⟨z, Subtype.ext hz⟩
  -- the CRT decomposition of `L ⊗[K] F`
  letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥Lint) //
      q.asIdeal.LiesOver Q.asIdeal},
      Algebra F (q.1.adicCompletion ↥Lint) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  obtain ⟨eProd⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
      K ↥Lint Q
  have hsurjProd : Function.Surjective (mulB.comp eProd.symm.toAlgHom) := by
    intro y
    obtain ⟨z, hz⟩ := hmulB_surj y
    exact ⟨eProd z, by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply]
      exact hz⟩
  haveI hqfin : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥Lint) //
      q.asIdeal.LiesOver Q.asIdeal}, Module.Finite F (q.1.adicCompletion ↥Lint) :=
    fun q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q.1 q.2
  haveI hfint : Fintype {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥Lint) //
      q.asIdeal.LiesOver Q.asIdeal} :=
    Fintype.ofEquiv _ (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q).symm
  -- the factor lemma
  obtain ⟨q₀, ⟨eiso⟩⟩ := Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
    (fun q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥Lint) //
        q.asIdeal.LiesOver Q.asIdeal} => q.1.adicCompletion ↥Lint)
    (mulB.comp eProd.symm.toAlgHom) hsurjProd
  -- the concrete finiteness theorem for `L_{q₀}`
  have hfin_q : Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F :
      q₀.1.adicCompletion ↥Lint →* F))) :=
    Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
      (K := K) (L := ↥Lint) Q q₀.1 q₀.2
  have hfin_B : Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F :
      ↥Bint →* F))) :=
    finite_quotient_units_range_norm_of_algEquiv (σ := eiso) hfin_q
  exact finite_quotient_units_range_norm_of_algEquiv (σ := eEB.symm) hfin_B

end

/-- For a finite Galois extension `E` of the local field `Q.adicCompletion K`, the quotient of
the units of `Q.adicCompletion K` by the image of the norm from `E` is finite. -/
theorem finite_quotient_units_range_norm_of_isGalois
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E] :
    Finite ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) := by
  exact finite_quotient_units_range_norm_of_isGalois_aux Q

end

end Commons.NumberTheory.NumberField.Completion
