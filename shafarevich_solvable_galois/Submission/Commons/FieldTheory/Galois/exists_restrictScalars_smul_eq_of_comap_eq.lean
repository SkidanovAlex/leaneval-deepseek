import Mathlib
import Submission.Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Commons.FieldTheory.Galois

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- Auxiliary: the `comap` form of the action of an algebra automorphism on a valuation subring. -/
private theorem comap_symm_eq_smul {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    (A : ValuationSubring K') (σ : K' ≃ₐ[F] K') :
    A.comap (σ.symm : K' →+* K') = σ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp [AlgEquiv.smul_def]

/-- Auxiliary: the trace on a normal intermediate field of `A.comap σ.symm` is the trace of `A`
transported by `σ|_E`. -/
private theorem comap_symm_comap_eq_aux {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    (A : ValuationSubring K') (σ : K' ≃ₐ[F] K') (E : IntermediateField F K') [Normal F E] :
    (A.comap (σ.symm : K' →+* K')).comap (algebraMap ↥E K') =
      (A.comap (algebraMap ↥E K')).comap
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K') E σ).symm : ↥E →+* ↥E) := by
  have h := Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A σ E
  rw [← comap_symm_eq_smul A σ,
    ← comap_symm_eq_smul (A.comap (algebraMap ↥E K'))
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') E σ)] at h
  exact h

/-- **Transitivity of the Galois action on the places of a Galois extension of a number field
over a fixed place of an *arbitrary intermediate field*.**

Let `K` be a number field, `K'` a Galois extension of `K`, `L` an intermediate field, and
`A`, `B` valuation subrings of `K'` whose traces on `L` agree and are not everything.  Then some
`K`-automorphism of `K'` fixing `L` pointwise carries `A` onto `B`
(equivalently `K' ≃ₐ[L] K'` acts transitively on the places of `K'` above `A|_L`).

Proof: index the compactness argument by the finite normal intermediate fields `E` of `K'/K`.  For
such `E`, the transitivity over the base field `L ⊓ E` (which is a number field since `L ⊓ E ≤ E`)
applied to the traces of `A` and `B` on `K'` provides a `K`-automorphism fixing `L ⊓ E` and
sending `A` to `B`; these finitely-defined nonempty closed conditions are directed, so by
compactness of `K' ≃ₐ[K] K'` the intersection is nonempty.  An element of the intersection sends
`A` to `B` (by `eq_of_comap_eq_forall_finite_normal`) and fixes `L` (every element of `L` lies in
`L ⊓ E` for some finite normal `E`, namely the normal closure of `K⟮x⟯`). -/
theorem exists_restrictScalars_smul_eq_of_comap_eq {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsGalois K K']
    (L : IntermediateField K K') (A B : ValuationSubring K')
    (hC : A.comap (algebraMap ↥L K') ≠ ⊤)
    (hAB : A.comap (algebraMap ↥L K') = B.comap (algebraMap ↥L K')) :
    ∃ σ : K' ≃ₐ[K] K', (∀ x : L, σ x = x) ∧ A.comap (σ.symm : K' →+* K') = B := by
  -- Index set: finite normal intermediate fields of `K'/K`.
  let ι := {E : IntermediateField K K' // FiniteDimensional K E ∧ Normal K E}
  haveI hιne : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let S : ι → Set (K' ≃ₐ[K] K') := fun E =>
    {σ | (A.comap (σ.symm : K' →+* K')).comap (algebraMap ↥E.1 K') =
            B.comap (algebraMap ↥E.1 K') ∧
          (∀ x : ↥(L ⊓ E.1), σ x = x)}
  -- Nonemptiness: at the finite normal level, use the transitivity over the base `L ⊓ E`.
  have hSne : ∀ E : ι, (S E).Nonempty := by
    intro E
    haveI hfin : FiniteDimensional K E.1 := E.2.1
    haveI hnorm : Normal K E.1 := E.2.2
    have halgE : Algebra.IsAlgebraic ↥(L ⊓ E.1) K' := inferInstance
    have hA0ne : A.comap (algebraMap ↥(L ⊓ E.1) K') ≠ ⊤ := by
      intro h0
      have hAtop : A = ⊤ :=
        Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
          A halgE h0
      apply hC
      rw [hAtop]
      ext x
      simp [ValuationSubring.mem_comap]
    have hA0B0 : A.comap (algebraMap ↥(L ⊓ E.1) K') =
        B.comap (algebraMap ↥(L ⊓ E.1) K') := by
      rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (inf_le_left : L ⊓ E.1 ≤ L) A, hAB,
          Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (inf_le_left : L ⊓ E.1 ≤ L) B]
    haveI hnum : NumberField ↥(L ⊓ E.1) := NumberField.of_module_finite K ↥(L ⊓ E.1)
    haveI hgal : IsGalois ↥(L ⊓ E.1) K' := inferInstance
    obtain ⟨σ', hσ'⟩ := Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq
      (F := ↥(L ⊓ E.1)) (K' := K') A B hA0ne hA0B0
    refine ⟨σ'.restrictScalars K, ?_, ?_⟩
    · -- trace condition
      have h1 : A.comap (σ'.symm : K' →+* K') = B := by
        rw [comap_symm_eq_smul A σ']; exact hσ'
      have h2 : ((σ'.restrictScalars K).symm : K' →+* K') = (σ'.symm : K' →+* K') := rfl
      rw [h2, h1]
    · -- fixing condition
      intro x
      exact σ'.commutes x
  -- Directedness.
  have hSdir : Directed (· ⊇ ·) S := by
    intro E₁ E₂
    haveI hfin₁ : FiniteDimensional K E₁.1 := E₁.2.1
    haveI hfin₂ : FiniteDimensional K E₂.1 := E₂.2.1
    haveI hnorm₁ : Normal K E₁.1 := E₁.2.2
    haveI hnorm₂ : Normal K E₂.1 := E₂.2.2
    refine ⟨⟨E₁.1 ⊔ E₂.1, IntermediateField.finiteDimensional_sup E₁.1 E₂.1,
      IntermediateField.normal_sup K K' E₁.1 E₂.1⟩, ?_, ?_⟩
    · intro σ hσ
      simp only [S, Set.mem_ofPred_eq] at hσ ⊢
      constructor
      · rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq
              (le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1) (A.comap (σ.symm : K' →+* K')),
            hσ.1,
            Commons.RingTheory.Valuation.comap_inclusion_comap_eq
              (le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1) B]
      · intro x
        exact hσ.2 ⟨x.1, ⟨x.2.1, (SetLike.le_def.mp (le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1)) x.2.2⟩⟩
    · intro σ hσ
      simp only [S, Set.mem_ofPred_eq] at hσ ⊢
      constructor
      · rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq
              (le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1) (A.comap (σ.symm : K' →+* K')),
            hσ.1,
            Commons.RingTheory.Valuation.comap_inclusion_comap_eq
              (le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1) B]
      · intro x
        exact hσ.2 ⟨x.1, ⟨x.2.1, (SetLike.le_def.mp (le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1)) x.2.2⟩⟩
  -- Closedness.
  have hScl : ∀ E : ι, IsClosed (S E) := by
    intro E
    haveI hfin : FiniteDimensional K E.1 := E.2.1
    haveI hnorm : Normal K E.1 := E.2.2
    have heq : S E = (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') E.1) ⁻¹'
        {g : ↥E.1 ≃ₐ[K] ↥E.1 |
          (A.comap (algebraMap ↥E.1 K')).comap (g.symm : ↥E.1 →+* ↥E.1) =
            B.comap (algebraMap ↥E.1 K') ∧
          (∀ y : ↥E.1, (y : K') ∈ (L ⊓ E.1 : IntermediateField K K') → g y = y)} := by
      ext σ
      simp only [S, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [← comap_symm_comap_eq_aux A σ E.1]; exact h1
        · intro y hy
          refine Subtype.ext ?_
          rw [AlgEquiv.restrictNormalHom_apply]
          exact h2 ⟨y.1, hy⟩
      · intro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [comap_symm_comap_eq_aux A σ E.1]; exact h1
        · intro x
          have hkey : ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') E.1 σ) ⟨x.1, x.2.2⟩ : K')
              = ((⟨x.1, x.2.2⟩ : ↥E.1) : K') :=
            congrArg (fun z : ↥E.1 => (z : K')) (h2 ⟨x.1, x.2.2⟩ x.2)
          rw [AlgEquiv.restrictNormalHom_apply] at hkey
          simpa using hkey
    rw [heq]
    exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous E.1) (isClosed_discrete _)
  -- Compactness.
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hSdir hSne (fun E => (hScl E).isCompact) hScl
  refine ⟨σ, ?_, ?_⟩
  · -- σ fixes `L`
    intro x
    haveI : Algebra.IsAlgebraic K K' := inferInstance
    have hxint : IsIntegral K x.1 :=
      isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic x.1)
    have hadj : FiniteDimensional K ↥(IntermediateField.adjoin K ({x.1} : Set K')) :=
      IntermediateField.finiteDimensional_adjoin (S := ({x.1} : Set K'))
        (by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact hxint)
    let E : IntermediateField K K' :=
      IntermediateField.normalClosure K ↥(IntermediateField.adjoin K ({x.1} : Set K')) K'
    haveI hEfin : FiniteDimensional K E := by
      dsimp only [E]; infer_instance
    haveI hEnorm : Normal K E := by
      dsimp only [E]; infer_instance
    have hxE : x.1 ∈ E := by
      dsimp only [E]
      exact (IntermediateField.le_normalClosure _)
        (IntermediateField.subset_adjoin K _ (Set.mem_singleton x.1))
    have hmem := Set.mem_iInter.mp hσ ⟨E, hEfin, hEnorm⟩
    have := hmem.2 ⟨x.1, ⟨x.2, hxE⟩⟩
    simpa using this
  · -- `A.comap σ.symm = B`
    refine Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
      (K := K) (K' := K') (A := A.comap (σ.symm : K' →+* K')) (B := B) ?_
    intro E hfin hnorm
    exact (Set.mem_iInter.mp hσ ⟨E, hfin, hnorm⟩).1

end Commons.FieldTheory.Galois
