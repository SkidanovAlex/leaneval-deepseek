import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open scoped Pointwise

/-- If the trace of `A` on an intermediate field is everything, then so is its trace on the base
field. -/
private theorem comap_algebraMap_eq_top_of_comap_eq_top {F K' : Type*} [Field F] [Field K']
    [Algebra F K'] (A : ValuationSubring K') {E : IntermediateField F K'}
    (h : A.comap (algebraMap ↥E K') = ⊤) : A.comap (algebraMap F K') = ⊤ := by
  have key : ∀ x : F, algebraMap F K' x ∈ A := by
    intro x
    have h1 : algebraMap F ↥E x ∈ A.comap (algebraMap ↥E K') := by
      rw [h]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap] at h1
    rw [IsScalarTower.algebraMap_apply F ↥E K']
    exact h1
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_comap]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => key x⟩

/-- The image of a valuation subring under an algebra automorphism is the preimage under the
inverse automorphism. -/
private theorem smul_eq_comap_symm_alg {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    (A : ValuationSubring K') (σ : K' ≃ₐ[F] K') :
    σ • A = A.comap (σ.symm : K' →+* K') := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  simp [AlgEquiv.smul_def]

/-- **Transitivity of the Galois action on the places of a Galois extension of a number field
over a fixed place of the base field.**  If `A` and `B` are valuation subrings of `K'` whose
traces on `F` agree and are not everything, then some `σ : K' ≃ₐ[F] K'` carries `A` onto `B`.

This is the infinite-level compactness argument, using the finite-level transitivity
`Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite` and the fact that
a valuation subring is determined by its traces on the finite normal intermediate fields
(`Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal`). -/
private theorem exists_smul_eq_of_comap_eq_of_isGalois {F K' : Type*} [Field F] [NumberField F]
    [Field K'] [Algebra F K'] [IsGalois F K'] (A B : ValuationSubring K')
    (hC : A.comap (algebraMap F K') ≠ ⊤)
    (hAB : A.comap (algebraMap F K') = B.comap (algebraMap F K')) :
    ∃ σ : K' ≃ₐ[F] K', σ • A = B := by
  let ι : Type _ := {E : IntermediateField F K' // FiniteDimensional F E ∧ Normal F E}
  haveI hneι : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let T : ι → Set (K' ≃ₐ[F] K') := fun E =>
    {σ | (σ • A).comap (algebraMap ↥(E.1) K') = B.comap (algebraMap ↥(E.1) K')}
  have htn : ∀ E : ι, (T E).Nonempty := by
    intro E
    haveI hfin : FiniteDimensional F E.1 := E.2.1
    haveI hnorm : Normal F E.1 := E.2.2
    haveI hfinQ : FiniteDimensional ℚ ↥(E.1) := FiniteDimensional.trans ℚ F ↥(E.1)
    haveI hnum : NumberField ↥(E.1) :=
      { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    haveI hgal : IsGalois F ↥(E.1) := isGalois_of_normal_of_charZero
    have hAne : A.comap (algebraMap ↥(E.1) K') ≠ ⊤ := fun h =>
      hC (comap_algebraMap_eq_top_of_comap_eq_top A h)
    have hBne : B.comap (algebraMap ↥(E.1) K') ≠ ⊤ := fun h =>
      hC (hAB ▸ comap_algebraMap_eq_top_of_comap_eq_top B h)
    have htr : (A.comap (algebraMap ↥(E.1) K')).comap (algebraMap F ↥(E.1)) =
        (B.comap (algebraMap ↥(E.1) K')).comap (algebraMap F ↥(E.1)) := by
      rw [ValuationSubring.comap_comap, ValuationSubring.comap_comap]
      have hcomp : (algebraMap ↥(E.1) K').comp (algebraMap F ↥(E.1)) = algebraMap F K' := by
        ext x
        exact IsScalarTower.algebraMap_apply F ↥(E.1) K' x
      rw [hcomp, hAB]
    obtain ⟨τ, hτ⟩ := Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite
      (A.comap (algebraMap ↥(E.1) K')) (B.comap (algebraMap ↥(E.1) K')) hAne hBne htr
    refine ⟨τ.liftNormal K', ?_⟩
    have hres : AlgEquiv.restrictNormalHom (F := F) (K₁ := K') E.1 (τ.liftNormal K') = τ := by
      rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := K') E.1 (τ.liftNormal K') =
          (τ.liftNormal K').restrictNormal E.1 from rfl]
      exact AlgEquiv.restrict_liftNormal (K₁ := E.1) (E := K') τ
    show ((τ.liftNormal K') • A).comap (algebraMap ↥(E.1) K') =
      B.comap (algebraMap ↥(E.1) K')
    rw [comap_smul_eq_restrictNormalHom_smul A (τ.liftNormal K') E.1, hres, hτ]
  have hcl : ∀ E : ι, IsClosed (T E) := by
    intro E
    haveI hfin : FiniteDimensional F E.1 := E.2.1
    haveI hnorm : Normal F E.1 := E.2.2
    have hEq : T E = (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') E.1) ⁻¹'
        {τ : ↥(E.1) ≃ₐ[F] ↥(E.1) | τ • (A.comap (algebraMap ↥(E.1) K')) =
          B.comap (algebraMap ↥(E.1) K')} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, T]
      rw [comap_smul_eq_restrictNormalHom_smul A σ E.1]
    rw [hEq]
    exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous E.1) (isClosed_discrete _)
  have htd : Directed (· ⊇ ·) T := by
    intro E₁ E₂
    haveI h1f : FiniteDimensional F E₁.1 := E₁.2.1
    haveI h1n : Normal F E₁.1 := E₁.2.2
    haveI h2f : FiniteDimensional F E₂.1 := E₂.2.1
    haveI h2n : Normal F E₂.1 := E₂.2.2
    refine ⟨⟨E₁.1 ⊔ E₂.1, inferInstance, inferInstance⟩, ?_, ?_⟩
    · intro σ hσ
      have h1 := Commons.RingTheory.Valuation.comap_inclusion_comap_eq
        (h := (le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1)) (A := σ • A)
      have h2 := Commons.RingTheory.Valuation.comap_inclusion_comap_eq
        (h := (le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1)) (A := B)
      show (σ • A).comap (algebraMap ↥(E₁.1) K') = B.comap (algebraMap ↥(E₁.1) K')
      rw [← h1, ← h2, hσ]
    · intro σ hσ
      have h1 := Commons.RingTheory.Valuation.comap_inclusion_comap_eq
        (h := (le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1)) (A := σ • A)
      have h2 := Commons.RingTheory.Valuation.comap_inclusion_comap_eq
        (h := (le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1)) (A := B)
      show (σ • A).comap (algebraMap ↥(E₂.1) K') = B.comap (algebraMap ↥(E₂.1) K')
      rw [← h1, ← h2, hσ]
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T htd htn (fun E => (hcl E).isCompact) hcl
  refine ⟨σ, ?_⟩
  exact eq_of_comap_eq_forall_finite_normal (σ • A) B (fun E hfin hnorm =>
    Set.mem_iInter.mp hσ ⟨E, hfin, hnorm⟩)

/-- **Surjectivity of the restriction map on stabilisers of valuation subrings.**  Let `F` be a
number field, `K'` a Galois extension of `F`, `A` a valuation subring of `K'` whose trace on `F`
is proper, and `L ⊆ K'` a finite normal intermediate field.  Then every element `τ : Gal(L/F)`
stabilising `A ∩ L` is the restriction of some `σ : K' ≃ₐ[F] K'` stabilising `A`.

This is the "decomposition group of a place is the inverse limit of the local Galois groups at its
finite levels" statement at the level of the finite quotients.  Suggested route: lift `τ` to
`σ₀ : K' ≃ₐ[F] K'` (`AlgEquiv.liftNormal`), set `B := A.comap σ₀.symm` and apply the transitivity
`Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq` to the pair `(B, A)` over the base field
`↥L` (using `hτ` to identify `B.comap (algebraMap ↥L K')` with `A.comap (algebraMap ↥L K')`), then
use `AlgEquiv.restrictScalars` and `AlgEquiv.commutes` to descend back to `Gal(K'/F)`. -/
theorem exists_mem_stabilizer_restrictNormalHom_eq {F K' : Type*} [Field F] [NumberField F]
    [Field K'] [Algebra F K'] [IsGalois F K'] (A : ValuationSubring K')
    (hC : A.comap (algebraMap F K') ≠ ⊤) (L : IntermediateField F K')
    [FiniteDimensional F L] [Normal F L] (τ : ↥L ≃ₐ[F] ↥L)
    (hτ : τ ∈ MulAction.stabilizer (↥L ≃ₐ[F] ↥L) (A.comap (algebraMap ↥L K'))) :
    ∃ σ : K' ≃ₐ[F] K', σ ∈ MulAction.stabilizer (K' ≃ₐ[F] K') A ∧
      AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L σ = τ := by
  haveI hfinQ : FiniteDimensional ℚ ↥L := FiniteDimensional.trans ℚ F ↥L
  haveI hnum : NumberField ↥L :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI hgal : IsGalois ↥L K' := IsGalois.tower_top_intermediateField L
  have hALne : A.comap (algebraMap ↥L K') ≠ ⊤ := fun h =>
    hC (comap_algebraMap_eq_top_of_comap_eq_top A h)
  have hτ' : τ • (A.comap (algebraMap ↥L K')) = A.comap (algebraMap ↥L K') :=
    (MulAction.mem_stabilizer_iff).mp hτ
  set σ₀ : K' ≃ₐ[F] K' := τ.liftNormal K' with hσ₀
  set B : ValuationSubring K' := σ₀ • A with hB
  have hρ : AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L σ₀ = τ := by
    rw [hσ₀]
    rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L (τ.liftNormal K') =
        (τ.liftNormal K').restrictNormal L from rfl]
    exact AlgEquiv.restrict_liftNormal (K₁ := L) (E := K') τ
  have hBcomap : B.comap (algebraMap ↥L K') = A.comap (algebraMap ↥L K') := by
    rw [hB, comap_smul_eq_restrictNormalHom_smul A σ₀ L, hρ, hτ']
  have hBne : B.comap (algebraMap ↥L K') ≠ ⊤ := by rw [hBcomap]; exact hALne
  obtain ⟨σ', hσ'⟩ := exists_smul_eq_of_comap_eq_of_isGalois (F := ↥L) (K' := K')
    B A hBne hBcomap
  have hfix : AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L (σ'.restrictScalars F) = 1 := by
    rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L (σ'.restrictScalars F) =
        (σ'.restrictScalars F).restrictNormal L from rfl]
    ext x
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictScalars_apply]
    show σ' ↑x = ↑x
    exact σ'.commutes x
  have hsmul : (σ'.restrictScalars F) • B = σ' • B := by
    rw [smul_eq_comap_symm_alg B (σ'.restrictScalars F), smul_eq_comap_symm_alg B σ']
    congr 1
  refine ⟨(σ'.restrictScalars F) * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hB, hsmul, hσ']
  · rw [map_mul, hfix, hρ, one_mul]

end Commons.FieldTheory.Galois
