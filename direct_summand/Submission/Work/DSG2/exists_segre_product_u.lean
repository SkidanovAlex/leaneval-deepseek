import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG4c.ClosedImmersionBaseChange.isClosedImmersion_pullback_of_isPullback

/-!
# DSG2: the `m`-fold product of `ℙⁿ_A` as a closed subscheme of a projective space
(universe-general form)

This file is the universe-general companion of `Submission/Work/DSG2/exists_segre_product.lean`.
There, `A : Type` is a ring in universe `0`; here `A : Type*`, so that all the constructions take
place in `Scheme.{u}` for an arbitrary universe `u`.  The arguments are those of the
`Type`-restricted file, re-run at a general universe:

* `Work.DSG2.SegreProductU.isProper_pspace_toSpec` : `ℙⁿ_A ⟶ Spec A` is proper (universe-general
  version of `Work.DSG2.isProper_pspace_toSpec`), deduced from Mathlib's properness of
  `Proj.toSpecZero`.
* `Work.DSG2.SegreProductU.exists_segre_product_aux` : for `m ≥ 1` the `m`-fold fibre product of
  `ℙⁿ_A` over `Spec A` is a closed subscheme of some `ℙ^M_A` over `Spec A`, its projections are
  proper and it satisfies the universal property of the fibre product.  The Segre embedding
  `ℙ^a_A ×_A ℙ^b_A ↪ ℙ^{(a+1)(b+1)-1}_A` enters as the hypothesis `h2`.

The main requested statement `Work.DSG2.exists_segre_product_u` follows from the auxiliary
statement by taking `π := i ≫ ℙ^M_A.toSpec A M`.
-/

open CategoryTheory AlgebraicGeometry Limits

-- The `haveI`s below really do need to register typeclass instances, so the style linter's
-- suggestion to use `have` (which only applies to proof-irrelevant data) is not appropriate.
set_option linter.style.haveILetI false

namespace Work.DSG2

-- The grading of `MvPolynomial σ A` by homogeneous degree is not a global instance in Mathlib;
-- we enable it locally, exactly as `DSMap` does.
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SegreProductU

universe u

section GradeZero

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The polynomial ring `A[x₀,…,xₙ]` is a finitely generated algebra over its degree-zero part
`𝒜 0 = A·1` (the constant polynomials). -/
theorem finiteType_gradeZero_mvPolynomial :
    Algebra.FiniteType (DSMap.PGr A n 0) (MvPolynomial (Fin (n + 1)) A) := by
  -- `A` sits in `𝒜 0` as the constants and the two algebra structures on `A[x₀,…,xₙ]`
  -- are compatible, so we may restrict scalars along `A → 𝒜 0`.
  haveI : IsScalarTower A (DSMap.PGr A n 0) (MvPolynomial (Fin (n + 1)) A) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := DSMap.PGr A n 0)
      (A := MvPolynomial (Fin (n + 1)) A) fun _ => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType A (DSMap.PGr A n 0)
    (MvPolynomial (Fin (n + 1)) A)

/-- The canonical map `A → 𝒜 0` onto the degree-zero part of `A[x₀,…,xₙ]` is surjective:
`𝒜 0` consists exactly of the constant polynomials. -/
theorem surjective_algebraMap_gradeZero :
    Function.Surjective (algebraMap A (DSMap.PGr A n 0)) := by
  intro r
  have hr : r.1 ∈ (1 : Submodule A (MvPolynomial (Fin (n + 1)) A)) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]
    exact r.2
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp hr
  refine ⟨a, Subtype.ext ?_⟩
  simpa [MvPolynomial.algebraMap_eq] using ha

/-- `Spec.map` of the structure map `A → 𝒜 0` is proper. -/
theorem isProper_specMap_algebraMap_gradeZero :
    IsProper (Spec.map (CommRingCat.ofHom (algebraMap A (DSMap.PGr A n 0)))) := by
  have hsurj := surjective_algebraMap_gradeZero A n
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (DSMap.PGr A n 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.Finite.of_surjective _ hsurj
  haveI := hfin
  infer_instance

/-- `Proj A[x₀,…,xₙ] ⟶ Spec (𝒜 0)` is proper, by Mathlib's properness of `Proj.toSpecZero`. -/
theorem isProper_proj_toSpecZero :
    IsProper (Proj.toSpecZero (DSMap.PGr A n)) := by
  haveI := finiteType_gradeZero_mvPolynomial A n
  infer_instance

/-- `ℙⁿ_A ⟶ Spec A` is proper (universe-general version of
`Work.DSG2.isProper_pspace_toSpec`). -/
theorem isProper_pspace_toSpec :
    IsProper (DSMap.PSpace.toSpec A n) := by
  haveI := finiteType_gradeZero_mvPolynomial A n
  haveI := isProper_specMap_algebraMap_gradeZero A n
  haveI := isProper_proj_toSpecZero A n
  unfold DSMap.PSpace DSMap.PSpace.toSpec DSMap.PGr
  infer_instance

end GradeZero

/-- **Iterated Segre embedding** (universe-general). For `m ≥ 1`, the `m`-fold fibre product of
`ℙⁿ_A` over `Spec A` is a closed subscheme of some projective space `ℙ^M_A` over `Spec A`;
moreover the product projections are proper and satisfy the universal property of the fibre
product. -/
theorem exists_segre_product_aux (A : Type u) [CommRing A]
    (h2 : ∀ (a b : ℕ),
      ∃ (σ : pullback (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ⟶
          DSMap.PSpace A ((a + 1) * (b + 1) - 1)),
        IsClosedImmersion σ ∧
          σ ≫ DSMap.PSpace.toSpec A ((a + 1) * (b + 1) - 1) =
            pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
              DSMap.PSpace.toSpec A a) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (n : ℕ),
      ∃ (P : Scheme) (M : ℕ) (i : P ⟶ DSMap.PSpace A M) (p : Fin m → (P ⟶ DSMap.PSpace A n)),
        IsClosedImmersion i ∧ IsProper (i ≫ DSMap.PSpace.toSpec A M) ∧
        (∀ j, p j ≫ DSMap.PSpace.toSpec A n = i ≫ DSMap.PSpace.toSpec A M) ∧
        (∀ j, IsProper (p j)) ∧
        (∀ (Q : Scheme) (q : Fin m → (Q ⟶ DSMap.PSpace A n))
          (πQ : Q ⟶ Spec (CommRingCat.of A)),
          (∀ j, q j ≫ DSMap.PSpace.toSpec A n = πQ) →
          ∃! (u : Q ⟶ P), u ≫ (i ≫ DSMap.PSpace.toSpec A M) = πQ ∧
            ∀ j, u ≫ p j = q j) := by
  refine Nat.le_induction (m := 1) ?_ ?_
  · -- Base case `m = 1`: the product is `ℙⁿ_A` itself, with the identity as projective model.
    intro n
    refine ⟨DSMap.PSpace A n, n, 𝟙 (DSMap.PSpace A n), fun _ => 𝟙 (DSMap.PSpace A n),
      inferInstance, ?_, ?_, ?_, ?_⟩
    · simpa using isProper_pspace_toSpec A n
    · intro j; simp
    · intro j; infer_instance
    · intro Q q πQ hq
      refine ⟨q 0, ⟨?_, ?_⟩, ?_⟩
      · simpa using hq 0
      · intro j; fin_cases j; simp
      · intro v hv
        simpa using hv.2 0
  · -- Inductive step: fibre the model of `m` factors with `ℙⁿ_A` and apply the Segre embedding.
    intro m hm1 ih n
    obtain ⟨P', M', i', p', hi'_closed, hi'_proper, hp'_c, hp'_p, huniv'⟩ := ih n
    obtain ⟨σ, hσ_closed, hσ_conn⟩ := h2 M' n
    have hpb : IsPullback (pullback.fst (DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n))
        (pullback.snd (DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n))
        (DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) :=
      IsPullback.of_hasPullback _ _
    obtain ⟨j, hj_closed, hj_conn⟩ :=
      Work.DSG4c.ClosedImmersionBaseChange.isClosedImmersion_pullback_of_isPullback
        i' (DSMap.PSpace.toSpec A M')
        (pullback.fst (DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n))
        (pullback.snd (DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n))
        (DSMap.PSpace.toSpec A n) hpb
    let P : Scheme := pullback (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n)
    let p : Fin (m+1) → (P ⟶ DSMap.PSpace A n) :=
      fun t => Fin.cases (motive := fun _ => P ⟶ DSMap.PSpace A n)
        (pullback.snd (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n))
        (fun s => pullback.fst (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) ≫ p' s) t
    have hp_zero : p 0 = pullback.snd (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) :=
      rfl
    have hp_succ : ∀ s, p s.succ =
        pullback.fst (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) ≫ p' s :=
      fun s => rfl
    -- The structure morphism of the closed immersion `j ≫ σ` is the first projection.
    have hi_conn : (j ≫ σ) ≫ DSMap.PSpace.toSpec A ((M'+1)*(n+1)-1) =
        pullback.fst (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) ≫
          (i' ≫ DSMap.PSpace.toSpec A M') := by
      rw [Category.assoc, hσ_conn,
        pullback.condition (f := DSMap.PSpace.toSpec A M') (g := DSMap.PSpace.toSpec A n),
        ← Category.assoc, hj_conn,
        ← pullback.condition (f := i' ≫ DSMap.PSpace.toSpec A M')
          (g := DSMap.PSpace.toSpec A n)]
    haveI := hi'_proper
    haveI : IsProper (DSMap.PSpace.toSpec A n) := isProper_pspace_toSpec A n
    refine ⟨P, (M'+1)*(n+1)-1, j ≫ σ, p, IsClosedImmersion.comp j σ, ?_, ?_, ?_, ?_⟩
    · rw [hi_conn]; infer_instance
    · intro t
      rw [hi_conn]
      induction t using Fin.cases with
      | zero =>
        rw [hp_zero]
        exact (pullback.condition (f := i' ≫ DSMap.PSpace.toSpec A M')
          (g := DSMap.PSpace.toSpec A n)).symm
      | succ s =>
        rw [hp_succ s, Category.assoc, hp'_c s]
    · intro t
      induction t using Fin.cases with
      | zero => rw [hp_zero]; infer_instance
      | succ s =>
        rw [hp_succ s]
        haveI : IsProper (p' s) := hp'_p s
        infer_instance
    · intro Q q πQ hq
      rw [hi_conn]
      have hq' : ∀ s : Fin m, q s.succ ≫ DSMap.PSpace.toSpec A n = πQ := fun s => hq s.succ
      obtain ⟨u', hu'⟩ : ∃! u : Q ⟶ P',
          u ≫ (i' ≫ DSMap.PSpace.toSpec A M') = πQ ∧ ∀ s, u ≫ p' s = q s.succ :=
        huniv' Q (fun s => q s.succ) πQ hq'
      have hw : u' ≫ (i' ≫ DSMap.PSpace.toSpec A M') = q 0 ≫ DSMap.PSpace.toSpec A n := by
        rw [hu'.1.1, hq 0]
      refine ⟨pullback.lift u' (q 0) hw, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, pullback.lift_fst, hu'.1.1]
      · intro t
        induction t using Fin.cases with
        | zero =>
          rw [hp_zero]
          change pullback.lift u' (q 0) hw ≫
            pullback.snd (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) = q 0
          rw [pullback.lift_snd]
        | succ s =>
          rw [hp_succ s]
          show pullback.lift u' (q 0) hw ≫
            (pullback.fst (i' ≫ DSMap.PSpace.toSpec A M') (DSMap.PSpace.toSpec A n) ≫ p' s)
              = q s.succ
          rw [← Category.assoc, pullback.lift_fst, hu'.1.2 s]
      · intro v hv
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine ExistsUnique.unique (huniv' Q (fun s => q s.succ) πQ hq') ⟨?_, ?_⟩ hu'.1
          · exact (Category.assoc _ _ _).trans hv.1
          · intro s
            exact (Category.assoc _ _ _).trans (hv.2 s.succ)
        · rw [pullback.lift_snd]
          exact hv.2 0

end SegreProductU

open SegreProductU

theorem exists_segre_product_u (A : Type*) [CommRing A] (n m : ℕ) (hm : 0 < m)
    (h2 : ∀ (a b : ℕ),
      ∃ (σ : CategoryTheory.Limits.pullback (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ⟶
          DSMap.PSpace A ((a + 1) * (b + 1) - 1)),
        AlgebraicGeometry.IsClosedImmersion σ ∧
          CategoryTheory.CategoryStruct.comp σ (DSMap.PSpace.toSpec A ((a + 1) * (b + 1) - 1)) =
            CategoryTheory.CategoryStruct.comp
              (CategoryTheory.Limits.pullback.fst (DSMap.PSpace.toSpec A a)
                (DSMap.PSpace.toSpec A b))
              (DSMap.PSpace.toSpec A a)) :
    ∃ (P : AlgebraicGeometry.Scheme) (π : P ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
      (p : Fin m → (P ⟶ DSMap.PSpace A n)),
      (∀ j, CategoryTheory.CategoryStruct.comp (p j) (DSMap.PSpace.toSpec A n) = π) ∧
      (∀ j, AlgebraicGeometry.IsProper (p j)) ∧
      AlgebraicGeometry.IsProper π ∧
      (∀ (Q : AlgebraicGeometry.Scheme) (q : Fin m → (Q ⟶ DSMap.PSpace A n))
        (πQ : Q ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)),
        (∀ j, CategoryTheory.CategoryStruct.comp (q j) (DSMap.PSpace.toSpec A n) = πQ) →
        ∃! (u : Q ⟶ P), CategoryTheory.CategoryStruct.comp u π = πQ ∧
          ∀ j, CategoryTheory.CategoryStruct.comp u (p j) = q j) ∧
      (∃ (N : ℕ) (i : P ⟶ DSMap.PSpace A N),
        AlgebraicGeometry.IsClosedImmersion i ∧
          CategoryTheory.CategoryStruct.comp i (DSMap.PSpace.toSpec A N) = π) := by
  obtain ⟨P, M, i, p, hi_closed, hi_proper, hp_conn, hp_proper, huniv⟩ :=
    exists_segre_product_aux A h2 m (Nat.succ_le_of_lt hm) n
  exact ⟨P, i ≫ DSMap.PSpace.toSpec A M, p, hp_conn, hp_proper, hi_proper, huniv,
    M, i, hi_closed, rfl⟩

end Work.DSG2
