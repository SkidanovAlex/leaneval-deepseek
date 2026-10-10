import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AsAutKb
import Submission.Work.MotC5N3.LamAS.root_eq_asRoot_add
import Submission.Work.MotV5.LamAS.shift_of_pow_five_sub_self
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier root field `K⟮asRoot g⟯`: Galois theory (general base field `K`)

Port of `Submission/Work/MotV5/LamAS/asRootField_galois_basic.lean` with `RatFunc 𝕜` replaced by an
arbitrary field `K` of characteristic `5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.MotC5N3.LamAS

open Polynomial

noncomputable section

/-- The `Nat.cast` form of `root_eq_asRoot_add`. -/
theorem root_eq_asRoot_add_natCast {K : Type} [Field K] [CharP K 5] (g : K) {β : KbA K}
    (hβ : β ^ 5 - β = algebraMap K (KbA K) g) :
    ∃ k : Fin 5, β = asRoot g + ((k : ℕ) : KbA K) := by
  obtain ⟨k, hk⟩ := root_eq_asRoot_add g hβ
  exact ⟨k, by
    rw [hk, show algebraMap ℤ (KbA K) ((k : Fin 5) : ℤ)
        = ((k : ℕ) : KbA K) from by push_cast; rfl]⟩

/-! ## §1 The root field and its Artin–Schreier polynomial -/

/-- The Artin–Schreier root field `K⟮asRoot g⟯ ⊆ KbA K`. -/
def asRootFieldAux {K : Type} [Field K] (g : K) : IntermediateField K (KbA K) :=
  IntermediateField.adjoin K ({asRoot g} : Set (KbA K))

/-- The polynomial `X ^ 5 - X - g` over `K` is separable. -/
theorem separable_asPolyK {K : Type} [Field K] [CharP K 5] (g : K) :
    (asPolyK g).Separable := by
  have h := Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C' (R := K) 5 5
    (1 : K) (-1) (-g) (dvd_refl 5) (isUnit_one.neg)
  have hp : (Polynomial.C (1 : K) * Polynomial.X ^ 5 + Polynomial.C (-1) * Polynomial.X
      + Polynomial.C (-g) : (K)[X]) = asPolyK g := by
    rw [asPolyK]
    simp only [Polynomial.C_neg, Polynomial.C_1]
    first | refl_ring1 | ring
  rwa [hp] at h

/-- `(X ^ 5 - X - g).natDegree = 5`. -/
theorem natDegree_asPolyK {K : Type} [Field K] (g : K) : (asPolyK g).natDegree = 5 := by
  rw [asPolyK]
  compute_degree!

/-- `asRoot g` is integral over `K`. -/
theorem isIntegral_asRoot {K : Type} [Field K] (g : K) : IsIntegral K (asRoot g) :=
  ⟨asPolyK g, asPolyK_monic g, asPolyK_aeval_root g⟩

/-- The root field `K⟮asRoot g⟯` is a splitting field of `X ^ 5 - X - g` over `K`. -/
theorem isSplittingField_asRootFieldAux {K : Type} [Field K] [CharP K 5] (g : K) :
    Polynomial.IsSplittingField K ↥(asRootFieldAux g) (asPolyK g) := by
  rw [IntermediateField.isSplittingField_iff]
  have hne : asPolyK g ≠ 0 := (asPolyK_monic g).ne_zero
  have hmem : ∀ x ∈ (asPolyK g).rootSet (KbA K), x ∈ asRootFieldAux g := by
    intro x hx
    rw [Polynomial.mem_rootSet_of_ne hne] at hx
    have hx' : x ^ 5 - x = algebraMap K (KbA K) g := by
      have h : x ^ 5 - x - algebraMap K (KbA K) g = 0 := by
        simpa [asPolyK] using hx
      linear_combination (norm := first | refl_ring1 | ring1) h
    obtain ⟨k, hk⟩ := root_eq_asRoot_add_natCast g hx'
    rw [asRootFieldAux, hk]
    refine IntermediateField.add_mem _
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) ?_
    rw [← map_natCast (algebraMap K (KbA K)) (k : ℕ)]
    exact IntermediateField.algebraMap_mem _ _
  refine ⟨IntermediateField.splits_of_splits (p := asPolyK g)
    (F := asRootFieldAux g) (IsAlgClosed.splits _) hmem, ?_⟩
  rw [asRootFieldAux]
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact IntermediateField.subset_adjoin _ _
      ((Polynomial.mem_rootSet_of_ne (p := asPolyK g) hne).mpr
        (asPolyK_aeval_root g))
  · rw [IntermediateField.adjoin_le_iff]
    exact hmem

/-- The root field `K⟮asRoot g⟯` is Galois over `K`. -/
theorem isGalois_asRootFieldAux {K : Type} [Field K] [CharP K 5] (g : K) :
    IsGalois K ↥(asRootFieldAux g) := by
  haveI : Polynomial.IsSplittingField K ↥(asRootFieldAux g) (asPolyK g) :=
    isSplittingField_asRootFieldAux g
  exact IsGalois.of_separable_splitting_field (p := asPolyK g) (separable_asPolyK g)

/-- `[K⟮asRoot g⟯ : K] = 5`. -/
theorem finrank_asRootFieldAux {K : Type} [Field K] [CharP K 5] (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Module.finrank K ↥(asRootFieldAux g) = 5 := by
  have h := IntermediateField.adjoin.finrank (K := K) (isIntegral_asRoot g)
  rw [minpoly_asRoot g hg, natDegree_asPolyK] at h
  exact h

/-- The fixed field of `Gal(K⟮asRoot g⟯/K)` is `K`. -/
theorem mem_range_algebraMap_of_fixed_asRootFieldAux {K : Type} [Field K] [CharP K 5]
    (g : K) (x : ↥(asRootFieldAux g))
    (hx : ∀ γ : ↥(asRootFieldAux g) ≃ₐ[K] ↥(asRootFieldAux g), γ x = x) :
    ∃ c : K, algebraMap K ↥(asRootFieldAux g) c = x := by
  haveI := isGalois_asRootFieldAux g
  haveI : FiniteDimensional K ↥(asRootFieldAux g) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_asRoot g)
  exact (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx

/-! ## §2 The theorem -/

theorem asRootField_galois_basic (K : Type) [Field K] [CharP K 5] (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    IsGalois K ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))) ∧
      Module.finrank K
        ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))) = 5 ∧
      (∀ x : ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))),
        (∀ γ : ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))) ≃ₐ[K]
            ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))), γ x = x) →
        ∃ c : K, algebraMap K _ c = x) ∧
      (∀ γ : ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))) ≃ₐ[K]
          ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))),
        ∃ k : Fin 5,
          γ ⟨asRoot g, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ =
            ⟨asRoot g, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
              + algebraMap ℤ _ ((k : Fin 5) : ℤ)) ∧
      (∀ (L : IntermediateField K (KbA K)) (W : KbA K) (hW : W ∈ L)
        (g' : K), W ^ 5 - W = algebraMap K (KbA K) g' →
        ∀ γ : ↥L ≃ₐ[K] ↥L, ∃ k : Fin 5,
          γ ⟨W, hW⟩ = ⟨W, hW⟩ + algebraMap ℤ ↥L ((k : Fin 5) : ℤ)) := by
  refine ⟨isGalois_asRootFieldAux g, finrank_asRootFieldAux g hg,
    mem_range_algebraMap_of_fixed_asRootFieldAux g, ?_, ?_⟩
  · intro γ
    have hmem : asRoot g ∈ asRootFieldAux g :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have hpow : (⟨asRoot g, hmem⟩ : ↥(asRootFieldAux g)) ^ 5
          - ⟨asRoot g, hmem⟩
        = algebraMap K ↥(asRootFieldAux g) g := by
      apply Subtype.ext
      simp [asRoot_spec g]
    exact Work.MotV5.LamAS.shift_of_pow_five_sub_self (F := K) hpow γ
  · intro L W hW g' hg' γ
    have hpow : (⟨W, hW⟩ : ↥L) ^ 5 - ⟨W, hW⟩
        = algebraMap K ↥L g' := by
      apply Subtype.ext
      simpa using hg'
    exact Work.MotV5.LamAS.shift_of_pow_five_sub_self (F := K) hpow γ

end

end Work.MotC5N3.LamAS
