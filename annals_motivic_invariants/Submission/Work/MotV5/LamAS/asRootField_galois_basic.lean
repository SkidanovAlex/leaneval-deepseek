import Mathlib
import Submission.Work.MotV5.asAut_Kb
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.LamAS.shift_of_pow_five_sub_self
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier root field `𝕜(t)⟮asRoot g⟯`: Galois theory

Let `𝕜` be a field of characteristic `5`, `K = 𝕜(t) = RatFunc 𝕜`, `Kb 𝕜` an algebraic closure of
`K`, and `g ∈ K` a class outside the image of the Artin–Schreier map `℘ u = u⁵ - u`.  Let
`α = asRoot g ∈ Kb 𝕜` be a root of `X⁵ - X - g` (`asRoot_spec`).

This file proves the basic field theory of the root field `F = K⟮α⟯`:

* `F/K` is Galois of degree `5` (the Artin–Schreier extension, cyclic of order `5`);
* the fixed field of `Gal(F/K)` is `K`;
* every `K`-automorphism of `F` shifts the root: `γ α = α + k` with `k : Fin 5`;
* more generally, if `W` lies in *any* intermediate field `L ⊆ Kb 𝕜` and satisfies
  `W⁵ - W = g'` for some `g' ∈ K`, then every `K`-automorphism of `L` shifts `W` by an element of
  the prime field `𝔽₅` (this is `Work.MotV5.LamAS.shift_of_pow_five_sub_self`).

The ingredient that makes the root field a splitting field of `X⁵ - X - g` is
`Work.MotV5.LamAS.root_eq_asRoot_add`: every root of that polynomial in `Kb 𝕜` differs from
`asRoot g` by an element of the prime field, because the difference of two roots of `X⁵ - X - g`
satisfies `z⁵ = z` and in characteristic `5` the solutions of `z⁵ = z` are exactly `0,1,2,3,4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.MotV5.LamAS

open Polynomial

noncomputable section

/-- The `Nat.cast` form of `root_eq_asRoot_add`, convenient for the membership computations in the
splitting-field argument below. -/
theorem root_eq_asRoot_add_natCast {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜)
    {β : Work.MotV.Kb 𝕜} (hβ : β ^ 5 - β = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) :
    ∃ k : Fin 5, β = Work.MotV5.asRoot g + ((k : ℕ) : Work.MotV.Kb 𝕜) := by
  obtain ⟨k, hk⟩ := root_eq_asRoot_add g hβ
  exact ⟨k, by
    rw [hk, show algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ)
        = ((k : ℕ) : Work.MotV.Kb 𝕜) from by push_cast; rfl]⟩

/-! ## §1 The root field and its Artin–Schreier polynomial -/

/-- The Artin–Schreier root field `K⟮asRoot g⟯ ⊆ Kb 𝕜`.  (A local name: the sibling module
`ASGalois` declares the same object as `Work.MotV5.LamAS.asRootField`.) -/
def asRootFieldAux {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜) :=
  IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))

/-- The polynomial `X ^ 5 - X - g` over `K = RatFunc 𝕜` is separable (its derivative is `-1`). -/
theorem separable_asPolyK {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜) :
    (Work.MotV5.asPolyK g).Separable := by
  have h := Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C' (R := RatFunc 𝕜) 5 5
    (1 : RatFunc 𝕜) (-1) (-g) (dvd_refl 5) (isUnit_one.neg)
  have hp : (Polynomial.C (1 : RatFunc 𝕜) * Polynomial.X ^ 5 + Polynomial.C (-1) * Polynomial.X
      + Polynomial.C (-g) : (RatFunc 𝕜)[X]) = Work.MotV5.asPolyK g := by
    rw [Work.MotV5.asPolyK]
    simp only [Polynomial.C_neg, Polynomial.C_1]
    first | refl_ring1 | ring
  rwa [hp] at h

/-- `(X ^ 5 - X - g).natDegree = 5`. -/
theorem natDegree_asPolyK {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) :
    (Work.MotV5.asPolyK g).natDegree = 5 := by
  rw [Work.MotV5.asPolyK]
  compute_degree!

/-- `asRoot g` is integral over `K = RatFunc 𝕜`. -/
theorem isIntegral_asRoot {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) :
    IsIntegral (RatFunc 𝕜) (Work.MotV5.asRoot g) :=
  ⟨Work.MotV5.asPolyK g, Work.MotV5.asPolyK_monic g, Work.MotV5.asPolyK_aeval_root g⟩

/-- The root field `K⟮asRoot g⟯` is a splitting field of `X ^ 5 - X - g` over `K`. -/
theorem isSplittingField_asRootFieldAux {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜) :
    Polynomial.IsSplittingField (RatFunc 𝕜) ↥(asRootFieldAux g) (Work.MotV5.asPolyK g) := by
  rw [IntermediateField.isSplittingField_iff]
  have hne : Work.MotV5.asPolyK g ≠ 0 := (Work.MotV5.asPolyK_monic g).ne_zero
  have hmem : ∀ x ∈ (Work.MotV5.asPolyK g).rootSet (Work.MotV.Kb 𝕜), x ∈ asRootFieldAux g := by
    intro x hx
    rw [Polynomial.mem_rootSet_of_ne hne] at hx
    have hx' : x ^ 5 - x = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g := by
      have h : x ^ 5 - x - algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g = 0 := by
        simpa [Work.MotV5.asPolyK] using hx
      linear_combination (norm := first | refl_ring1 | ring1) h
    obtain ⟨k, hk⟩ := root_eq_asRoot_add_natCast g hx'
    rw [asRootFieldAux, hk]
    refine IntermediateField.add_mem _
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) ?_
    rw [← map_natCast (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (k : ℕ)]
    exact IntermediateField.algebraMap_mem _ _
  refine ⟨IntermediateField.splits_of_splits (p := Work.MotV5.asPolyK g)
    (F := asRootFieldAux g) (IsAlgClosed.splits _) hmem, ?_⟩
  rw [asRootFieldAux]
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact IntermediateField.subset_adjoin _ _
      ((Polynomial.mem_rootSet_of_ne (p := Work.MotV5.asPolyK g) hne).mpr
        (Work.MotV5.asPolyK_aeval_root g))
  · rw [IntermediateField.adjoin_le_iff]
    exact hmem

/-- The root field `K⟮asRoot g⟯` is Galois over `K`. -/
theorem isGalois_asRootFieldAux {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜) :
    IsGalois (RatFunc 𝕜) ↥(asRootFieldAux g) := by
  haveI : Polynomial.IsSplittingField (RatFunc 𝕜) ↥(asRootFieldAux g)
      (Work.MotV5.asPolyK g) := isSplittingField_asRootFieldAux g
  exact IsGalois.of_separable_splitting_field (p := Work.MotV5.asPolyK g) (separable_asPolyK g)

/-- `[K⟮asRoot g⟯ : K] = 5`. -/
theorem finrank_asRootFieldAux {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜)
    (hg : ¬ ∃ u : RatFunc 𝕜, u ^ 5 - u = g) :
    Module.finrank (RatFunc 𝕜) ↥(asRootFieldAux g) = 5 := by
  have h := IntermediateField.adjoin.finrank (K := RatFunc 𝕜) (isIntegral_asRoot g)
  rw [Work.MotV5.minpoly_asRoot g hg, natDegree_asPolyK] at h
  exact h

/-- The fixed field of `Gal(K⟮asRoot g⟯/K)` is `K`. -/
theorem mem_range_algebraMap_of_fixed_asRootFieldAux {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
    (g : RatFunc 𝕜) (x : ↥(asRootFieldAux g))
    (hx : ∀ γ : ↥(asRootFieldAux g) ≃ₐ[RatFunc 𝕜] ↥(asRootFieldAux g), γ x = x) :
    ∃ c : RatFunc 𝕜, algebraMap (RatFunc 𝕜) ↥(asRootFieldAux g) c = x := by
  haveI := isGalois_asRootFieldAux g
  haveI : FiniteDimensional (RatFunc 𝕜) ↥(asRootFieldAux g) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_asRoot g)
  exact (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx

/-! ## §2 The theorem -/

theorem asRootField_galois_basic (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (g : RatFunc 𝕜)
    (hg : ¬ ∃ u : RatFunc 𝕜, u ^ 5 - u = g) :
    IsGalois (RatFunc 𝕜)
        ↥(IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))) ∧
      Module.finrank (RatFunc 𝕜)
        ↥(IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))) = 5 ∧
      (∀ x : ↥(IntermediateField.adjoin (RatFunc 𝕜)
            ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))),
        (∀ γ : ↥(IntermediateField.adjoin (RatFunc 𝕜)
              ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))) ≃ₐ[RatFunc 𝕜]
            ↥(IntermediateField.adjoin (RatFunc 𝕜)
              ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))), γ x = x) →
        ∃ c : RatFunc 𝕜, algebraMap (RatFunc 𝕜) _ c = x) ∧
      (∀ γ : ↥(IntermediateField.adjoin (RatFunc 𝕜)
            ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))) ≃ₐ[RatFunc 𝕜]
          ↥(IntermediateField.adjoin (RatFunc 𝕜)
            ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))),
        ∃ k : Fin 5,
          γ ⟨Work.MotV5.asRoot g, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ =
            ⟨Work.MotV5.asRoot g, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
              + algebraMap ℤ _ ((k : Fin 5) : ℤ)) ∧
      (∀ (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (W : Work.MotV.Kb 𝕜) (hW : W ∈ L)
        (g' : RatFunc 𝕜), W ^ 5 - W = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g' →
        ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L, ∃ k : Fin 5,
          γ ⟨W, hW⟩ = ⟨W, hW⟩ + algebraMap ℤ ↥L ((k : Fin 5) : ℤ)) := by
  refine ⟨isGalois_asRootFieldAux g, finrank_asRootFieldAux g hg,
    mem_range_algebraMap_of_fixed_asRootFieldAux g, ?_, ?_⟩
  · intro γ
    have hmem : Work.MotV5.asRoot g ∈ asRootFieldAux g :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have hpow : (⟨Work.MotV5.asRoot g, hmem⟩ : ↥(asRootFieldAux g)) ^ 5
          - ⟨Work.MotV5.asRoot g, hmem⟩
        = algebraMap (RatFunc 𝕜) ↥(asRootFieldAux g) g := by
      apply Subtype.ext
      simp [Work.MotV5.asRoot_spec g]
    exact shift_of_pow_five_sub_self (F := RatFunc 𝕜) hpow γ
  · intro L W hW g' hg' γ
    have hpow : (⟨W, hW⟩ : ↥L) ^ 5 - ⟨W, hW⟩
        = algebraMap (RatFunc 𝕜) ↥L g' := by
      apply Subtype.ext
      simpa using hg'
    exact shift_of_pow_five_sub_self (F := RatFunc 𝕜) hpow γ

end

end Work.MotV5.LamAS
