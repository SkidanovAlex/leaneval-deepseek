import Mathlib
import Submission.Work.Cohomology.DualComplex

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The dual of an acyclic chain complex of vector spaces is acyclic

Let `k` be a field and `C` a chain complex of `k`-modules which is *acyclic*, i.e.
`Hₙ(C) = 0` for every `n`.  Then the dual cochain complex `dualComplex k C` (whose objects are
`Hom_k(Cₙ, k)` and whose differentials are the transposes of those of `C`) is acyclic as well:
`Hⁿ(dualComplex k C) = 0` for every `n`.

This is the statement that the exact functor `Hom_k(-, k)` sends exact sequences of vector spaces
to exact sequences: over a field every subspace admits a complement, so every linear functional on
a subspace extends to the whole space, which is exactly what is needed to dualise an exact pair
`A --f--> B --g--> C` into the exact pair `C* --gᵀ--> B* --fᵀ--> A*`.

Concretely, the proof computes

* `(dualComplex k C).d n (n+1) = dualDiff k C n` (`dualComplex_d_succ`), whose underlying linear
  map is the transpose `(C.d (n+1) n)ᵀ` (`dualDiff_hom`);
* the exactness of `C` in degree `n = m+1`, in the form
  `range (C.d (m+2) (m+1)) = ker (C.d (m+1) m)`, which by `range_dualMap_of_range_eq_ker`
  (`LinearMap.range_dualMap_eq_dualAnnihilator_ker` together with Mathlib's identification of the
  kernel of a transpose with an annihilator) dualises to
  `range (dualDiff k C m) = ker (dualDiff k C (m+1))`.

The degree `n = 0` is the boundary case, where the incoming differential of the dual complex
vanishes and the outgoing one is the transpose of the surjection `C.d 1 0`.
-/

namespace Work.Cohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- The underlying linear map of `dualDiff k C n` is the transpose of `(C.d (n+1) n).hom`. -/
lemma dualDiff_hom (k : Type) [Field k] (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ) :
    (dualDiff k C n).hom = ((C.d (n+1) n).hom).dualMap := by
  ext φ
  rfl

/-- The differential of the dual complex in the syntactic shape `(n, n+1)`. -/
lemma dualComplex_d_succ (k : Type) [Field k] (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ) :
    (dualComplex k C).d n (n+1) = dualDiff k C n := by
  simp only [dualComplex, CochainComplex.of, CochainComplex.of.d]
  rfl

/-- The differential of the dual complex from degree `0` to degree `0` vanishes. -/
lemma dualComplex_d_zero (k : Type) [Field k] (C : ChainComplex (ModuleCat k) ℕ) :
    (dualComplex k C).d 0 0 = 0 := by
  simp only [dualComplex, CochainComplex.of, CochainComplex.of.d]
  rfl

/-- Dualising an exact pair of linear maps between vector spaces: if
`range f = ker g` then `range gᵀ = ker fᵀ`.

This is the exactness of `Hom_k(-, k)` on vector spaces, and is where the hypothesis that the base
ring is a field is used (via `LinearMap.range_dualMap_eq_dualAnnihilator_ker`, i.e. the extension
of functionals from a subspace to the whole space). -/
lemma range_dualMap_of_range_eq_ker (k : Type) [Field k] {V₁ V₂ V₃ : Type*}
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [AddCommGroup V₃] [Module k V₃] {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h]

/-- **The dual of an acyclic chain complex of vector spaces is acyclic**, degree by degree. -/
lemma dualComplex_exactAt (k : Type) [Field k] (C : ChainComplex (ModuleCat k) ℕ)
    (hC : ∀ n : ℕ, CategoryTheory.Limits.IsZero (C.homology n)) (n : ℕ) :
    (dualComplex k C).ExactAt n := by
  rcases n with _ | m
  · -- degree `0`: the outgoing differential of `C` is onto, so its transpose is injective
    have hEx0 : C.ExactAt 0 :=
      (HomologicalComplex.exactAt_iff_isZero_homology C 0).mpr (hC 0)
    rw [C.exactAt_iff' 1 0 0
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
      (ComplexShape.next_eq_self' _ 0 (fun j h => by
        have h' : j + 1 = 0 := h
        omega))] at hEx0
    have hg0 : (C.sc' 1 0 0).g = 0 := by
      rw [show (C.sc' 1 0 0).g = C.d 0 0 from rfl]
      exact HomologicalComplex.shape C 0 0 (fun h => by
        have h' : 0 + 1 = 0 := h
        omega)
    have hepi : Epi (C.sc' 1 0 0).f := (ShortComplex.exact_iff_epi _ hg0).mp hEx0
    have hsurj : Function.Surjective (ModuleCat.Hom.hom (C.d 1 0)) := by
      have h := (ModuleCat.epi_iff_surjective ((C.sc' 1 0 0).f)).mp hepi
      rw [show (C.sc' 1 0 0).f = C.d 1 0 from rfl] at h
      exact h
    rw [HomologicalComplex.exactAt_iff' (dualComplex k C) 0 0 1
      (ComplexShape.prev_eq_self' _ 0 (fun j h => by
        have h' : j + 1 = 0 := h
        omega))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl))]
    have hf0 : ((dualComplex k C).sc' 0 0 1).f = 0 := by
      rw [show ((dualComplex k C).sc' 0 0 1).f = (dualComplex k C).d 0 0 from rfl]
      exact dualComplex_d_zero k C
    refine (ShortComplex.exact_iff_mono _ hf0).mpr ?_
    have hg : ((dualComplex k C).sc' 0 0 1).g = dualDiff k C 0 := by
      rw [show ((dualComplex k C).sc' 0 0 1).g = (dualComplex k C).d 0 1 from rfl]
      exact dualComplex_d_succ k C 0
    rw [hg]
    have hinj : Function.Injective (ModuleCat.Hom.hom (dualDiff k C 0)) := by
      rw [dualDiff_hom k C 0]
      exact LinearMap.dualMap_injective_of_surjective hsurj
    exact (ModuleCat.mono_iff_injective _).mpr hinj
  · -- degree `m+1`: dualise the exact sequence `C_{m+2} → C_{m+1} → C_m`
    have hEx : C.ExactAt (m+1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology C (m+1)).mpr (hC (m+1))
    rw [C.exactAt_iff' (m+2) (m+1) m
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (m+2) (m+1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (m+1) m from rfl))] at hEx
    have hker : LinearMap.range (ModuleCat.Hom.hom (C.d (m+2) (m+1)))
        = LinearMap.ker (ModuleCat.Hom.hom (C.d (m+1) m)) :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker (C.sc' (m+2) (m+1) m)).mp hEx
    have hdual : LinearMap.range (dualDiff k C m).hom
        = LinearMap.ker (dualDiff k C (m+1)).hom := by
      have h := range_dualMap_of_range_eq_ker k hker
      rw [← dualDiff_hom k C m, ← dualDiff_hom k C (m+1)] at h
      exact h
    rw [HomologicalComplex.exactAt_iff' (dualComplex k C) m (m+1) (m+2)
      (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel m (m+1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (m+1) (m+2) from rfl))]
    have hf : ((dualComplex k C).sc' m (m+1) (m+2)).f = dualDiff k C m := by
      rw [show ((dualComplex k C).sc' m (m+1) (m+2)).f = (dualComplex k C).d m (m+1) from rfl]
      exact dualComplex_d_succ k C m
    have hg : ((dualComplex k C).sc' m (m+1) (m+2)).g = dualDiff k C (m+1) := by
      rw [show ((dualComplex k C).sc' m (m+1) (m+2)).g = (dualComplex k C).d (m+1) (m+2)
        from rfl]
      exact dualComplex_d_succ k C (m+1)
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker
      ((dualComplex k C).sc' m (m+1) (m+2))).mpr ?_
    rw [hf, hg]
    exact hdual

theorem dualComplex_acyclic_of_acyclic (k : Type) [Field k]
    (C : ChainComplex (ModuleCat k) ℕ)
    (hC : ∀ n : ℕ, CategoryTheory.Limits.IsZero (C.homology n)) (n : ℕ) :
    CategoryTheory.Limits.IsZero ((dualComplex k C).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact dualComplex_exactAt k C hC n

end

end Work.Cohomology
