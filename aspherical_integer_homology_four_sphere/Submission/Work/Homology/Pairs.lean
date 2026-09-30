import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Relative singular homology and the long exact sequence of a pair

For a topological space `X` and a subspace `A ⊆ X` we have the short exact
sequence of chain complexes
`0 ⟶ C_*(A;R) ⟶ C_*(X;R) ⟶ C_*(X,A;R) ⟶ 0`
and its long exact sequence in homology.  The exactness statements are
`pairHomHX_exact`, `pairHomRel_exact`, `pairHomA_exact`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-! ## The pair sequence is short exact -/

/-- The chain map induced by the inclusion of a subspace is a monomorphism. -/
theorem inclChain_mono (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    Mono (inclChain R X A) := by
  have : Mono (incl A) := by
    rw [TopCat.mono_iff_injective]
    exact Subtype.val_injective
  exact Functor.map_mono ..

/-- A morphism of simplicial sets which is injective in every degree induces an
injective morphism of chain complexes. -/
theorem chainMapMono {X Y : SSet} (f : X ⟶ Y) (hf : ∀ n, Function.Injective (f.app n))
    (R : ModuleCat ℤ) : Mono (SSet.chainComplexMap f R) := by
  apply mono_of_forall_mono_f
  intro n
  let i : X.obj (Opposite.op (SimplexCategory.mk n)) →
      Y.obj (Opposite.op (SimplexCategory.mk n)) :=
    f.app (Opposite.op (SimplexCategory.mk n))
  have hi : Function.Injective i := hf _
  haveI : Mono (Sigma.map' i (fun _ => 𝟙 R)) := by
    have := Limits.MonoCoprod.mono_map'_of_injective
      (fun _ : Y.obj (Opposite.op (SimplexCategory.mk n)) => R) i hi
    simpa using this
  convert this using 2 <;> rfl

/-- The short complex `0 → C_*(A;R) → C_*(X;R) → C_*(X,A;R) → 0` is short exact. -/
theorem pairSeq_shortExact (R : ModuleCat ℤ) (X : TopCat) (A : Set X) :
    (pairSeq R X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (inclChain R X A))
  mono_f := inclChain_mono R X A
  epi_g := inferInstance

/-! ## The long exact sequence -/

/-- The map `H_k(X;R) ⟶ H_k(X,A;R)`. -/
abbrev relProjHom (R : ModuleCat ℤ) (k : ℕ) (X : TopCat) (A : Set X) :
    singHomology R k X ⟶ relHomology R k X A :=
  HomologicalComplex.homologyMap (relProj R X A) k

/-- The connecting homomorphism `H_{k+1}(X,A;R) ⟶ H_k(A;R)` of the pair `(X,A)`. -/
abbrev pairδ (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    relHomology R (k + 1) X A ⟶ singHomology R k (TopCat.of A) :=
  (pairSeq_shortExact R X A).δ (k + 1) k (by simp)

/-- The sequence `H_k(A;R) ⟶ H_k(X;R) ⟶ H_k(X,A;R)`. -/
abbrev pairHomHX (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (inclChain R X A) k)
    (HomologicalComplex.homologyMap (relProj R X A) k)
    (by rw [← HomologicalComplex.homologyMap_comp, (pairSeq R X A).zero,
      HomologicalComplex.homologyMap_zero])

/-- The sequence `H_{k+1}(X;R) ⟶ H_{k+1}(X,A;R) ⟶ H_k(A;R)`. -/
abbrev pairHomRel (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (HomologicalComplex.homologyMap (relProj R X A) (k + 1))
    (pairδ R X A k) ((pairSeq_shortExact R X A).comp_δ (k + 1) k (by simp))

/-- The sequence `H_{k+1}(X,A;R) ⟶ H_k(A;R) ⟶ H_k(X;R)`. -/
abbrev pairHomA (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (pairδ R X A k) (HomologicalComplex.homologyMap (inclChain R X A) k)
    ((pairSeq_shortExact R X A).δ_comp (k + 1) k (by simp))

/-- Exactness of `H_k(A;R) ⟶ H_k(X;R) ⟶ H_k(X,A;R)`. -/
theorem pairHomHX_exact (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    (pairHomHX R X A k).Exact :=
  (pairSeq_shortExact R X A).homology_exact₂ k

/-- Exactness of `H_{k+1}(X;R) ⟶ H_{k+1}(X,A;R) ⟶ H_k(A;R)`. -/
theorem pairHomRel_exact (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    (pairHomRel R X A k).Exact :=
  (pairSeq_shortExact R X A).homology_exact₃ (k + 1) k (by simp)

/-- Exactness of `H_{k+1}(X,A;R) ⟶ H_k(A;R) ⟶ H_k(X;R)`. -/
theorem pairHomA_exact (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (k : ℕ) :
    (pairHomA R X A k).Exact :=
  (pairSeq_shortExact R X A).homology_exact₁ (k + 1) k (by simp)

end

end Work.Homology
