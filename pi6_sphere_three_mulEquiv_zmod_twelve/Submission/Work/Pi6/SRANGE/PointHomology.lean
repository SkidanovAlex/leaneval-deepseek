import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.epsilonNaturality
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The relative homology `Hₙ(B, {b₀}; R)` of a path connected space

For a path connected space `B`, a basepoint `b₀ : B` and a commutative ring `R`, the projection

`C_*(B; R) ⟶ C_*(B, {b₀}; R)`

to the relative chains (the cokernel of the inclusion `C_*({b₀}; R) ⟶ C_*(B; R)`) induces an
isomorphism on homology in every degree `n ≥ 1`.  Equivalently,
`Hₙ(B, {b₀}; R) ≅ Hₙ(B; R)` for `n ≥ 1`, the classical statement that relative homology with
respect to a point is reduced homology.

The proof is the exactness chase in the long exact sequence of the pair

`Hₙ({b₀}) --f--> Hₙ(B) --g--> Hₙ(B,{b₀}) --δ--> H_{n-1}({b₀})`

(`Work.StemsB.relChainsR_exact₁/₂/₃`):

* `g` is injective: exactness at `Hₙ(B)` identifies `ker g` with `im f`, and `f = 0` because
  `Hₙ({b₀}; R) = 0` for `n ≥ 1` (the one point space is contractible);
* `g` is surjective: exactness at `Hₙ(B,{b₀})` identifies `im g` with `ker δ`, and `δ = 0`
  because it is the composite in the exact sequence at `H_{n-1}({b₀})`, where the map
  `H_{n-1}({b₀}; R) ⟶ H_{n-1}(B; R)` is a monomorphism.  For `n ≥ 2` that map has zero source; for
  `n = 1` it is the degree `0` map `H₀({b₀}; R) ⟶ H₀(B; R)`, which is an isomorphism because both
  spaces are path connected: it is the composite of the augmentations
  `H₀({b₀};R) ⟶ R` and `R ≅ H₀(B;R)` (`Work.Cohomology.SSet_homologyMap_homology₀ε`).

The maps `f`, `g`, `δ` being a short exact sequence of chain complexes, the two halves of the
argument are pure consequences of exactness (`ShortComplex.Exact.mono_g_iff`,
`ShortComplex.Exact.epi_f_iff`), so no element-level computation is needed.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SRANGE

noncomputable section

/-- **The homology of the one-point space `{b₀}` vanishes in positive degrees.**  The subspace
`{b₀} ⊆ B` is a subsingleton, hence contractible, so its singular homology agrees with that of a
point (`Work.Cohomology.homologyContractible_ring`). -/
theorem isZero_homology_singleton (R : Type) [CommRing R] {B : Type} [TopologicalSpace B]
    (b₀ : B) (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((Work.Cohomology.singularChains R (TopCat.of ↥({b₀} : Set B))).homology n) :=
  Work.Cohomology.homologyContractible_ring R n (by omega)

/-- A morphism whose source is a zero object is a monomorphism. -/
theorem mono_of_isZero_src {R : Type} [CommRing R] {X Y : ModuleCat R} (h : IsZero X)
    (f : X ⟶ Y) : Mono f := by
  haveI : Subsingleton X := ModuleCat.subsingleton_of_isZero h
  rw [ModuleCat.mono_iff_injective]
  intro a b _
  exact Subsingleton.elim a b

/-- **`H₀(A; R) ⟶ H₀(X; R)` is a monomorphism for `X` and `A` path connected.**  By naturality of
the degree-`0` augmentation (`Work.Cohomology.SSet_homologyMap_homology₀ε`) this map is the
composite `ε_A ≫ ε_X⁻¹` of two isomorphisms; it is even an isomorphism. -/
theorem mono_homologyMap_relChainsRIncl_zero (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    [PathConnectedSpace X] [PathConnectedSpace (TopCat.of A)] :
    Mono (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) 0) := by
  have hX : IsIso (X.singularHomology₀ε (ModuleCat.of R R)) := inferInstance
  have hA : IsIso ((TopCat.of A).singularHomology₀ε (ModuleCat.of R R)) := inferInstance
  have hnat : HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) 0
      ≫ X.singularHomology₀ε (ModuleCat.of R R)
      = (TopCat.of A).singularHomology₀ε (ModuleCat.of R R) :=
    Work.Cohomology.SSet_homologyMap_homology₀ε
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) (ModuleCat.of R R)
  rw [show HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) 0
      = (TopCat.of A).singularHomology₀ε (ModuleCat.of R R)
        ≫ CategoryTheory.inv (X.singularHomology₀ε (ModuleCat.of R R)) from by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **The exactness chase.**  Let `A ⊆ X` and `n = k + 1 ≥ 1`.  If `H_{k+1}(A; R) = 0` and the
inclusion `H_k(A; R) ⟶ H_k(X; R)` is a monomorphism, then the projection to the relative chains
induces an isomorphism `H_{k+1}(X; R) ≅ H_{k+1}(X, A; R)`. -/
theorem isIso_homologyMap_cokernel_π_succ (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    (k : ℕ)
    (h1 : IsZero ((Work.Cohomology.singularChains R (TopCat.of A)).homology (k + 1)))
    (h2 : Mono (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl R X A) k)) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R X A)) (k + 1)) := by
  -- Injectivity: `ker g = im f = 0`, since `H_{k+1}(A) = 0`.
  have hS2 := Work.StemsB.relChainsR_exact₂ R X A (k + 1)
  have hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R X A)) (k + 1)) :=
    hS2.mono_g_iff.mpr (h1.eq_zero_of_src _)
  -- Surjectivity: the connecting map `δ` vanishes, because the previous map in the sequence is a
  -- monomorphism (`ker δ = im g` is then everything).
  have hS1 := Work.StemsB.relChainsR_exact₁ R X A k
  have hδ : Work.StemsB.relChainsRδ R X A k = 0 := hS1.mono_g_iff.mp h2
  have hS3 := Work.StemsB.relChainsR_exact₃ R X A k
  have hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl R X A)) (k + 1)) :=
    hS3.epi_f_iff.mpr hδ
  exact isIso_of_mono_of_epi _

/-- **`Hₙ(B, {b₀}; R) ≅ Hₙ(B; R)` for `B` path connected and `n ≥ 1`.**  The projection to the
relative chains is an isomorphism on homology in every positive degree. -/
theorem PointHomology (R : Type) [CommRing R] {B : Type} [TopologicalSpace B]
    [PathConnectedSpace B] (b₀ : B) (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.StemsB.relChainsRIncl R (TopCat.of B) ({b₀} : Set B))) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h2 : Mono (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl R (TopCat.of B) ({b₀} : Set B)) k) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact mono_homologyMap_relChainsRIncl_zero R (TopCat.of B) ({b₀} : Set B)
    · exact mono_of_isZero_src (isZero_homology_singleton R b₀ k hk) _
  exact isIso_homologyMap_cokernel_π_succ R (TopCat.of B) ({b₀} : Set B) k
    (isZero_homology_singleton R b₀ (k + 1) (by omega)) h2

end

end Work.Pi6.SRANGE
