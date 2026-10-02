import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.local_generator_convex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local class at a point of a compact convex set is injective

Let `W ⊆ ℝᴺ` be open (`N ≥ 1`), `B ⊆ W` compact and convex and `x ∈ B`.  The relative chain
complexes `C_*(W, W∖B)` and `C_*(W, W∖{x})` are related by the enlargement map
`relCokerMap (TopCat.of ↥W) (pdRelSub W B) (pdRelSub W {x})` (`B ⊇ {x}`), and this file proves
that it is **injective** on `H_N`, i.e. that a class `β ∈ H_N(W, W∖B)` whose image in the local
homology `H_N(W, W∖{x})` vanishes is itself zero.

The proof has three steps.

* **The vanishing of the relative homology of the pair `(W∖{x}, W∖B)`.**  This is
  `localClass_punctured_isZero`: the two-cover/excision lemma `excision_relChainsMap_isIso`
  applied to the open cover `{y : ↑({x}ᶜ) | y ∈ W} ∪ {y : ↑({x}ᶜ) | y ∉ B} = ℝᴺ ∖ {x}`
  identifies `H_N(W∖{x}, W∖B)` with the flat `H_N(ℝᴺ∖{x}, ℝᴺ∖B)`, which vanishes by
  `isZero_relChains_punctured_euclid` (radial retraction; compact convex `B ∋ x`).
  The canonical relabelling of the two models of `W ∖ {x}` (as a subtype of `ℝᴺ∖{x}` or of
  `W`) is `relChains_homology_subtype_swap`.
* **The same vanishing in the "restricted inclusion" model.**  `coker_inclChainsSub_homology_iso`
  identifies the first term of the exact sequence of the triple `pdRelSub W B ⊆ pdRelSub W {x} ⊆ W`
  with the honest relative complex of the pair `(W∖{x}, W∖B)`.
* **Injectivity from the triple sequence.**  The homology sequence of the triple is exact at the
  middle term (`relChains_triple_shortExact`, `tripleShort_g`), and its first term vanishes in
  degree `N`, so `relCokerMap_homologyMap_ker_eq_bot` gives that the enlargement map has trivial
  kernel.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- **The two representations of a "double subtype" are canonically homeomorphic.**  The subtype
`{a : ↥P | (a : α) ∈ Q}` of the subtype `↥P` and the subtype `{a : ↥Q | (a : α) ∈ P}` of `↥Q`
describe the same set `P ∩ Q`, and the obvious swap map is a homeomorphism. -/
private def subSubtypeHomeoSwap (α : Type) [TopologicalSpace α] (P Q : Set α) :
    {y : ↥P | (y : α) ∈ Q} ≃ₜ {y : ↥Q | (y : α) ∈ P} where
  toFun y := ⟨⟨(y : α), y.2⟩, y.1.2⟩
  invFun z := ⟨⟨(z : α), z.2⟩, z.1.2⟩
  left_inv y := by ext <;> rfl
  right_inv z := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Relative homology is insensitive to the order in which the two identifications of the
ambient set are taken.**  The pair `(P ∩ Q, P ∩ Q ∩ S)`, modelled as a pair in the space `P ∩ Q`
seen as a subtype of `P` or of `Q`, has the same relative homology. -/
private theorem relChains_homology_subtype_swap {α : Type} [TopologicalSpace α] (P Q S : Set α)
    (n : ℕ) :
    Nonempty (((relChains (TopCat.of ↥{a : ↥P | (a : α) ∈ Q})
        {a : ↥{a : ↥P | (a : α) ∈ Q} | (a : α) ∈ S}).homology n) ≅
      ((relChains (TopCat.of ↥{a : ↥Q | (a : α) ∈ P})
        {a : ↥{a : ↥Q | (a : α) ∈ P} | (a : α) ∈ S}).homology n)) := by
  refine relChains_homeomorph (↥{a : ↥P | (a : α) ∈ Q}) (↥{a : ↥Q | (a : α) ∈ P})
    {a : ↥{a : ↥P | (a : α) ∈ Q} | (a : α) ∈ S}
    {a : ↥{a : ↥Q | (a : α) ∈ P} | (a : α) ∈ S}
    (subSubtypeHomeoSwap α P Q) (fun _ => Iff.rfl) n

/-- **The relative homology of the pair `(W∖{x}, W∖B)` vanishes.**

For `W ⊆ ℝᴺ` open (`N ≥ 1`), `B ⊆ W` compact and convex with `x ∈ B`, the relative singular
homology of the pair `(W∖{x}, W∖B)` vanishes in degree `N`: the open cover
`{y ∈ ℝᴺ∖{x} | y ∈ W} ∪ {y ∈ ℝᴺ∖{x} | y ∉ B} = ℝᴺ∖{x}` (valid because `B ⊆ W`) and excision
identify this pair with the flat pair `(ℝᴺ∖{x}, ℝᴺ∖B)`, whose relative homology vanishes. -/
private theorem localClass_punctured_isZero {N : ℕ} (hN : 1 ≤ N)
    {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hBc : IsCompact B) (hBv : Convex ℝ B) (hBW : B ⊆ W)
    {x : EuclideanSpace ℝ (Fin N)} (hxB : x ∈ B) :
    IsZero ((relChains (TopCat.of ↥{y : ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ) |
        (y : EuclideanSpace ℝ (Fin N)) ∈ W})
      {y : ↥{y : ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ) | (y : EuclideanSpace ℝ (Fin N)) ∈ W} |
        (y : ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ)) ∈
          {y : ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ) | (y : EuclideanSpace ℝ (Fin N)) ∈ Bᶜ}}).homology N) := by
  let U : Set (↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ)) :=
    {y | (y : EuclideanSpace ℝ (Fin N)) ∈ W}
  let A : Set (↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ)) :=
    {y | (y : EuclideanSpace ℝ (Fin N)) ∈ Bᶜ}
  have hUopen : IsOpen U := hW.preimage continuous_subtype_val
  have hAopen : IsOpen A := hBc.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcov : U ∪ A = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : (y : EuclideanSpace ℝ (Fin N)) ∈ B
    · exact Or.inl (hBW hy)
    · exact Or.inr (by simpa only [A, Set.mem_ofPred_eq, Set.mem_compl_iff] using hy)
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (relChainsMap (TopCat.of ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ)) U A) N) :=
    excision_relChainsMap_isIso (X := TopCat.of ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ))
      U A hUopen hAopen hcov N
  have hE : IsZero ((relChains (TopCat.of ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ))
      A).homology N) :=
    isZero_relChains_punctured_euclid N hN x B hBc hBv hxB N
  exact IsZero.of_iso hE (asIso (HomologicalComplex.homologyMap
    (relChainsMap (TopCat.of ↥(({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ)) U A) N))

/-- **Injectivity of the enlargement map out of the homology sequence of a triple.**

If the "first" relative complex `coker (inclChainsSub X A B h)` (a model of the relative chains of
the pair `(B, A)`) has vanishing `n`-th homology, then the map
`H_n(X, A) ⟶ H_n(X, B)` induced by `A ⊆ B` (`relCokerMap`) has trivial kernel. -/
private theorem relCokerMap_homologyMap_ker_eq_bot {X : TopCat} {A B : Set X} (h : A ⊆ B) (n : ℕ)
    (hvan : IsZero ((cokernel (inclChainsSub X A B h)).homology n)) :
    LinearMap.ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (relCokerMap X A B h) n)) = ⊥ := by
  have hS : (tripleShort X A B h).ShortExact := relChains_triple_shortExact X A B h
  have hg : (tripleShort X A B h).g = relCokerMap X A B h := tripleShort_g X A B h
  have hf0 : HomologicalComplex.homologyMap (tripleShort X A B h).f n = 0 := by
    refine IsZero.eq_zero_of_src ?_ _
    simpa only [tripleShort_X1] using hvan
  have hr2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A B h).f n)).range =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A B h).g n)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
  rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero] at hr2
  rw [← hg]
  exact hr2.symm

/-! ## The main statement -/

theorem localClass_point_injective {N : ℕ} (hN : 1 ≤ N)
    {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hBc : IsCompact B) (hBv : Convex ℝ B) (hBW : B ⊆ W)
    {x : EuclideanSpace ℝ (Fin N)} (hxB : x ∈ B)
    (β : (relChains (TopCat.of ↥W) (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)).homology N)
    (h : HomologicalComplex.homologyMap
          (relCokerMap (TopCat.of ↥W)
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W ({x} : Set (EuclideanSpace ℝ (Fin N))))
            (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
              (Set.singleton_subset_iff.mpr hxB))) N β = 0) :
    β = 0 := by
  -- Step 1: the vanishing of `H_N(W∖{x}, W∖B)` in the honest model of the pair.
  have hP : IsZero ((relChains
      (TopCat.of ↥(pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
        ({x} : Set (EuclideanSpace ℝ (Fin N)))))
      {y : ↥(pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
          ({x} : Set (EuclideanSpace ℝ (Fin N)))) |
        (y : ↥W) ∈ pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B}).homology N) := by
    obtain ⟨e⟩ := relChains_homology_subtype_swap W (({x} : Set (EuclideanSpace ℝ (Fin N)))ᶜ) Bᶜ N
    exact IsZero.of_iso (localClass_punctured_isZero hN hW hBc hBv hBW hxB) e
  -- Step 2: the same vanishing in the restricted-inclusion (cokernel) model.
  have hvan : IsZero ((cokernel (inclChainsSub (TopCat.of ↥W)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W ({x} : Set (EuclideanSpace ℝ (Fin N))))
      (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
        (Set.singleton_subset_iff.mpr hxB)))).homology N) := by
    obtain ⟨e1⟩ := coker_inclChainsSub_homology_iso (M := TopCat.of ↥W)
      (A := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
      (B := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
        ({x} : Set (EuclideanSpace ℝ (Fin N))))
      (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
        (Set.singleton_subset_iff.mpr hxB)) N
    exact IsZero.of_iso hP e1
  -- Step 3: the exact sequence of the triple turns the vanishing into injectivity.
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of ↥W)
        (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
        (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W ({x} : Set (EuclideanSpace ℝ (Fin N))))
        (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
          (Set.singleton_subset_iff.mpr hxB))) N)) = ⊥ :=
    relCokerMap_homologyMap_ker_eq_bot _ N hvan
  have hmem : β ∈ LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of ↥W)
        (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
        (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W ({x} : Set (EuclideanSpace ℝ (Fin N))))
        (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
          (Set.singleton_subset_iff.mpr hxB))) N)) :=
    LinearMap.mem_ker.mpr h
  simpa [hker] using hmem

end

end Work.Cohomology
