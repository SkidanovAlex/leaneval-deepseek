import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.pdHom_iUnion_lift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The top homology of an open subset of `ℝ^N` vanishes

For an open subset `U ⊆ ℝ^N` (`N ≥ 1`) the `N`-th singular homology `H_N(U; ℤ)` vanishes.

This is the top-degree case of Hatcher, *Algebraic Topology*, Proposition 3.29 for Euclidean
space: a connected non-compact `n`-manifold has `H_i = 0` for `i ≥ n`.

## The argument

1. **Complements of compact sets.**  For a compact `A ⊆ ℝ^N` and `j ≥ N` we have
   `H_j(ℝ^N ∖ A) = 0`: the long exact sequence of the pair `(ℝ^N, ℝ^N ∖ A)` has
   `H_{j+1}(ℝ^N) = H_j(ℝ^N) = 0` (contractibility) and `H_{j+1}(ℝ^N, ℝ^N∖A) = 0`
   (Hatcher's Lemma 3.27 (b), `relChains_vanishing_of_compact`, since `j + 1 > N`), so the
   connecting map `H_{j+1}(ℝ^N, ℝ^N∖A) ⟶ H_j(ℝ^N∖A)` is an isomorphism onto a zero group
   (`hPairδ_isIso`).

2. **Bounded open sets.**  Let `W` be open with compact closure and put `A = closure W ∖ W`, so
   that `ℝ^N ∖ A = W ⊔ (ℝ^N ∖ closure W)` is a disjoint union of two *open* sets.  The space
   `ℝ^N ∖ A` has trivial `H_N` by step 1, whereas Mayer–Vietoris for the disjoint open cover gives
   `H_N(W) ⊕ H_N(ℝ^N∖closure W) ≅ H_N(ℝ^N ∖ A) = 0`; hence `H_N(W) = 0`.

3. **The general open set.**  Writing `U` as the increasing union of the bounded open sets
   `U ∩ B(0,k)`, every class of `H_N(U)` comes from some finite stage (`pdHom_iUnion_lift`), where
   it is zero by step 2.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The singular homology of the empty space -/

/-- The singular `n`-simplices of an empty space form an empty type: a singular simplex is a
continuous map from the (nonempty) standard `n`-simplex into the empty space. -/
theorem isEmpty_simplex_of_isEmpty_aux (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op ⦋n⦌)) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquiv Y (Opposite.op ⦋n⦌)) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋n⦌)).len + 1)))) :=
    inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

/-- Every component of the singular chain complex of an empty space is a zero object. -/
theorem isZero_singularChains_of_isEmpty_aux (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((singularChains ℤ Y).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op ⦋n⦌)) :=
    isEmpty_simplex_of_isEmpty_aux Y n
  exact isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op ⦋n⦌)) => ModuleCat.of ℤ ℤ)

/-- **The singular homology of the empty space vanishes.** -/
theorem isZero_homology_of_isEmpty_aux (Y : TopCat) [IsEmpty (↥Y)] (m : ℕ) :
    IsZero ((singularChains ℤ Y).homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (isZero_singularChains_of_isEmpty_aux Y m)

/-! ## A summand of a biproduct with vanishing homology vanishes -/

/-- If the homology in degree `k` of a biproduct of chain complexes vanishes, then so does the
homology in degree `k` of each factor. -/
theorem isZero_homology_of_isZero_biprod_homology_aux {C D : ChainComplex (ModuleCat ℤ) ℕ} (k : ℕ)
    (h : IsZero ((C ⊞ D).homology k)) : IsZero (C.homology k) := by
  rw [IsZero.iff_id_eq_zero]
  have h0 : HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k = 0 :=
    IsZero.eq_zero_of_tgt h _
  calc (𝟙 (C.homology k))
      = HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k := by
        rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
          HomologicalComplex.homologyMap_id]
    _ = 0 := by rw [h0, zero_comp]

/-! ## Mayer–Vietoris for a disjoint cover -/

/-- **Mayer–Vietoris for a disjoint cover.**  If `U, V ⊆ X` are open with `U ∪ V = X` and the
homology of `U ∩ V` vanishes in degrees `m` and `m + 1`, then the Mayer–Vietoris map
`H_{m+1}(U) ⊕ H_{m+1}(V) ⟶ H_{m+1}(X)` is an isomorphism. -/
theorem isIso_mvRightX_of_isZero_inter_aux {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ)
    (h1 : IsZero ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homology (m + 1)))
    (h0 : IsZero ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homology m)) :
    IsIso (mvRightX U V hU hV hcov (m + 1)) := by
  have hiso : IsIso (HomologicalComplex.homologyMap (mvRight U V) (m + 1)) := by
    haveI : Mono (HomologicalComplex.homologyMap (mvRight U V) (m + 1)) :=
      (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src h1 _)).1 (mv_H_exact₂ U V (m + 1))
    haveI : Epi (HomologicalComplex.homologyMap (mvRight U V) (m + 1)) :=
      (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt h0 _)).1 (mv_H_exact₃ U V m)
    exact isIso_of_mono_of_epi _
  haveI := hiso
  rw [mvRightX]
  infer_instance

/-! ## Complements of compact sets -/

/-- **The homology of the complement of a compact set vanishes above the dimension.**
For a compact `A ⊆ ℝ^N` and `j ≥ N` we have `H_j(ℝ^N ∖ A) = 0`.

The long exact sequence of the pair `(ℝ^N, ℝ^N∖A)` has `H_{j+1}(ℝ^N) = H_j(ℝ^N) = 0` (the space is
contractible) and `H_{j+1}(ℝ^N, ℝ^N∖A) = 0` (Hatcher's Lemma 3.27 (b), since `j + 1 > N`); hence
the connecting map `H_{j+1}(ℝ^N, ℝ^N∖A) ⟶ H_j(ℝ^N∖A)` is an isomorphism onto a zero group. -/
theorem compl_homology_vanishing_of_compact_aux {N : ℕ} (hN : 1 ≤ N)
    (A : Set (EuclideanSpace ℝ (Fin N))) (hAc : IsCompact A) (j : ℕ) (hj : N ≤ j) :
    IsZero ((singularChains ℤ (TopCat.of ↥(Aᶜ))).homology j) := by
  haveI : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin N))) := inferInstance
  have hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ j) :=
    hPairδ_isIso _ _ j (homologyContractible (j + 1) (by omega))
      (homologyContractible j (by omega))
  have hrel : IsZero ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ).homology
      (j + 1)) :=
    relChains_vanishing_of_compact (M := TopCat.of (EuclideanSpace ℝ (Fin N))) hN A hAc
      (j + 1) (by omega)
  have hbij : Function.Bijective (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ j) :=
    ConcreteCategory.bijective_of_isIso _
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := hbij.2 a
  obtain ⟨b', hb'⟩ := hbij.2 b
  rw [← ha', ← hb']
  congr 1
  haveI : Subsingleton
      ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ).homology (j + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hrel
  exact Subsingleton.elim a' b'

/-! ## The top homology of a bounded open set -/

/-- **The top homology of an open set with compact closure vanishes.**
For an open `W ⊆ ℝ^N` with `closure W` compact, `H_N(W; ℤ) = 0`.

Put `A = closure W ∖ W`, so that `A` is compact and `ℝ^N ∖ A = W ⊔ (ℝ^N ∖ closure W)` is a
disjoint union of two open sets.  By the previous lemma `H_N(ℝ^N ∖ A) = 0`, and Mayer–Vietoris for
the (disjoint) open cover identifies `H_N(ℝ^N∖A)` with `H_N(W) ⊕ H_N(ℝ^N∖closure W)`; hence
`H_N(W) = 0`. -/
theorem isZero_homology_of_isCompact_closure_aux {N : ℕ} (hN : 1 ≤ N)
    (W : Set (EuclideanSpace ℝ (Fin N))) (hW : IsOpen W)
    (hcpt : IsCompact (closure W)) :
    IsZero ((singularChains ℤ (TopCat.of ↥W)).homology N) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  -- the compact set `A = closure W ∖ W`
  have hAc : IsCompact (closure W ∩ Wᶜ) := hcpt.inter_right hW.isClosed_compl
  have hset : (closure W ∩ Wᶜ)ᶜ = W ∪ (closure W)ᶜ := by
    rw [Set.compl_inter, compl_compl W, Set.union_comm]
  -- the complement of `A` has vanishing `H_{m+1}`
  have hA : IsZero ((singularChains ℤ (TopCat.of ↥((closure W ∩ Wᶜ)ᶜ))).homology (m + 1)) :=
    compl_homology_vanishing_of_compact_aux hN (closure W ∩ Wᶜ) hAc (m + 1) (by omega)
  haveI hsubA : Subsingleton
      ↥((singularChains ℤ (TopCat.of ↥((closure W ∩ Wᶜ)ᶜ))).homology (m + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hA
  have hX0 : IsZero ((singularChains ℤ (TopCat.of ↥(W ∪ (closure W)ᶜ))).homology (m + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (subsingleton_homology_of_set_eq hset (m + 1) hsubA)
  -- the two pieces of the disjoint open cover
  set U : Set ↥(TopCat.of ↥(W ∪ (closure W)ᶜ)) :=
    {x | (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ W} with hUdef
  set V : Set ↥(TopCat.of ↥(W ∪ (closure W)ᶜ)) :=
    {x | (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ (closure W)ᶜ} with hVdef
  have hUopen : IsOpen U := hW.preimage continuous_subtype_val
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  have hcov : U ∪ V = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact x.2
  have hdisj : U ∩ V = ∅ := by
    ext x
    constructor
    · rintro ⟨hxW, hxcl⟩
      exact absurd (subset_closure
        (show (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ W from hxW)) hxcl
    · intro hx
      exact absurd hx (Set.notMem_empty x)
  have hInterZ : ∀ k, IsZero ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homology k) := by
    intro k
    haveI : IsEmpty ↥(U ∩ V) := Set.isEmpty_coe_sort.mpr hdisj
    exact isZero_homology_of_isEmpty_aux (TopCat.of ↥(U ∩ V)) k
  -- Mayer–Vietoris identifies `H_{m+1}(U) ⊕ H_{m+1}(V)` with `H_{m+1}(X)`
  haveI hiso : IsIso (mvRightX U V hUopen hVopen hcov (m + 1)) :=
    isIso_mvRightX_of_isZero_inter_aux U V hUopen hVopen hcov m
      (hInterZ (m + 1)) (hInterZ m)
  have hbip : IsZero
      ((singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).homology
        (m + 1)) :=
    IsZero.of_iso hX0 (asIso (mvRightX U V hUopen hVopen hcov (m + 1)))
  have hUz : IsZero ((singularChains ℤ (TopCat.of U)).homology (m + 1)) :=
    isZero_homology_of_isZero_biprod_homology_aux (C := singularChains ℤ (TopCat.of U))
      (D := singularChains ℤ (TopCat.of V)) (m + 1) hbip
  -- `U` is canonically homeomorphic to `W`
  haveI hsubU : Subsingleton ↥((singularChains ℤ (TopCat.of U)).homology (m + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hUz
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (subsingleton_homology_of_homeomorph
      (homeomorphSubsetUnion (A := W) (B := (closure W)ᶜ)) (m + 1) hsubU)

/-! ## Exhaustion by an increasing union -/

/-- **Vanishing for an increasing union of open sets.**  If `U = ⋃ k, W k` with the `W k` open
and increasing, and the top homology of every `W k` vanishes, then that of `U` vanishes too: every
class of `H_N(U)` is the image of a class of some `H_N(W k)`. -/
theorem isZero_homology_of_iUnion_exhaustion_aux {N : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin N))) (W : ℕ → Set (EuclideanSpace ℝ (Fin N)))
    (hopen : ∀ k, IsOpen (W k)) (hmono : Monotone W) (hUnion : (⋃ k, W k) = U)
    (hWzero : ∀ k, IsZero ((singularChains ℤ (TopCat.of ↥(W k))).homology N)) :
    IsZero ((singularChains ℤ (TopCat.of ↥U)).homology N) := by
  have hsubUnion : Subsingleton
      ↥((singularChains ℤ (TopCat.of ↥(⋃ k, W k))).homology N) := by
    refine ⟨fun y₁ y₂ => ?_⟩
    obtain ⟨i, yi, hyi⟩ := pdHom_iUnion_lift (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W hopen hmono N y₂
    haveI : Subsingleton ↥((singularChains ℤ (TopCat.of ↥(W i))).homology N) :=
      ModuleCat.isZero_iff_subsingleton.mp (hWzero i)
    have hy2 : y₂ = 0 := by
      rw [← hyi, Subsingleton.elim yi 0]
      exact map_zero _
    obtain ⟨j, yj, hyj⟩ := pdHom_iUnion_lift (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W hopen hmono N y₁
    haveI : Subsingleton ↥((singularChains ℤ (TopCat.of ↥(W j))).homology N) :=
      ModuleCat.isZero_iff_subsingleton.mp (hWzero j)
    have hy1 : y₁ = 0 := by
      rw [← hyj, Subsingleton.elim yj 0]
      exact map_zero _
    rw [hy1, hy2]
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (subsingleton_homology_of_set_eq hUnion N hsubUnion)

/-! ## The main statement -/

theorem euclidean_top_homology_vanishing {N : ℕ} (hN : 1 ≤ N)
    (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥U)).homology N) := by
  refine isZero_homology_of_iUnion_exhaustion_aux U
    (fun k => U ∩ Metric.ball 0 ((k : ℝ) + 1)) ?_ ?_ ?_ ?_
  · intro k
    exact hU.inter Metric.isOpen_ball
  · intro k l hkl x hx
    refine ⟨hx.1, Metric.ball_subset_ball ?_ hx.2⟩
    have h : (k : ℝ) ≤ (l : ℝ) := Nat.cast_le.mpr hkl
    linarith
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      exact hxk.1
    · intro x hx
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      refine Set.mem_iUnion.mpr ⟨k, hx, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      linarith
  · intro k
    refine isZero_homology_of_isCompact_closure_aux hN _ (hU.inter Metric.isOpen_ball) ?_
    have hsub : closure (U ∩ Metric.ball 0 ((k : ℝ) + 1))
        ⊆ Metric.closedBall 0 ((k : ℝ) + 1) :=
      closure_minimal ((Set.inter_subset_right).trans Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) _).of_isClosed_subset
      isClosed_closure hsub

end

end Work.Cohomology
