import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.capRelAux

/-!
# Compactly supported cohomology as a direct limit over compact subsets

For a space `M` and a subset `W ⊆ M`, the compactly supported cohomology
`H^k_c(W) = colim_{K ⊆ W compact} H^k(W, W∖K)` is the direct limit of the relative cohomology
groups `H^k(W, W∖K)` over the compact subsets `K` of `W`, ordered by inclusion, with transition
maps the *enlargements* `pdRelComplexEnlarge W h` (for `K ⊆ K'`, a cochain vanishing on
`W∖K`-chains also vanishes on the smaller set `W∖K'`).

This file sets up that directed system (`pdCIdx`, `pdCLimMod`, `pdCLimMap`) and the direct limit
`pdCColim`, together with the map `pdCColimToHom` to `H_m(W)` given by the cap product with the
local fundamental class (the compatibility of the `goodD`'s with the transition maps is
`pd_goodD_natural`).

The two facts the five-lemma argument for the gluing needs are

* `pdCColim_eq_zero_iff` — the explicit criterion for vanishing in the direct limit: an element of
  a component maps to `0` precisely when some transition map kills it;
* `pdCColimToHom` — the duality map `D_W : H^k_c(W) → H_m(W)`, `x ↦ x ⌢ μ_W`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The index type of the direct system defining `H^k_c(W)`: the compact subsets of `W`. -/
def pdCIdx (M : TopCat) (W : Set M) : Type _ := {K : Set M // K ⊆ W ∧ IsCompact K}

instance pdCIdxPreorder (M : TopCat) (W : Set M) : Preorder (pdCIdx M W) where
  le i j := i.1 ⊆ j.1
  le_refl i := Set.Subset.rfl
  le_trans i j k hij hjk := hij.trans hjk

instance pdCIdxNonempty (M : TopCat) (W : Set M) : Nonempty (pdCIdx M W) :=
  ⟨⟨∅, Set.empty_subset W, isCompact_empty⟩⟩

instance pdCIdxDirected (M : TopCat) (W : Set M) : IsDirectedOrder (pdCIdx M W) where
  directed i j :=
    ⟨⟨i.1 ∪ j.1, Set.union_subset i.2.1 j.2.1, i.2.2.union j.2.2⟩,
      Set.subset_union_left, Set.subset_union_right⟩

/-- The degree-`k` piece attached to a compact set: `H^k(W, W∖K)`. -/
def pdCLimMod (M : TopCat) (W : Set M) (k : ℕ) (i : pdCIdx M W) : ModuleCat ℤ :=
  (relComplex ℤ (TopCat.of W) (pdRelSub W i.1)).homology k

/-- The transition map of the direct system: for `K ⊆ K'`, the enlargement map
`H^k(W, W∖K) → H^k(W, W∖K')`. -/
def pdCLimMap (M : TopCat) (W : Set M) (k : ℕ) {i j : pdCIdx M W} (h : i ≤ j) :
    (pdCLimMod M W k i) →ₗ[ℤ] (pdCLimMod M W k j) :=
  (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h) k).hom

/-- The enlargement map is the identity when the compact set is unchanged. -/
theorem pdRelComplexEnlarge_self' {M : TopCat} (W : Set M) {K : Set M} (h : K ⊆ K) :
    pdRelComplexEnlarge W h = 𝟙 (relComplex ℤ (TopCat.of W) (pdRelSub W K)) := by
  rw [pdRelComplexEnlarge]
  exact capRel_relComplexMap_id (R := ℤ) (X := TopCat.of W) (pdRelSub W K) (pdRelSub_mono h)

/-- The enlargement maps are compatible with composition. -/
theorem pdRelComplexEnlarge_comp {M : TopCat} (W : Set M) {K K' K'' : Set M}
    (h : K ⊆ K') (h' : K' ⊆ K'') :
    pdRelComplexEnlarge W h ≫ pdRelComplexEnlarge W h'
      = pdRelComplexEnlarge W (h.trans h') := by
  have hc := capRel_relComplexMap_comp (R := ℤ) (X₀ := TopCat.of W) (X₁ := TopCat.of W)
    (X₂ := TopCat.of W) (pdRelSub W K'') (pdRelSub W K') (pdRelSub W K)
    (𝟙 (TopCat.of W)) (𝟙 (TopCat.of W)) (pdRelSub_mono h') (pdRelSub_mono h)
  simp only [pdRelComplexEnlarge, Category.id_comp] at hc ⊢
  exact hc.symm

/-- The transition maps are compatible with the identities. -/
theorem pdCLimMap_self (M : TopCat) (W : Set M) (k : ℕ) (i : pdCIdx M W) :
    pdCLimMap M W k (le_refl i) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  show (HomologicalComplex.homologyMap (pdRelComplexEnlarge W (le_refl i)) k).hom x = x
  rw [pdRelComplexEnlarge_self' W (le_refl i), HomologicalComplex.homologyMap_id]
  rfl

/-- The transition maps are compatible with composition. -/
theorem pdCLimMap_comp (M : TopCat) (W : Set M) (k : ℕ) {i j l : pdCIdx M W}
    (hij : i ≤ j) (hjl : j ≤ l) :
    pdCLimMap M W k hjl ∘ₗ pdCLimMap M W k hij = pdCLimMap M W k (hij.trans hjl) := by
  apply LinearMap.ext
  intro x
  have hcomp : HomologicalComplex.homologyMap (pdRelComplexEnlarge W hij) k
        ≫ HomologicalComplex.homologyMap (pdRelComplexEnlarge W hjl) k
      = HomologicalComplex.homologyMap (pdRelComplexEnlarge W (hij.trans hjl)) k := by
    rw [← HomologicalComplex.homologyMap_comp, pdRelComplexEnlarge_comp W hij hjl]
  have h := congrArg
    (fun (f : (relComplex ℤ (TopCat.of W) (pdRelSub W i.1)).homology k
        ⟶ (relComplex ℤ (TopCat.of W) (pdRelSub W l.1)).homology k) => f.hom x) hcomp
  show (HomologicalComplex.homologyMap (pdRelComplexEnlarge W hjl) k).hom
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge W hij) k).hom x)
    = (HomologicalComplex.homologyMap (pdRelComplexEnlarge W (hij.trans hjl)) k).hom x
  exact h

/-- The transition maps, as additive homomorphisms (the form in which the direct limit is taken;
this keeps the `ℤ`-module structure on the colimit the canonical one coming from the abelian group
structure). -/
def pdCLimMapAdd (M : TopCat) (W : Set M) (k : ℕ) {i j : pdCIdx M W} (h : i ≤ j) :
    (pdCLimMod M W k i) →+ (pdCLimMod M W k j) :=
  (pdCLimMap M W k h).toAddMonoidHom

/-- The transition maps form a directed system. -/
instance pdCLimDirectedSystem (M : TopCat) (W : Set M) (k : ℕ) :
    DirectedSystem (fun i : pdCIdx M W => ↥(pdCLimMod M W k i))
      (fun i j h => pdCLimMapAdd M W k h) where
  map_self := by
    intro i x
    have h := LinearMap.congr_fun (pdCLimMap_self M W k i) x
    simpa [pdCLimMapAdd] using h
  map_map := by
    intro a b c hij hjk x
    have h := LinearMap.congr_fun (pdCLimMap_comp M W k hij hjk) x
    simpa [pdCLimMapAdd] using h

/-- **The compactly supported cohomology** `H^k_c(W)` of `W`, as the direct limit of the relative
groups `H^k(W, W∖K)` over the compact subsets `K ⊆ W`. -/
abbrev pdCColim (M : TopCat) (W : Set M) (k : ℕ) : Type _ :=
  DirectLimit (F := fun i : pdCIdx M W => ↥(pdCLimMod M W k i))
    (T := fun i j h => ↥(pdCLimMod M W k i) →+ ↥(pdCLimMod M W k j))
    (f := fun i j h => pdCLimMapAdd M W k h)

instance pdCColimAddCommGroup (M : TopCat) (W : Set M) (k : ℕ) :
    AddCommGroup (pdCColim M W k) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass

instance pdCColimModule (M : TopCat) (W : Set M) (k : ℕ) :
    Module ℤ (pdCColim M W k) :=
  AddCommGroup.toIntModule _

/-- The canonical map from a component to the direct limit. -/
def pdCColimOf (M : TopCat) (W : Set M) (k : ℕ) (i : pdCIdx M W) :
    (pdCLimMod M W k i) →+ (pdCColim M W k) where
  toFun x := (⟦⟨i, x⟩⟧ : pdCColim M W k)
  map_zero' := (DirectLimit.zero_def i).symm
  map_add' := fun x y => by rw [DirectLimit.add_def]

end

end Work.Cohomology
