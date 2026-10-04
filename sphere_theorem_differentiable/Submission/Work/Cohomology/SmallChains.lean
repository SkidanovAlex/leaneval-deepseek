import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.Sd_comm

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Small simplices and the small-chains subcomplex

Let `X` be a topological space and `U`, `V ⊆ X` subsets covering `X`.  A singular simplex is
*small* if its image lies in `U` or in `V`, and the **small chains** `C^{U,V}_*(X)` are the chains
spanned by the small simplices.  They form a subcomplex of the singular chains — the faces of a
small simplex are small — and the small-simplices theorem says that the inclusion induces an
isomorphism on homology, which is what makes the Mayer–Vietoris sequence work.

The small simplices are realized here as a **subcomplex of the singular simplicial set**: the
predicate `IsSmall` is preserved by all the simplicial operations (faces, degeneracies, and more
generally by the restriction maps along maps of simplex categories, since those only shrink the
image of a simplex).  Consequently the small chain complex is *free* (it is the simplicial chain
complex of a simplicial set), which is what allows the Mayer–Vietoris cochain sequence to be
obtained by dualising.

## Main definitions

* `IsSmall U V σ` — the image of the singular simplex `σ` lies in `U` or in `V`;
* `smallSubcomplex U V` — the subcomplex of the singular simplicial set of `X` on the small
  simplices;
* `smallChains U V` — the small chain complex (with `ℤ` coefficients);
* `smallToSing U V` — the inclusion of the small chains into the singular chains of `X`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- A singular simplex is **small** for the pair `(U, V)` if its image is contained in `U` or in
`V` (this is the general form, indexed by an arbitrary simplex category object). -/
def IsSmall (U V : Set X) {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) : Prop :=
  Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) =>
      TopCat.toSSetObjEquivT X n σ z) ⊆ U ∨
    Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) =>
      TopCat.toSSetObjEquivT X n σ z) ⊆ V

/-- The `ℕ`-indexed form of `IsSmall`, in terms of the continuous map `sdMap`. -/
theorem isSmall_iff {U V : Set X} {k : ℕ} (σ : Simplex X k) :
    IsSmall U V σ ↔
      Set.range (fun z : (Delta k : TopCat) => sdMap k σ z) ⊆ U ∨
        Set.range (fun z : (Delta k : TopCat) => sdMap k σ z) ⊆ V :=
  Iff.rfl

/-- The face of a small simplex is small. -/
theorem IsSmall.face {U V : Set X} {n : ℕ} {σ : Simplex X (n + 1)} (h : IsSmall U V σ)
    (i : Fin (n + 2)) : IsSmall U V ((TopCat.toSSet.obj X).δ i σ) := by
  rw [isSmall_iff] at h ⊢
  have hsub : Set.range (fun z : (Delta n : TopCat) =>
        sdMap n ((TopCat.toSSet.obj X).δ i σ) z)
      ⊆ Set.range (fun z : (Delta (n + 1) : TopCat) => sdMap (n + 1) σ z) := by
    rintro y ⟨z, rfl⟩
    refine ⟨stdSimplex.map i.succAbove z, ?_⟩
    have h := congrArg (fun (f : Delta n ⟶ X) => f z) (faceMap_comp_sdMap X n σ i)
    first
      | (simpa [sdMap, faceMap] using h)
      | (simpa [sdMap, faceMap] using h.symm)
  exact h.imp (fun h1 => hsub.trans h1) (fun h2 => hsub.trans h2)

/-- The restriction of a simplicial map to the singular simplices shrinks the image, so it
preserves smallness. -/
theorem IsSmall.map {U V : Set X} {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    {σ : (TopCat.toSSet.obj X).obj n} (h : IsSmall U V σ) :
    IsSmall U V ((TopCat.toSSet.obj X).map i σ) := by
  have hsub : Set.range (fun z : stdSimplex ℝ (Fin (m.unop.len + 1)) =>
        TopCat.toSSetObjEquivT X m ((TopCat.toSSet.obj X).map i σ) z)
      ⊆ Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) =>
        TopCat.toSSetObjEquivT X n σ z) := by
    rintro y ⟨z, rfl⟩
    refine ⟨stdSimplex.map i.unop z, ?_⟩
    exact (TopCat.toSSetObjEquivT_naturality_apply i.unop σ z).symm
  exact h.imp (fun h1 => hsub.trans h1) (fun h2 => hsub.trans h2)

/-- **The subcomplex of small simplices** of the singular simplicial set of `X`. -/
def smallSubcomplex (U V : Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | IsSmall U V σ}
  map i := fun _ hx => IsSmall.map i hx

/-- The small simplicial set. -/
abbrev smallSSet (U V : Set X) : SSet := smallSubcomplex U V

/-- **The small chain complex**: the simplicial chains of the small simplices, with `ℤ`
coefficients. -/
abbrev smallChains (U V : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (smallSSet U V).chainComplex (ModuleCat.of ℤ ℤ)

/-- The inclusion of the small chains into the singular chains of `X`. -/
abbrev smallToSing (U V : Set X) : smallChains U V ⟶ singularChains ℤ X :=
  SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)

/-- The generator of the simplicial chains of an arbitrary simplicial set, indexed by a simplex
(this is `gen` for `SSet`s rather than topological spaces). -/
def genSSet (Y : SSet) (n : ℕ) (σ : Y _⦋n⦌) : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  ModuleCat.Hom.hom (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) (1 : ℤ)

/-- The submodule of small `n`-chains. -/
def smallChainSubmodule (U V : Set X) (n : ℕ) :
    Submodule ℤ ((singularChains ℤ X).X n) :=
  LinearMap.range (((smallToSing U V).f n).hom)

/-- A singular `n`-chain is **small** if it lies in the image of the small chain complex. -/
abbrev IsSmallChain (U V : Set X) {n : ℕ} (c : (singularChains ℤ X).X n) : Prop :=
  c ∈ smallChainSubmodule U V n

/-- A singular simplex that is small generates a small chain. -/
theorem isSmallChain_gen {U V : Set X} {n : ℕ} {σ : Simplex X n} (h : IsSmall U V σ) :
    IsSmallChain U V (gen X n σ) := by
  refine ⟨genSSet (smallSSet U V) n ⟨σ, h⟩, ?_⟩
  have h' := chainComplexMap_ι_apply (smallSubcomplex U V).ι n ⟨σ, h⟩ (1 : ℤ)
  rw [show (smallSubcomplex U V).ι.app (Opposite.op ⦋n⦌) ⟨σ, h⟩ = σ from rfl] at h'
  exact h'

theorem IsSmallChain.zero (U V : Set X) (n : ℕ) :
    IsSmallChain U V (0 : (singularChains ℤ X).X n) :=
  (smallChainSubmodule U V n).zero_mem

theorem IsSmallChain.add {U V : Set X} {n : ℕ} {c d : (singularChains ℤ X).X n}
    (hc : IsSmallChain U V c) (hd : IsSmallChain U V d) : IsSmallChain U V (c + d) :=
  (smallChainSubmodule U V n).add_mem hc hd

theorem IsSmallChain.neg {U V : Set X} {n : ℕ} {c : (singularChains ℤ X).X n}
    (hc : IsSmallChain U V c) : IsSmallChain U V (-c) :=
  (smallChainSubmodule U V n).neg_mem hc

theorem IsSmallChain.sub {U V : Set X} {n : ℕ} {c d : (singularChains ℤ X).X n}
    (hc : IsSmallChain U V c) (hd : IsSmallChain U V d) : IsSmallChain U V (c - d) :=
  (smallChainSubmodule U V n).sub_mem hc hd

theorem IsSmallChain.smul {U V : Set X} {n : ℕ} {c : (singularChains ℤ X).X n} (a : ℤ)
    (hc : IsSmallChain U V c) : IsSmallChain U V (a • c) := by
  obtain ⟨c', hc'⟩ := hc
  exact ⟨a • c', by rw [map_zsmul, hc']⟩

theorem IsSmallChain.sum {U V : Set X} {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (singularChains ℤ X).X n) (hf : ∀ i ∈ s, IsSmallChain U V (f i)) :
    IsSmallChain U V (∑ i ∈ s, f i) :=
  (smallChainSubmodule U V n).sum_mem fun i hi => hf i hi

end

end Work.Cohomology
