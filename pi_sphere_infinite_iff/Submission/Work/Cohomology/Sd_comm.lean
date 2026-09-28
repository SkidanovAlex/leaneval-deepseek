import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.sdLC_boundary
import Submission.Work.Cohomology.toChain_boundaryLC
import Submission.Work.Cohomology.affineSimplex_map_target

/-!
# The subdivision of singular chains is a chain map

`Sd X n : C_n(X) ⟶ C_n(X)` (`Submission/Work/Cohomology/Subdivision.lean`) is the barycentric
subdivision of singular chains: on a generator `σ` (a singular `n`-simplex, i.e. a continuous map
`Δⁿ ⟶ X`) it pushes forward the subdivision `sdChain n` of the identity simplex of `Δⁿ` along `σ`.

This file proves the chain-map property

`Sd X n (∂ c) = ∂ (Sd X (n+1) c)`

which is what makes `Sd` a chain map, hence (`Sd ~ id` being the next step) a chain homotopy
equivalence — the input to the small-simplices / Mayer–Vietoris theorem.

## The proof

Everything is a transport of the *simplicial* identity of
`Submission/Work/Cohomology/sdLC_boundary.lean`,

`∂ (sdLC (n+1)) = ∑ᵢ (-1)ⁱ • embedLCᵢ (sdLC n)`  ("the boundary of the subdivided simplex is the
subdivided boundary"),

along the affine-chain ↦ singular-chain translation `toChain`:

* `toChain_embedLC` — `toChain` intertwines the face embeddings `embedLC` with the
  pushforward `chainComplexMap (toSSet.map (faceMap N i))` along the affine face map `Δ^N ⟶ Δ^{N+1}`
  (`faceMap`), which is the chain-level form of `(δᵢ)_*`;
* `chainComplexMap_comm_apply`, `chainComplexMap_ι_apply`, `chainComplexMap_toSSet_map_comp` —
  naturality of `chainComplexMap` (it is a chain map, and it is functorial);
* `faceMap_comp_sdMap` — the singular simplex of the `i`-th face of `σ` is `σ` composed with the
  affine face map, which is what makes the two sides match for an arbitrary space `X`.

The generator-level input is then `d_sdElem`:

`∂ (sdElem X (n+1) σ) = ∑ᵢ (-1)ⁱ • sdElem X n (δᵢ σ)`,

and `Sd_comm` follows because both sides are `ℤ`-linear in `c` and agree on the generators
`1 • σ` of the coproduct `C_{n+1}(X)`.

Note on formalisation: the chain modules `(singularChains ℤ X).X n` are coproducts
(`SSet.chainComplexXCofan`) whose inclusions `ιChainComplex` live in the equivalent but
syntactically different guise `(TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)`; the
auxiliary definition `gen` names the generator `1 • σ` in the `singularChains` guise so that all
element-level rewriting happens in a single representation.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section


/-- The `i`-th face map `Δ^n ⟶ Δ^{n+1}` of the standard simplices, as a continuous map. -/
def faceMap (n : ℕ) (i : Fin (n + 2)) : Delta n ⟶ Delta (n + 1) :=
  TopCat.ofHom ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

/-- A singular `n`-simplex of `X`, viewed as a continuous map `Δ^n ⟶ X` via
`TopCat.toSSetObjEquivT`. -/
def sdMap {X : TopCat} (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) : Delta n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquivT X (Opposite.op ⦋n⦌) σ)

/-- `sdElem` is the push-forward of the subdivided identity simplex `sdChain n` along the
singular simplex `σ` (this is the definition, recorded for rewriting). -/
lemma sdElem_eq (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    sdElem X n σ =
      ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap n σ)) (ModuleCat.of ℤ ℤ)).f n)
        (sdChain n) := rfl

/-- The singular simplex of the `i`-th face of `σ` is `σ` composed with the affine face map. -/
lemma faceMap_comp_sdMap (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    faceMap n i ≫ sdMap (n + 1) σ = sdMap n ((TopCat.toSSet.obj X).δ i σ) := by
  ext z
  change (TopCat.toSSetObjEquivT X (Opposite.op ⦋n + 1⦌) σ) (stdSimplex.map i.succAbove z)
      = (TopCat.toSSetObjEquivT X (Opposite.op ⦋n⦌) ((TopCat.toSSet.obj X).δ i σ)) z
  rw [TopCat.toSSetObjEquivT_δ_apply]

/-- Naturality of `TopCat.toSSetObjEquivT` in the space: precomposition with `g` corresponds to
composition of the underlying continuous maps with `g`. -/
lemma toSSetObjEquiv_map_apply {X Y : TopCat} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquivT Y n ((TopCat.toSSet.map f).app n x) z
      = f (TopCat.toSSetObjEquivT X n x z) := rfl

/-- The chain map induced by a simplicial map, on a generator `a • x`. -/
lemma chainComplexMap_ι_apply {X Y : SSet} (f : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) (a : ℤ) :
    (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom a)
      = (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) (f.app (Opposite.op ⦋n⦌) x)).hom a := by
  have h := SSet.ι_chainComplexMap_f X Y f (ModuleCat.of ℤ ℤ) x
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    g.hom a) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- `chainComplexMap` is a chain map: it commutes with the differential, on elements. -/
lemma chainComplexMap_comm_apply {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (x : (X.chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1)) :
    ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom
        (((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f (n + 1)) x)
      = ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n)
        (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom x) := by
  have h := HomologicalComplex.Hom.comm (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) (n + 1) n
  have h2 := congrArg (fun (g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1) ⟶
      (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) => g.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Functoriality of `chainComplexMap` for maps induced by maps of topological spaces, on
elements. -/
lemma chainComplexMap_toSSet_map_comp {A B C : TopCat} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ)
    (x : ((TopCat.toSSet.obj A).chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    ((SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℤ ℤ)).f n)
        (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n) x)
      = ((SSet.chainComplexMap (TopCat.toSSet.map (f ≫ g)) (ModuleCat.of ℤ ℤ)).f n) x := by
  have h2 : SSet.chainComplexMap (TopCat.toSSet.map (f ≫ g)) (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℤ ℤ) :=
    Functor.map_comp ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (TopCat.toSSet.map f) (TopCat.toSSet.map g)
  simp only [h2, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The image of a linear simplex under the push-forward along the affine face map. -/
lemma toSSet_map_faceMap_linSimplex (N k : ℕ) (i : Fin (N + 2))
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) :
    (TopCat.toSSet.map (faceMap N i)).app (Opposite.op ⦋k⦌) (linSimplex v)
      = linSimplex (fun j => stdSimplex.map (Fin.succAbove i) (v j)) := by
  apply (TopCat.toSSetObjEquivT (Delta (N + 1)) (Opposite.op ⦋k⦌)).injective
  ext z : 1
  rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_linSimplex, toSSetObjEquiv_linSimplex]
  exact affineSimplex_map_target (Fin.succAbove i) v z

/-- `toChain` intertwines the face embeddings `embedLC` with the push-forward of chains along the
affine face map. -/
lemma toChain_embedLC (N k : ℕ) (i : Fin (N + 2)) (c : LinChain N k) :
    toChain (N + 1) k (embedLC N k i c) =
      ((SSet.chainComplexMap (TopCat.toSSet.map (faceMap N i)) (ModuleCat.of ℤ ℤ)).f k)
        (toChain N k c) := by
  have key : (toChain (N + 1) k) ∘ₗ (embedLC N k i)
      = ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (faceMap N i))
          (ModuleCat.of ℤ ℤ)).f k) ∘ₗ (toChain N k) := by
    refine Finsupp.basisSingleOne.ext fun v => ?_
    simp only [LinearMap.comp_apply, Finsupp.coe_basisSingleOne]
    rw [embedLC_map_single, toChain_apply_single, toChain_apply_single]
    simp only [one_smul]
    rw [chainComplexMap_ι_apply, toSSet_map_faceMap_linSimplex]
  exact LinearMap.congr_fun key c

/-- The subdivision morphism on a generator: `sdHom X n` sends `1 • σ` to `sdElem X n σ`. -/
lemma sdHom_ι (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ sdHom X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (sdElem X n σ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The generator `1 • σ` of the singular chains of `X`, in the `singularChains` guise. -/
def gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) : (singularChains ℤ X).X n :=
  ModuleCat.Hom.hom ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) (1 : ℤ)

/-- `Sd` on a generator: `Sd X n (1 • σ) = sdElem X n σ`. -/
lemma Sd_gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    Sd X n (gen X n σ) = sdElem X n σ := by
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singularChains ℤ X).X n) =>
    g.hom (1 : ℤ)) (sdHom_ι X n σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul, Sd, gen] at h ⊢
  exact h

/-- The differential of a generator: `∂ (1 • σ) = ∑ᵢ (-1)ⁱ • (1 • δᵢ σ)`. -/
lemma d_gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    ((singularChains ℤ X).d (n + 1) n).hom (gen X (n + 1) σ)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          gen X n ((TopCat.toSSet.obj X).δ i σ) := by
  exact chainComplex_d_ι_apply ℤ (X := TopCat.toSSet.obj X) (n := n) σ

/-- `Sd` of the boundary of a generator. -/
lemma Sd_d_gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    Sd X n (((singularChains ℤ X).d (n + 1) n).hom (gen X (n + 1) σ))
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          sdElem X n ((TopCat.toSSet.obj X).δ i σ) := by
  rw [d_gen X n σ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Sd_gen]

/-- **The boundary of a subdivided simplex is the subdivided boundary**: the generator identity
underlying `Sd_comm`. -/
theorem d_sdElem (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    ((singularChains ℤ X).d (n + 1) n).hom (sdElem X (n + 1) σ)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          sdElem X n ((TopCat.toSSet.obj X).δ i σ) := by
  have hsd : ((TopCat.toSSet.obj (Delta (n + 1))).chainComplex (ModuleCat.of ℤ ℤ)).d
        (n + 1) n (sdChain (n + 1))
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((SSet.chainComplexMap (TopCat.toSSet.map (faceMap n i)) (ModuleCat.of ℤ ℤ)).f n)
            (sdChain n) := by
    rw [show sdChain (n + 1) = toChain (n + 1) (n + 1) (sdLC (n + 1)) from rfl,
      ← toChain_boundaryLC (n + 1) n (sdLC (n + 1)), sdLC_boundary n, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : toChain (n + 1) n (embedLC n n i (sdLC n))
        = ((SSet.chainComplexMap (TopCat.toSSet.map (faceMap n i)) (ModuleCat.of ℤ ℤ)).f n)
            (sdChain n) := by
      rw [toChain_embedLC, show sdChain n = toChain n n (sdLC n) from rfl]
    exact (map_zsmul (toChain (n + 1) n) ((-1 : ℤ) ^ (i : ℕ)) (embedLC n n i (sdLC n))).trans
      (congrArg (fun (z : ((TopCat.toSSet.obj (Delta (n + 1))).chainComplex
        (ModuleCat.of ℤ ℤ)).X n) => (((-1 : ℤ) ^ (i : ℕ)) : ℤ) • z) hi)
  have h1 : ((singularChains ℤ X).d (n + 1) n).hom (sdElem X (n + 1) σ)
      = ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (n + 1) σ)) (ModuleCat.of ℤ ℤ)).f n)
          (((TopCat.toSSet.obj (Delta (n + 1))).chainComplex (ModuleCat.of ℤ ℤ)).d
            (n + 1) n (sdChain (n + 1))) :=
    chainComplexMap_comm_apply _ n _
  have h2 : ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (n + 1) σ)) (ModuleCat.of ℤ ℤ)).f n)
          (((TopCat.toSSet.obj (Delta (n + 1))).chainComplex (ModuleCat.of ℤ ℤ)).d
            (n + 1) n (sdChain (n + 1)))
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          sdElem X n ((TopCat.toSSet.obj X).δ i σ) := by
    rw [hsd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (n + 1) σ)) (ModuleCat.of ℤ ℤ)).f n)
          (((SSet.chainComplexMap (TopCat.toSSet.map (faceMap n i)) (ModuleCat.of ℤ ℤ)).f n)
            (sdChain n))
        = sdElem X n ((TopCat.toSSet.obj X).δ i σ) := by
      rw [chainComplexMap_toSSet_map_comp, faceMap_comp_sdMap,
        ← sdElem_eq (n := n) X ((TopCat.toSSet.obj X).δ i σ)]
    rw [map_zsmul]
    exact congrArg (fun (z : (singularChains ℤ X).X n) => (((-1 : ℤ) ^ (i : ℕ)) : ℤ) • z) hi
  rw [h1, h2]

theorem Sd_comm (X : TopCat) (n : ℕ) (c : (singularChains ℤ X).X (n + 1)) :
    Sd X n (((singularChains ℤ X).d (n + 1) n).hom c) =
      (((singularChains ℤ X).d (n + 1) n).hom (Sd X (n + 1) c)) := by
  have hmain : ((singularChains ℤ X).d (n + 1) n) ≫ sdHom X n
      = sdHom X (n + 1) ≫ ((singularChains ℤ X).d (n + 1) n) := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show Sd X n (((singularChains ℤ X).d (n + 1) n).hom (gen X (n + 1) σ))
      = (((singularChains ℤ X).d (n + 1) n).hom (Sd X (n + 1) (gen X (n + 1) σ)))
    rw [Sd_gen X (n + 1) σ, Sd_d_gen X n σ, d_sdElem X n σ]
  have h := congrArg (fun (g : (singularChains ℤ X).X (n + 1) ⟶ (singularChains ℤ X).X n) =>
    g.hom c) hmain
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Sd] using h

end

end Work.Cohomology
