import Mathlib
import Submission.Work.ThomBordism.localBoundaryTransfer
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.RatHurewicz.hPair_delta_natural_map
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_map_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local boundary transfer: *congruence* form

`Work.ThomBordism.localBoundaryTransfer'` compares the boundary local class of a relative
fundamental class with a given class `ψ` through a map `Ψb : ∂W → ∂(stdHalfBall)` which is a local
homeomorphism at the point `y`.  The two *chart-level* hypotheses `hψ`, `hPair` of that lemma are
transports of the relevant local classes along `Ψb` into the **model**.

Here we prove the form needed by the source construction of the last mile, where the comparison is
made **directly between two manifolds `W` and `W'`** (a bordism and the model), without a detour
through a single model space: the transport along `Φb : ∂W → ∂W'` of the boundary local class of
`w ∈ H_{m+1}(W,B)` equals the boundary local class of `w' ∈ H_{m+1}(W',B')`, and the two punctured
local classes of `w`, `w'` at `x₀`, `Φ x₀` correspond under `Φ`.

The mathematical content is the naturality of the map
`c ↦ locClass ((hPairδ …).hom c) y` under a map of pairs `(Φ, Φb)` (the connecting homomorphism of
a pair is natural and the local classes are natural), together with the *local* injectivity of the
transport along `Φb` (`Work.ThomBordism.relHmapOf_injective_of_localHomeo`, from the local
homeomorphism data on the open set `N`).

## Main results

* `Work.ThomBordism.relChainsMapOf_relPunct_aux` — the naturality square of `relPunct`;
* `Work.ThomBordism.locClass_hPairDelta_natural_aux` — naturality of `locClass ∘ hPairδ`;
* `Work.ThomBordism.localBoundaryTransfer_congr` — the target.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-! ## The naturality of the punctured localisation -/

/-- **The naturality square of the punctured localisation.**

For a map of pairs `(f, g) : (X, A) → (Y, B)` (i.e. `f` maps `A` into `B`, so that
`relChainsMapOf X Y A B f g _` is defined) with `x ∉ A`, `f x ∉ B`, and `f` injective at `x`
(`z ≠ x → f z ≠ f x`), the punctured localisation commutes with `f`:

`(X, A) --f--> (Y, B)`,  `(X, X∖{x}) --f--> (Y, Y∖{f x})`.

Both composites are morphisms of relative chain complexes with the *same* first component, and a
`relChainsMapOf` is determined by its first component
(`Work.RatHurewicz.Cofibre.relChainsMapOf_eq_of_eq`). -/
theorem relChainsMapOf_relPunct_aux {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of ↥A ⟶ TopCat.of ↥B)
    (hw : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl Y B))
    {x : X} (hx : x ∉ A) (hxB : f x ∉ B) (hinj : ∀ z : X, z ≠ x → f z ≠ f x) :
    CategoryTheory.CategoryStruct.comp (Work.Cohomology.relChainsMapOf X Y A B f g hw)
        (Work.Orient.relPunct Y B (f x) hxB)
      = CategoryTheory.CategoryStruct.comp (Work.Orient.relPunct X A x hx)
          (Work.Cohomology.relChainsMapOf X Y {z : X | z ≠ x} {z : Y | z ≠ f x} f
            (Work.Cohomology.relMapSub {z : X | z ≠ x} {z : Y | z ≠ f x} f (fun z hz => hinj z hz))
            (Work.Cohomology.relMapSub_spec {z : X | z ≠ x} {z : Y | z ≠ f x} f
              (fun z hz => hinj z hz))) := by
  dsimp only [Work.Orient.relPunct, Work.Orient.relChainsIncl]
  rw [Work.RatHurewicz.Cofibre.relChainsMapOf_comp',
      Work.RatHurewicz.Cofibre.relChainsMapOf_comp']
  exact Work.RatHurewicz.Cofibre.relChainsMapOf_eq_of_eq A {z : Y | z ≠ f x}
    (f₁ := f ≫ 𝟙 Y) (f₂ := 𝟙 X ≫ f) (by simp) _ _

/-- **Naturality of the boundary local class under a map of pairs.**

A map of pairs `(f, fb) : (X, A) → (Y, A')` carries the local class at `⟨y, hy⟩` of the connecting
homomorphism `hPairδ X A n` of `w` to the local class at `fb ⟨y, hy⟩` of `hPairδ Y A' n` of the
image of `w` in `H_{n+1}(Y, A')`.  The two ingredients are the naturality of `hPairδ`
(`Work.RatHurewicz.hPair_delta_natural_map`) and the naturality of the local classes
(`Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair`). -/
theorem locClass_hPairDelta_natural_aux {X Y : TopCat} (A : Set X) (A' : Set Y) (f : X ⟶ Y)
    (fb : TopCat.of ↥A ⟶ TopCat.of ↥A')
    (hw : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp fb (Work.Cohomology.subtypeIncl Y A'))
    {y : X} (hy : y ∈ A)
    (hinj : ∀ z : ↥A, z ∉ ({⟨y, hy⟩} : Set ↥A) → fb z ∉ ({fb ⟨y, hy⟩} : Set ↥A'))
    (n : ℕ) (w : (Work.Cohomology.relChains X A).homology (n + 1)) :
    Work.PTGeometric.HOF.RelHmapOf n fb ({⟨y, hy⟩} : Set ↥A) ({fb ⟨y, hy⟩} : Set ↥A') hinj
        (Work.Orient.locClass (TopCat.of ↥A) n ((Work.Cohomology.hPairδ X A n).hom w) ⟨y, hy⟩)
      = Work.Orient.locClass (TopCat.of ↥A') n
          ((Work.Cohomology.hPairδ Y A' n).hom
            ((HomologicalComplex.homologyMap
              (Work.Cohomology.relChainsMapOf X Y A A' f fb hw) (n + 1)).hom w))
          (fb ⟨y, hy⟩) := by
  have hnatδ : (Work.Cohomology.hPairδ Y A' n).hom
      ((HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A A' f fb hw) (n+1)).hom w)
      = (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥A') fb) n).hom
          ((Work.Cohomology.hPairδ X A n).hom w) := by
    have := congrArg (fun (φ : (Work.Cohomology.relChains X A).homology (n+1) ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of ↥A')).homology n) => φ.hom w)
      (Work.RatHurewicz.hPair_delta_natural_map A A' f fb hw n)
    simpa using this
  rw [hnatδ]
  exact Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair (n := n) fb
    (K := ({⟨y, hy⟩} : Set ↥A)) (K' := ({fb ⟨y, hy⟩} : Set ↥A'))
    (Work.Cohomology.relMapSub ({⟨y, hy⟩} : Set ↥A)ᶜ ({fb ⟨y, hy⟩} : Set ↥A')ᶜ fb hinj)
    (Work.Cohomology.relMapSub_spec _ _ fb hinj)
    ((Work.Cohomology.hPairδ X A n).hom w)

/-- **The local boundary-sign transfer, in congruence form.**

The transport along `Φb` of the boundary local class of `w` at `y` equals the boundary local class
of `w'` at `Φb ⟨y, hy⟩`, *provided* the punctured localisations of `w` and `w'` at `x₀` and
`Φ x₀` correspond under `Φ` and the transport along `Φb` at `y` is injective (which the local
homeomorphism data `N`, `ginv` supplies).

The conclusion is the pointwise identity `locClass (hPairδ w) y = c • locClass ψ y`. -/
theorem localBoundaryTransfer_congr (m : ℕ) (hm : 1 ≤ m)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 W]
    {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary W = B)
    {y : W} (hy : y ∈ B)
    (W' : TopCat) [CompactSpace W'] [T2Space W']
    [ChartedSpace (EuclideanHalfSpace (m + 1)) W']
    [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 W']
    {B' : Set W'} (hB' : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary W' = B')
    {y' : W'} (hy' : y' ∈ B')
    (Φ : W ⟶ W') (Φb : TopCat.of ↥B ⟶ TopCat.of ↥B')
    (hΦb : ∀ z : ↥B, (Φb z : W') = Φ z.1)
    (hyy : Φb ⟨y, hy⟩ = ⟨y', hy'⟩)
    (hfB : ∀ x : ↥B, x ∉ ({⟨y, hy⟩} : Set ↥B) → Φb x ∉ ({Φb ⟨y, hy⟩} : Set ↥B'))
    (hcl : IsClosed ({Φb ⟨y, hy⟩} : Set ↥B'))
    (N : Set ↥B) (hN : IsOpen N) (hyN : ⟨y, hy⟩ ∈ N) (hIm : IsOpen (Φb '' N))
    (ginv : ↥(Φb '' N) → ↥N) (hgcont : Continuous ginv)
    (hgf : ∀ z : ↥N, ginv ⟨(Φb z.1 : ↥B'), ⟨z.1, z.2, rfl⟩⟩ = z)
    (hfg : ∀ w : ↥(Φb '' N), (Φb (ginv w).1 : ↥B') = w.1)
    {r : ℝ} (hr : 0 < r) (hgood : Work.Orient.halfBallGood (m + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (m + 1) W y r) (hx₀int : x₀ ∉ B)
    (hΦinj : ∀ z : W, Φ z = Φ x₀ → z = x₀)
    {r' : ℝ} (hr' : 0 < r') (hgood' : Work.Orient.halfBallGood (m + 1) W' y' r')
    (hx₀' : Φ x₀ ∈ Work.Orient.halfBallPiece (m + 1) W' y' r')
    (hx₀'int : Φ x₀ ∉ B')
    (w : (Work.Cohomology.relChains W B).homology (m + 1))
    (ψ : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B)).homology m)
    (w' : (Work.Cohomology.relChains W' B').homology (m + 1))
    (ψ' : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B')).homology m)
    (hγ : Work.PTGeometric.HOF.RelHmapOf (m + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
        (fun z hz hzx => hz (hΦinj z hzx))
        ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (m + 1)).hom w)
      = (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀'int) (m + 1)).hom w')
    (c : ℤ) (hc : c = 1 ∨ c = -1)
    (hPair' : Work.Orient.locClass (TopCat.of ↥B') m
        ((Work.Cohomology.hPairδ W' B' m).hom w') ⟨y', hy'⟩
      = c • Work.Orient.locClass (TopCat.of ↥B') m ψ' ⟨y', hy'⟩)
    (hψ : Work.PTGeometric.HOF.RelHmapOf m Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hfB
        (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)
      = Work.Orient.locClass (TopCat.of ↥B') m ψ' (Φb ⟨y, hy⟩)) :
    Work.Orient.locClass (TopCat.of ↥B) m
        ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩
      = c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩ := by
  classical
  -- the compatibility of the pair map `(Φ, Φb)`
  have hw : Work.Cohomology.subtypeIncl W B ≫ Φ = Φb ≫ Work.Cohomology.subtypeIncl W' B' := by
    apply TopCat.ext
    intro z
    exact (hΦb z).symm
  -- the transported relative fundamental class
  let wtilde : (Work.Cohomology.relChains W' B').homology (m + 1) :=
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw) (m + 1)).hom w
  -- the punctured localisations of `wtilde` and `w'` at `Φ x₀` agree
  have hPunct : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀'int)
        (m + 1)).hom wtilde
      = (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀'int) (m + 1)).hom w' := by
    have hsq := relChainsMapOf_relPunct_aux B B' Φ Φb hw hx₀int hx₀'int
      (fun z hz hzx => hz (hΦinj z hzx))
    have h2 : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀'int) (m + 1)).hom
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw) (m + 1)).hom w)
        = (HomologicalComplex.homologyMap
            ((Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw)
              ≫ (Work.Orient.relPunct W' B' (Φ x₀) hx₀'int)) (m + 1)).hom w := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    rw [h2, hsq, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
    exact hγ
  -- hence the boundary local classes of `hPairδ wtilde` and `hPairδ w'` agree at `y'`
  have hloc := Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq (n := m) W' hB' hy' hr' hgood'
    hx₀' hx₀'int hPunct
  -- naturality of the local class of `hPairδ` under the map of pairs `(Φ, Φb)`
  have hnat := locClass_hPairDelta_natural_aux (A := B) (A' := B') Φ Φb hw hy hfB m w
  -- transport the two consequences to the point `Φb ⟨y, hy⟩`
  have hloc' : Work.Orient.locClass (TopCat.of ↥B') m
        ((Work.Cohomology.hPairδ W' B' m).hom wtilde) (Φb ⟨y, hy⟩)
      = Work.Orient.locClass (TopCat.of ↥B') m
        ((Work.Cohomology.hPairδ W' B' m).hom w') (Φb ⟨y, hy⟩) :=
    hyy.symm ▸ hloc
  have hPair'' : Work.Orient.locClass (TopCat.of ↥B') m
        ((Work.Cohomology.hPairδ W' B' m).hom w') (Φb ⟨y, hy⟩)
      = c • Work.Orient.locClass (TopCat.of ↥B') m ψ' (Φb ⟨y, hy⟩) :=
    hyy.symm ▸ hPair'
  -- the key identity: the transport of the two sides of the claim agree
  have key : Work.PTGeometric.HOF.RelHmapOf m Φb ({⟨y, hy⟩} : Set ↥B) ({Φb ⟨y, hy⟩} : Set ↥B') hfB
        (Work.Orient.locClass (TopCat.of ↥B) m ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
      = Work.PTGeometric.HOF.RelHmapOf m Φb ({⟨y, hy⟩} : Set ↥B) ({Φb ⟨y, hy⟩} : Set ↥B') hfB
        (c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) := by
    rw [hnat, hloc', hPair'', ← hψ]
    exact (map_zsmul (f := Work.PTGeometric.HOF.RelHmapOf m Φb ({⟨y, hy⟩} : Set ↥B)
      ({Φb ⟨y, hy⟩} : Set ↥B') hfB) c (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)).symm
  -- the transport at `y` is injective
  exact (Work.ThomBordism.relHmapOf_injective_of_localHomeo (n := m) Φb hN hyN hIm hcl ginv hgcont
    hgf hfg hfB) key

end

end Work.ThomBordism
