import Mathlib
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The half-ball localisation determines the local class of `hPairδ`

For a compact `C^1` manifold `W` with boundary `B = ∂W`, a boundary point `y ∈ B` and a coordinate
half-ball `K = halfBallPiece (n+1) W y r` around it, the local class at `y` of the boundary map
`hPairδ W B n w ∈ H_n(B)` of a relative class `w ∈ H_{n+1}(W,B)` depends on `w` only through its
image in `H_{n+1}(W, B ∪ Kᶜ)`.

## The route

Write `B' := B ∪ Kᶜ = bigB n W y r` (the complement of the interior part `P = K ∩ W°` of the
half-ball) and `A' := B' ∖ {y} = bigA n W y r`.

* `hPairδ_comp_localization_eq_tripleδ` and `diffCokerMap` (in
  `Submission/Work/Orient/Boundary/BoundaryOrientation.lean`) identify the localisation of
  `hPairδ W B n w` at `y` with the image under the isomorphism `diffCokerMap` of the connecting map
  `Δ = δ` of the triple `B∖{y} ⊆ B ⊆ W` (`locClass_hPairDelta_eq_tripleDelta`).
* `tripleMap_delta_naturality` (in `Orient/Boundary/TripleSetup.lean`) gives the naturality square
  `τ₁ ∘ Δ = δ_{(A',B')} ∘ τ₃` for the map of triples `(B∖{y} ⊆ B) → (A' ⊆ B')`, where `τ₃` is the
  map `H_{n+1}(W,B) → H_{n+1}(W,B')` of the hypothesis.
* `tripleConnecting_input₁` (excision: `B` and `B'` agree near `y`) says that `τ₁` is injective.

Hence `Δ w = Δ w'` as soon as `τ₃ w = τ₃ w'`, and the hypothesis of the theorem gives exactly that:
the excluded set `B ∪ Kᶜ` of the hypothesis is `bigB n W y r`, and the two maps agree by
functoriality of `relChainsIncl` (`relChainsIncl_comp`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open scoped CategoryTheory

theorem halfBallLocalisation_hPairDelta_eq {n : ℕ}
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W = B)
    {y : W} (hy : y ∈ B) {r : ℝ} (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {w w' : (Work.Cohomology.relChains W B).homology (n + 1)}
    (h : (HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl W (A := B)
          (B := B ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ) (fun z hz => Or.inl hz)) (n + 1)).hom w
       = (HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl W (A := B)
          (B := B ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ) (fun z hz => Or.inl hz)) (n + 1)).hom w') :
    Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w) ⟨y, hy⟩
      = Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w') ⟨y, hy⟩ := by
  subst hB
  -- the excision input: the comparison of the local groups is injective
  have hInj := Work.Orient.Boundary.tripleConnecting_input₁ n W y hy r hr hgood
  -- the excluded set `B' = B ∪ Kᶜ` of the hypothesis is `bigB n W y r`, up to the explicit
  -- inclusions `B ⊆ B' ⊆ B'` and `B ⊆ B'`
  have h₁ : Work.Orient.Boundary.bdrySetW n W ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ
      ⊆ Work.Orient.Boundary.bigB n W y r := by
    intro z hz
    rcases hz with hz | hz
    · exact Work.Orient.Boundary.bdrySetW_sub_bigB n W y r hz
    · exact fun hcon => hz hcon.1
  have hinc : Work.Orient.Boundary.bdrySetW n W
      ⊆ Work.Orient.Boundary.bdrySetW n W ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ :=
    fun z hz => Or.inl hz
  have hcomp : (Work.Orient.relChainsIncl W hinc)
      ≫ (Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ)
        (B := Work.Orient.Boundary.bigB n W y r) h₁)
      = Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W)
        (B := Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) :=
    (Work.Orient.Boundary.relChainsIncl_comp hinc h₁).trans
      (Work.Orient.Boundary.relChainsIncl_congr_h _ _)
  have hmap : HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W)
        (B := Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1)
      = HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hinc) (n + 1)
        ≫ HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
            (A := Work.Orient.Boundary.bdrySetW n W ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ)
            (B := Work.Orient.Boundary.bigB n W y r) h₁) (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp]
  -- the hypothesis, in the form of the `B'`-excluded set of the triple machinery
  have hbigstep : (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W)
        (B := Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1)) w
      = (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W)
        (B := Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1)) w' := by
    rw [hmap]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    exact congrArg (fun x => (HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W
      (A := Work.Orient.Boundary.bdrySetW n W ∪ (Work.Orient.halfBallPiece (n + 1) W y r)ᶜ)
      (B := Work.Orient.Boundary.bigB n W y r) h₁) (n + 1)) x) h
  -- `τ₃` of the map of triples is `relChainsIncl` on `B'`
  have hτ : (Work.Orient.Boundary.tripleMap W
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
        (Work.Orient.Boundary.bigA_sub_bigB n W y r)
        (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₃
      = Work.Orient.relChainsIncl W
        (A := Work.Orient.Boundary.bdrySetW n W)
        (B := Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) := by
    rw [Work.Orient.Boundary.relChainsIncl_eq_relCokerMap]
    rfl
  -- the naturality square of the connecting map of the two triples
  have hsquare : ∀ a : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1),
      (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
          (Work.Orient.Boundary.bigA_sub_bigB n W y r)
          (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
          (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₁ n)
        (((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
            (Work.Orient.Boundary.bdrySetW n W)
            (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
              (by simp [ComplexShape.down])) a)
      = ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bigA n W y r)
            (Work.Orient.Boundary.bigB n W y r)
            (Work.Orient.Boundary.bigA_sub_bigB n W y r)).δ (n + 1) n
              (by simp [ComplexShape.down]))
          ((HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W
              (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
              (Work.Orient.Boundary.bigA_sub_bigB n W y r)
              (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
              (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)) a) := by
    intro a
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun φ => φ a) (Work.Orient.Boundary.tripleMap_delta_naturality W
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
        (Work.Orient.Boundary.bigA_sub_bigB n W y r)
        (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) n)
  -- the connecting maps of the two triples agree on `w` and `w'`
  have hΔ : ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W)
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w
      = ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W)
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w' := by
    refine hInj ?_
    rw [hsquare w, hsquare w', hτ]
    exact congrArg (fun x => ((Work.Cohomology.relChains_triple_shortExact W
        (Work.Orient.Boundary.bigA n W y r)
        (Work.Orient.Boundary.bigB n W y r)
        (Work.Orient.Boundary.bigA_sub_bigB n W y r)).δ (n + 1) n
          (by simp [ComplexShape.down])) x) hbigstep
  rw [locClass_hPairDelta_eq_tripleDelta n W w y hy,
      locClass_hPairDelta_eq_tripleDelta n W w' y hy, hΔ]

end Work.ThomBordism
