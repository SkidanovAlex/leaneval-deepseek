import Mathlib
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

/-! ## The point-localised forms of `span_relCokerMap_eq_top` and `span_delta_eq_top`

`Work.Orient.Boundary.span_relCokerMap_eq_top` uses the hypothesis `IsRelFundClass W (n+1) ∂W w`
at exactly one point `x` of the half-ball piece (obtained from
`exists_mem_halfBallPiece_and_notMem_boundary`).  Here the point is *given* (it is `x₀`) and the
generator property is only assumed at that point. -/

/-- **The localisation over the interior part `P = K ∩ W°` of a coordinate half-ball at a boundary
point generates**, from the generator property at the *single* interior point `x₀ ∈ K`.

This is `Work.Orient.Boundary.span_relCokerMap_eq_top` with the hypothesis `IsRelFundClass` replaced
by the generator property at `x₀`; the proof is verbatim the same, with `x := x₀`. -/
theorem span_relCokerMap_eq_top_point
    (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ Work.Orient.Boundary.bdrySetW n W) (r : ℝ) (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.Boundary.halfBallK n W y r)
    (hx₀int : x₀ ∉ Work.Orient.Boundary.bdrySetW n W)
    (w : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1))
    (hgen : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int) (n + 1))) w)} :
      Set (Work.Orient.RelH W (n + 1) {x₀})) = ⊤) :
    Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bigB n W y r)
          (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1))) w)} :
      Set ((Work.Cohomology.relChains W (Work.Orient.Boundary.bigB n W y r)).homology (n + 1)))
      = ⊤ := by
  classical
  have hxnotB' : x₀ ∉ Work.Orient.Boundary.bigB n W y r := fun h => h ⟨hx₀, hx₀int⟩
  have hinc : Work.Orient.Boundary.bigB n W y r ⊆ (({x₀} : Set W))ᶜ :=
    fun _ hz hzx => hxnotB' (hzx ▸ hz)
  have hsing : ({x₀} : Set W) ⊆
      Work.Orient.Boundary.halfBallK n W y r ∩ (Work.Orient.Boundary.bdrySetW n W)ᶜ :=
    Set.singleton_subset_iff.mpr ⟨hx₀, hx₀int⟩
  have hLid : Work.Orient.resRelH W (n + 1) hsing
      = (HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := Work.Orient.Boundary.bigB n W y r)
            (B := (({x₀} : Set W))ᶜ) hinc)
          (n + 1)).hom := by
    have hmap : Work.Cohomology.relCokerMap W (Work.Orient.Boundary.bigB n W y r)
          (({x₀} : Set W))ᶜ
          (Set.compl_subset_compl.mpr hsing)
        = Work.Orient.relChainsIncl W (A := Work.Orient.Boundary.bigB n W y r)
            (B := (({x₀} : Set W))ᶜ) hinc :=
      (Work.Orient.Boundary.relChainsIncl_eq_relCokerMap W hinc).symm
    unfold Work.Orient.resRelH Work.ThomBordism.RelHmap
    rw [hmap]
  set ρm : Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W) ⟶
      Work.Cohomology.relChains W (Work.Orient.Boundary.bigB n W y r) :=
    Work.Cohomology.relCokerMap W (Work.Orient.Boundary.bdrySetW n W)
      (Work.Orient.Boundary.bigB n W y r)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) with hρm
  have hcomp : Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int
      = ρm ≫ Work.Orient.relChainsIncl W (A := Work.Orient.Boundary.bigB n W y r)
          (B := (({x₀} : Set W))ᶜ) hinc := by
    rw [hρm, Work.Orient.Boundary.relPunct_eq_relChainsIncl]
    rw [← Work.Orient.Boundary.relChainsIncl_comp (X := W)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) hinc]
    rw [Work.Orient.Boundary.relChainsIncl_eq_relCokerMap (X := W)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)]
  have hLρ : (Work.Orient.resRelH W (n + 1) hsing).comp
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1)))
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int) (n + 1)) := by
    rw [hLid, hcomp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  let Hloc : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1) →ₗ[ℤ]
      Work.Orient.RelH W (n + 1) {x₀} :=
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int) (n + 1))
  have hHloc : ∀ a, Hloc a = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int) (n + 1))) a :=
    fun _ => rfl
  have hLcomp : ∀ a, (Work.Orient.resRelH W (n + 1) hsing)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) a) = Hloc a := by
    intro a
    rw [hHloc]
    exact congrArg (fun (f : _ →ₗ[ℤ] _) => f a) hLρ
  have hLinj : Function.Injective (Work.Orient.resRelH W (n + 1) hsing) :=
    Work.Orient.Boundary.injective_localisation_of_halfBallInterior n W y hy r hr hgood x₀
      ⟨hx₀, hx₀int⟩
  have hmap : Submodule.map (Work.Orient.resRelH W (n + 1) hsing)
      (Submodule.span ℤ ({(ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) w} :
        Set _)) = ⊤ := by
    rw [Submodule.map_span, Set.image_singleton, hLcomp w, hHloc, hgen]
  refine Submodule.eq_top_iff'.mpr (fun v => ?_)
  have hv : (Work.Orient.resRelH W (n + 1) hsing) v
      ∈ Submodule.map (Work.Orient.resRelH W (n + 1) hsing)
        (Submodule.span ℤ ({(ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) w} :
          Set _)) := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨s, hs, hsv⟩ := Submodule.mem_map.mp hv
  exact (hLinj hsv).symm ▸ hs

/-- **`span{Δ_y w} = ⊤` from the generator property at a single interior point `x₀` of the
half-ball piece.**  The same assembly as `Work.Orient.Boundary.span_delta_eq_top`, with
`span_relCokerMap_eq_top_point` in place of `span_relCokerMap_eq_top`. -/
theorem span_delta_eq_top_point
    (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ Work.Orient.Boundary.bdrySetW n W) (r : ℝ) (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.Boundary.halfBallK n W y r)
    (hx₀int : x₀ ∉ Work.Orient.Boundary.bdrySetW n W)
    (w : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1))
    (hgen : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W (Work.Orient.Boundary.bdrySetW n W) x₀ hx₀int) (n + 1))) w)} :
      Set (Work.Orient.RelH W (n + 1) {x₀})) = ⊤) :
    Submodule.span ℤ ({(((Work.Cohomology.relChains_triple_shortExact W
        (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W)
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
        (by simp [ComplexShape.down])) w)} : Set _) = ⊤ := by
  classical
  have hspanρ : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bigB n W y r)
          (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1))) w)} : Set _) = ⊤ :=
    span_relCokerMap_eq_top_point n W y hy r hr hgood hx₀ hx₀int w hgen
  have hτ₃eq : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.Boundary.tripleMap W
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
        (Work.Orient.Boundary.bigA_sub_bigB n W y r)
        (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
        (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bigB n W y r)
          (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)) (n + 1))) := rfl
  have hspanτ : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Orient.Boundary.tripleMap W
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
          (Work.Orient.Boundary.bigA_sub_bigB n W y r)
          (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
          (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₃ (n + 1))) w)} :
      Set _) = ⊤ := by
    rw [hτ₃eq]
    exact hspanρ
  have hsq : ∀ a : (Work.Cohomology.relChains W
        (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1),
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
    have hnat := Work.Orient.Boundary.tripleMap_delta_naturality W
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
      (Work.Orient.Boundary.bigA_sub_bigB n W y r)
      (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r) n
    have h := congrArg (fun (φ : (Work.Cohomology.tripleShort W
          (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).X₃.homology (n + 1) ⟶
        (Work.Cohomology.tripleShort W (Work.Orient.Boundary.bigA n W y r)
          (Work.Orient.Boundary.bigB n W y r)
          (Work.Orient.Boundary.bigA_sub_bigB n W y r)).X₁.homology n) => φ a) hnat
    simpa only [ModuleCat.comp_apply] using h
  exact Work.Orient.Boundary.span_eq_top_of_surjective_injective
    (ModuleCat.Hom.hom ((Work.Cohomology.relChains_triple_shortExact W
      (Work.Orient.Boundary.bdryMinus n W y)
      (Work.Orient.Boundary.bdrySetW n W)
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
      (by simp [ComplexShape.down])))
    (ModuleCat.Hom.hom ((Work.Cohomology.relChains_triple_shortExact W
      (Work.Orient.Boundary.bigA n W y r)
      (Work.Orient.Boundary.bigB n W y r)
      (Work.Orient.Boundary.bigA_sub_bigB n W y r)).δ (n + 1) n
      (by simp [ComplexShape.down])))
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
      (Work.Orient.Boundary.bigA_sub_bigB n W y r)
      (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)))
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Orient.Boundary.tripleMap W
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)
      (Work.Orient.Boundary.bigA_sub_bigB n W y r)
      (Work.Orient.Boundary.bdryMinus_sub_bigA n W y r)
      (Work.Orient.Boundary.bdrySetW_sub_bigB n W y r)).τ₁ n))
    w hsq
    (Work.Orient.Boundary.tripleConnecting_input₁ n W y hy r hr hgood)
    (Work.Orient.Boundary.triple_δ_surjective_of_isZero n W y hy r hr hgood) hspanτ

/-- **The local class of the boundary class generates, under a chart-local generator hypothesis.**

This is `Work.Orient.Boundary.BoundaryOrientation` (Hatcher 3.43, second half) with the hypothesis
`IsRelFundClass W (n+1) ∂W w` weakened to a generator property at the *single* point `x₀`, which lies
in the half-ball piece around `y`.

Route: the existing proofs `Work.Orient.Boundary.span_relCokerMap_eq_top` and
`Work.Orient.Boundary.span_delta_eq_top` use `hw` at exactly *one* point `x` of `halfBallPiece`
(obtained from `exists_mem_halfBallPiece_and_notMem_boundary`); take that `x` to be `x₀` instead
(the hypotheses `hx₀ : x₀ ∈ halfBallPiece (n+1) W y r` and `hx₀int : x₀ ∉ boundary` are exactly what
the old `x` satisfied) and replace `hw x hxnotB` by the hypothesis `hgen`. Then copy the last step of
`Work.Orient.Boundary.BoundaryOrientation` (`hPairδ_comp_localization_eq_tripleδ`,
`diffCokerMap_localClass`, `span_eq_top_of_surjective`). Note `bdrySetW n W` is an abbrev for
`(modelWithCornersEuclideanHalfSpace (n+1)).boundary W` and `halfBallK n W y r` is an abbrev for
`Work.Orient.halfBallPiece (n+1) W y r`. -/
theorem boundarySign_span_locClass
    (n : ℕ) (hn : 1 ≤ n)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {r : ℝ} (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r)
    (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (hgen : Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          x₀ hx₀int) (n + 1)).hom w)) = ⊤) :
    Submodule.span ℤ (Set.singleton (Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩)) = ⊤ := by
  classical
  have hyB : y ∈ Work.Orient.Boundary.bdrySetW n W := hy
  have hspan : Submodule.span ℤ ({((ModuleCat.Hom.hom
      ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
        (Work.Orient.Boundary.bdrySetW n W)
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
        (by simp [ComplexShape.down]))) w)} : Set _) = ⊤ :=
    span_delta_eq_top_point n W y hyB r hr hgood hx₀ hx₀int w hgen
  have h1 : (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChainsSub W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y))) n)
        (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w)
      = ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w := by
    rw [← ModuleCat.comp_apply,
      Work.Orient.Boundary.hPairδ_comp_localization_eq_tripleδ n W y
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)]
    congr 1 <;> try rfl <;> exact Subsingleton.elim _ _
  have h2 := Work.Orient.Boundary.diffCokerMap_localClass W (Work.Orient.Boundary.bdrySetW n W) y
    hyB (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y) n
    (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w)
  rw [h1] at h2
  have hloc : Work.Orient.locClass (TopCat.of (Work.Orient.Boundary.bdrySetW n W)) n
        (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w)
        ⟨y, hyB⟩
      = (HomologicalComplex.homologyMap
          (Work.Orient.Boundary.diffCokerMap W (Work.Orient.Boundary.bdrySetW n W) y hyB
            (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n)
        (((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w) := by
    rw [h2]
    rfl
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Orient.Boundary.diffCokerMap W (Work.Orient.Boundary.bdrySetW n W) y hyB
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n) := by
    intro v
    refine ⟨(HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMapInv W
      (Work.Orient.Boundary.bdrySetW n W) y hyB
      (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n) v, ?_⟩
    have hcomp : HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMapInv W
          (Work.Orient.Boundary.bdrySetW n W) y hyB
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n
        ≫ HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMap W
          (Work.Orient.Boundary.bdrySetW n W) y hyB
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n = 𝟙 _ := by
      rw [← HomologicalComplex.homologyMap_comp,
        Work.Orient.Boundary.diffCokerMap_inv_hom, HomologicalComplex.homologyMap_id]
    rw [← ModuleCat.comp_apply, hcomp, ModuleCat.id_apply]
  rw [hloc]
  exact Work.Orient.Boundary.span_eq_top_of_surjective
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.Boundary.diffCokerMap W (Work.Orient.Boundary.bdrySetW n W) y hyB
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n)) hsurj hspan

end

end Work.ThomBordism
