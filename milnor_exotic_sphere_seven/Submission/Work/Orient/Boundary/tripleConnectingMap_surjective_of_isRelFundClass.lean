import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Orient.Boundary.injective_localisation_of_halfBallInterior
import Submission.Work.Orient.Boundary.isZero_punctured_halfBall_of_model
import Submission.Work.Orient.Boundary.halfBallInteriorUnionPoint
import Submission.Work.Orient.Boundary.tripleMapTau1Injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The connecting map of the triple `(∂W∖{y}, ∂W, W)` is onto

`Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass`: for a compact
`C^1` manifold `W` with boundary `∂W` (modelled on the half-space `𝓡∂ (n+1)`), a point
`y ∈ ∂W` and a *relative fundamental class* `w ∈ H_{n+1}(W, ∂W)` (`Work.Orient.IsRelFundClass`,
i.e. `w` restricts to a local generator at every interior point), the connecting map

`δ_y : H_{n+1}(W, ∂W) ⟶ H_n(∂W, ∂W∖{y})`

of the triple `∂W∖{y} ⊆ ∂W ⊆ W` is **surjective**.

## The route

Let `K ⊆ W` be a coordinate half-ball around `y` (`K = halfBallPiece (n+1) W y r`, lying in the
interior except on the boundary), and put

* `P := K ∩ W°` (the interior part of `K`),
* `B' := ∂W ∪ (W∖K)` (so that `W∖B' = P`),
* `A := B'∖{y}`.

The map of **triples** `(∂W∖{y} ⊆ ∂W ⊆ W) ⟶ (A ⊆ B' ⊆ W)` (all the inclusions are the
identity on `W`) induces, by the naturality of the connecting homomorphism
(`HomologicalComplex.HomologySequence.δ_naturality`), the **commutative square**

`e ≫ δ_y = ρ ≫ δ'`

in `H_n(B', A)`, where `e : H_n(∂W, ∂W∖{y}) → H_n(B', A)`, `ρ : H_{n+1}(W, ∂W) → H_{n+1}(W, B')`
and `δ'` is the connecting map of the second triple.  It then suffices to know

* **(I)** `e` is injective (excision: `B` and `B'` agree near `y`);
* **(II)** `ρ` is onto (the hypothesis that `w` is a relative fundamental class: the localisation
  of `w` at an interior point `x ∈ P` generates `H_{n+1}(W, W∖{x})`, and the localisation
  `H_{n+1}(W, W∖P) → H_{n+1}(W, W∖{x})` is injective);
* **(III)** `δ'` is onto (immediate from `H_n(W, A) = 0` and the long exact sequence of the triple,
  i.e. from the vanishing of `H_n(W, W∖(P∪{y}))`).

The two geometric inputs are isolated below as `isZero_halfBallInterior_union_point` and
`injective_localisation_of_halfBallInterior`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **(I)** The map `e` on the `n`-th homology induced by the inclusion of pairs
`(∂W, ∂W∖{y}) → (B', A)` is injective (excision: `∂W` and `B'` agree near `y`). -/
theorem tripleConnecting_input₁ (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (tripleMap W (bdryMinus_sub_bdrySetW n W y)
        (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
        (bdrySetW_sub_bigB n W y r)).τ₁ n)) :=
  tripleMap_tau1_injective n W y hy r hr hgood

/-- **A point of the interior inside a coordinate half-ball at a boundary point.**  The chart at `y`
sends `y` to a point of the hyperplane of the model, so a small step in the direction of the
positive normal gives a point of the chart target that is an interior point of `W` and still lies
in the half-ball piece. -/
theorem exists_mem_halfBallPiece_and_notMem_boundary (n : ℕ) (W : TopCat.{0}) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    ∃ x : W, x ∈ Work.Orient.halfBallPiece (n + 1) W y r ∧
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := by
  classical
  set e := chartAt (EuclideanHalfSpace (n + 1)) y with he
  set v : EuclideanSpace ℝ (Fin (n + 1)) :=
    ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) + (r / 4) • EuclideanSpace.single 0 1 with hv
  have hc0 : ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 := chartAt_boundary_coord_zero n W hy
  have hv0 : v 0 = r / 4 := by
    rw [hv]
    simp only [PiLp.add_apply, PiLp.smul_apply, hc0, PiLp.single_apply, ↓reduceIte, smul_eq_mul,
      mul_one, zero_add]
  have hdist : dist v ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) = r / 4 := by
    rw [hv]
    have hsub : ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) + (r / 4) • EuclideanSpace.single 0 1
        - (e y).1 = (r / 4) • EuclideanSpace.single 0 1 := by abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ r / 4),
      EuclideanSpace.norm_single]
    simp
  have hvnn : (0 : ℝ) ≤ v 0 := by rw [hv0]; positivity
  set w : EuclideanHalfSpace (n + 1) := ⟨v, hvnn⟩ with hw
  have hhalf : Work.Orient.halfIncl (n + 1) w
      = ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) + (r / 4) • EuclideanSpace.single 0 1 := rfl
  have hhalf' : Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) y) y)
      = ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) := rfl
  have hvt : ((e y).1 : EuclideanSpace ℝ (Fin (n + 1))) + (r / 4) • EuclideanSpace.single 0 1 = v :=
    hv.symm
  have hwt : w ∈ e.target := by
    apply hgood
    rw [Set.mem_preimage, hhalf, hvt, hhalf', Metric.mem_ball, hdist]
    linarith
  refine ⟨e.symm w, ?_, ?_⟩
  · refine ⟨?_, e.map_target hwt⟩
    rw [Set.mem_preimage, OpenPartialHomeomorph.right_inv e hwt]
    rw [Set.mem_preimage, hhalf, hvt, hhalf', Metric.mem_closedBall, hdist]
    linarith
  · refine not_mem_boundary_of_chartAt_pos (n := n) (W := W) (z := y) (x := e.symm w)
      (e.map_target hwt) ?_
    rw [OpenPartialHomeomorph.right_inv e hwt]
    exact (show (0 : ℝ) < w.1 0 from by rw [hv0]; positivity)

/-- **(II)** The map `ρ` on the `(n+1)`-st homology induced by the inclusion of pairs
`(W, ∂W) → (W, B')` is **onto**, using that `w` is a relative fundamental class. -/
theorem tripleConnecting_input₂ (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (w : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1))
    (hw : Work.Orient.IsRelFundClass W (n + 1) (bdrySetW n W) w) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (tripleMap W (bdryMinus_sub_bdrySetW n W y)
        (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
        (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1))) := by
  classical
  have hτ : (tripleMap W (bdryMinus_sub_bdrySetW n W y)
        (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
        (bdrySetW_sub_bigB n W y r)).τ₃
      = Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
          (bdrySetW_sub_bigB n W y r) := rfl
  rw [hτ]
  -- name the map under consideration, so that the goal and the auxiliary statements
  -- mention literally the same term
  set ρm : Work.Cohomology.relChains W (bdrySetW n W) ⟶
      Work.Cohomology.relChains W (bigB n W y r) :=
    Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
      (bdrySetW_sub_bigB n W y r) with hρm
  obtain ⟨x, hxK, hxbdry⟩ := exists_mem_halfBallPiece_and_notMem_boundary n W y hy r hr hgood
  have hxnotB : x ∉ bdrySetW n W := hxbdry
  have hxnotB' : x ∉ bigB n W y r := fun h => h ⟨hxK, hxbdry⟩
  -- the two inclusions
  have hinc : bigB n W y r ⊆ (({x} : Set W))ᶜ := fun _ hz hzx => hxnotB' (hzx ▸ hz)
  have hsing : ({x} : Set W) ⊆ halfBallK n W y r ∩ (bdrySetW n W)ᶜ :=
    Set.singleton_subset_iff.mpr ⟨hxK, hxbdry⟩
  -- the localisation `L` is the map induced by `B' ⊆ W∖{x}`
  have hLid : Work.Orient.resRelH W (n + 1) hsing
      = (HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc)
          (n + 1)).hom := by
    have hmap : Work.Cohomology.relCokerMap W (bigB n W y r) (({x} : Set W)ᶜ)
          (Set.compl_subset_compl.mpr hsing)
        = Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc :=
      (relChainsIncl_eq_relCokerMap W hinc).symm
    unfold Work.Orient.resRelH Work.ThomBordism.RelHmap
    rw [hmap]
  -- the composite with `ρ` is the map of the hypothesis `hw`
  have hcomp : Work.Orient.relPunct W (bdrySetW n W) x hxnotB
      = ρm ≫ Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc := by
    rw [hρm, relPunct_eq_relChainsIncl]
    rw [← relChainsIncl_comp (X := W) (bdrySetW_sub_bigB n W y r) hinc]
    rw [relChainsIncl_eq_relCokerMap (X := W) (bdrySetW_sub_bigB n W y r)]
  -- the two maps are equal, in linear-map form
  have hLρ : (Work.Orient.resRelH W (n + 1) hsing).comp
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1)))
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1)) := by
    rw [hLid, hcomp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  -- the localisation, in the `RelH` spelling (so that the scalar actions agree)
  let Hloc : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1) →ₗ[ℤ]
      Work.Orient.RelH W (n + 1) {x} :=
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1))
  have hHloc : ∀ a, Hloc a = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1))) a := fun _ => rfl
  have hLcomp : ∀ a, (Work.Orient.resRelH W (n + 1) hsing)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) a) = Hloc a := by
    intro a
    rw [hHloc]
    exact congrArg (fun (f : _ →ₗ[ℤ] _) => f a) hLρ
  have hLinj : Function.Injective (Work.Orient.resRelH W (n + 1) hsing) :=
    Work.Orient.Boundary.injective_localisation_of_halfBallInterior n W y hy r hr hgood x
      ⟨hxK, hxbdry⟩
  intro v
  have hv : (Work.Orient.resRelH W (n + 1) hsing) v ∈ Submodule.span ℤ ({Hloc w} : Set _) := by
    rw [hHloc, hw x hxnotB]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hv
  -- align the two `ℤ`-scalar actions
  have hmz : m • Hloc w = (Work.Orient.resRelH W (n + 1) hsing) v := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Orient.RelH W (n + 1) {x})) m (Hloc w)]
    exact hm
  refine ⟨m • w, hLinj ?_⟩
  exact (hLcomp (m • w)).trans ((map_zsmul Hloc m w).trans hmz)

/-- **The vanishing input.** For the coordinate half-ball `K` around the boundary point `y`, the
relative group `H_n(W, W∖(K∩W° ∪ {y}))` vanishes (equivalently
`H_n(W, A) = 0` for `A = B'∖{y} = (∂W ∪ (W∖K))∖{y}`). -/
theorem tripleConnecting_input₀ (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains W
      ((((Work.Orient.halfBallPiece (n + 1) W y r) ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ∪ {y})ᶜ)).homology n) :=
  isZero_halfBallInteriorUnionPoint n W y hy r hr hgood

theorem triple_δ_surjective_of_isZero (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    Function.Surjective (ModuleCat.Hom.hom
      ((Work.Cohomology.relChains_triple_shortExact W (bigA n W y r) (bigB n W y r)
        (bigA_sub_bigB n W y r)).δ (n + 1) n (by simp [ComplexShape.down]))) := by
  have hzero : IsZero ((Work.Cohomology.relChains W (bigA n W y r)).homology n) := by
    have h1 : Work.Cohomology.relChains W (bigA n W y r)
        = Work.Cohomology.relChains W
          (((halfBallK n W y r) ∩ (bdrySetW n W)ᶜ) ∪ {y})ᶜ :=
      congrArg (fun S : Set W => Work.Cohomology.relChains W S) (bigA_eq n W y r)
    rw [h1]
    exact tripleConnecting_input₀ n W y hy r hr hgood
  have hexact := (Work.Cohomology.relChains_triple_shortExact W (bigA n W y r) (bigB n W y r)
      (bigA_sub_bigB n W y r)).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])
  have hf0 : HomologicalComplex.homologyMap (Work.Cohomology.tripleShort W (bigA n W y r)
      (bigB n W y r) (bigA_sub_bigB n W y r)).f n = 0 :=
    IsZero.eq_zero_of_tgt hzero _
  haveI : Epi ((Work.Cohomology.relChains_triple_shortExact W (bigA n W y r) (bigB n W y r)
      (bigA_sub_bigB n W y r)).δ (n + 1) n (by simp [ComplexShape.down])) :=
    ShortComplex.Exact.epi_f hexact hf0
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-! ## 3. The main proof -/

theorem tripleConnectingMap_surjective_of_isRelFundClass (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (w : (Work.Cohomology.relChains W
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (hw : Work.Orient.IsRelFundClass W (n + 1)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w)
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    Function.Surjective (ModuleCat.Hom.hom
      ((Work.Cohomology.relChains_triple_shortExact W
        (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) \ {y})
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (by rintro z ⟨hz, -⟩; exact hz)).δ (n + 1) n (by simp [ComplexShape.down]))) := by
  classical
  obtain ⟨r, hr, hgood, -⟩ :=
    Work.Orient.Boundary.exists_halfBall_subset n (W := W) (U := Set.univ) isOpen_univ
      (Set.mem_univ y)
  have hnat := tripleMap_delta_naturality W (bdryMinus_sub_bdrySetW n W y)
    (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r) n
  have hsquare : ∀ a : (Work.Cohomology.relChains W
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1),
      (HomologicalComplex.homologyMap (tripleMap W (bdryMinus_sub_bdrySetW n W y)
          (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
          (bdrySetW_sub_bigB n W y r)).τ₁ n)
        (((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y) (bdrySetW n W)
            (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n (by simp [ComplexShape.down])) a)
      = ((Work.Cohomology.relChains_triple_shortExact W (bigA n W y r) (bigB n W y r)
            (bigA_sub_bigB n W y r)).δ (n + 1) n (by simp [ComplexShape.down]))
          ((HomologicalComplex.homologyMap (tripleMap W (bdryMinus_sub_bdrySetW n W y)
              (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
              (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)) a) := by
    intro a
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun φ => φ a) hnat
  have hInj := tripleConnecting_input₁ n W y hy r hr hgood
  have hSurjρ := tripleConnecting_input₂ n W y hy r hr hgood w hw
  have hSurjδ := triple_δ_surjective_of_isZero n W y hy r hr hgood
  intro c
  obtain ⟨u, hu⟩ := hSurjδ ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    (tripleMap W (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
      (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)).τ₁ n)) c)
  obtain ⟨a, ha⟩ := hSurjρ u
  refine ⟨a, hInj ?_⟩
  rw [hsquare a, ha, hu]

end

end Work.Orient.Boundary

