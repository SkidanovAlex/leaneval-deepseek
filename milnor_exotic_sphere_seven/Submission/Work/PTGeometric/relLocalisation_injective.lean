import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfCompactZero
import Submission.Work.Orient.Boundary.RelChainsBridge
import Submission.Work.Orient.Bridge
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.PTGeometric.exists_boundaryCollapse_gen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `relLocalisation_injective`: Hatcher 3.27 (a) for the whole interior

The statement (unchanged, at the bottom of the file) says: for a compact connected `C¹`
`(n+1)`-manifold `W` with boundary, a class `u ∈ H_{n+1}(W,∂W;ℤ)` whose localisation at *every*
interior point vanishes is zero.

## The route (no collar needed)

1. `Work.Orient.Boundary.HalfCompactZero` (proved in the workspace, the half-space port of Hatcher
   3.27(a)) applied to a *compact* set `K` of interior points gives: the image of `u` in
   `H_{n+1}(W, W∖K)` is zero, as soon as the localisations of `u` vanish at the points of `K`.
   The comparison between the point localisation of `u` and the `resRelH` of its image in
   `H_{n+1}(W, W∖K)` is `localisation_factor` below (a direct `relChainsIncl`-functoriality
   computation).
2. The workspace's **boundary-collapse** technology (`Work.PTGeometric.exists_boundaryCollapse_gen`,
   the general-`n` form of `Work.ThomBordism.RelDuality.exists_boundaryCollapse`) supplies, when
   `∂W ≠ ∅`, a compact `K ⊆ int W` and a self-map `ψ` of `W` with
   `ψ(W∖K) ⊆ ∂W`, `ψ|∂W = id`, and `ψ ≃ id` through maps preserving `∂W`.
3. The **chain-level chase** (`u_eq_zero_of_kills_comp` below): `ψ#` maps chains supported off `K`
   into `C_*(∂W)`, so it descends to a map `M : relChains W (Kᶜ) ⟶ relChains W (∂W)`; with
   `L : relChains W (∂W) ⟶ relChains W (Kᶜ)` the localisation, the composite identity
   `L ≫ M = M₀` holds (`M₀` = the map induced by `ψ` on `relChains W (∂W)`), and
   `M₀ = id` on homology by the *proved* pairs-version of homotopy invariance
   (`Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic`).  Hence
   `u = (M₀)_* u = M_*(L_* u) = M_* 0 = 0`.
4. If `∂W = ∅`: apply `HalfCompactZero` with `K := W` (compact, and all its points are interior)
   to get that the image of `u` in `H_{n+1}(W, W∖W) = H_{n+1}(W)` vanishes.  The passage back from
   that image to `u` is *not* a transport along the set equality `∂W = ∅`: the two inclusions
   `∂W ⊆ Wᶜ` and `Wᶜ ⊆ ∂W` compose to a self-inclusion, and `relChainsIncl_self` below identifies
   the self-inclusion map with the identity, so `u` is the image of `(relChainsIncl …)* u` under an
   explicit map.  This is where the empty-boundary case is dispatched without any `eqToHom`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-- `resRelH` is the homology of `relChainsIncl` (complement form). -/
theorem resRelH_eq (W : TopCat) (m : ℕ) {A B : Set W} (h : A ⊆ B) :
    Work.Orient.resRelH W m h
      = (HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (Set.compl_subset_compl.mpr h)) m).hom :=
  Work.Orient.Boundary.resRelH_eq_relChainsIncl W m h _

/-- **`relChainsIncl` of a self-inclusion is the identity.** -/
theorem relChainsIncl_self (W : TopCat) (A : Set W) :
    Work.Orient.relChainsIncl W (A := A) (B := A) (fun x hx => hx)
      = 𝟙 (Work.Cohomology.relChains W A) := by
  rw [Work.Orient.relChainsIncl_eq_relCokerMap]
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains W A))).mp
  rw [Work.Cohomology.relCokerMap_comp_π]
  exact (Category.comp_id _).symm

/-- The relative chain map induced by the identity is the identity on homology. -/
theorem relChainsMapOf_id_homologyMap (W : TopCat.{0}) (B : Set W) (m : ℕ) :
    HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf W W B B (𝟙 W)
          (Work.Cohomology.relMapSub B B (𝟙 W) (fun x hx => hx))
          (Work.Cohomology.relMapSub_spec B B (𝟙 W) (fun x hx => hx))) m
      = HomologicalComplex.homologyMap (𝟙 (Work.Cohomology.relChains W B)) m :=
  congrArg (fun φ => HomologicalComplex.homologyMap φ m)
    (Work.PTGeometric.HOF.relChainsMapOf_id W B)

/-- **The localisation at a point factors through the localisation to a compact set.**  For
`K ⊆ int W`, the point localisation (at `x ∈ K`) of `u ∈ H_{n+1}(W,∂W)` equals the `resRelH` of the
image of `u` in `H_{n+1}(W, W∖K)`. -/
theorem localisation_factor
    (W : TopCat.{0}) [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (K : Set W) (hKint : K ⊆ ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ)
    {u : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1)}
    {x : W} (hx : x ∈ K) :
    Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)
        ((HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            (B := Kᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u)
      = (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x
            (hKint hx)) (n + 1)).hom u := by
  have hφ : Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (B := Kᶜ) (fun x hx hxK => hKint hxK hx)
      ≫ Work.Orient.relChainsIncl W (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))
      = Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x
          (hKint hx) := by
    rw [Work.Orient.relChainsIncl_trans, Work.Orient.relPunct_eq_relChainsIncl]
  rw [resRelH_eq W (n + 1) (h := Set.singleton_subset_iff.mpr hx)]
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, hφ]
  rfl

/-- **The chase.**  Given the boundary-collapse datum, a class killed by the localisation to the
collapsed compact set of interior points is zero. -/
theorem u_eq_zero_of_kills_comp
    (W : TopCat.{0}) [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (K : Set W) (hKint : K ⊆ ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ)
    (ψ : ContinuousMap W W)
    (hψ_compl : ∀ x : W, x ∈ Kᶜ → ψ x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hψ_fix : ∀ x : W, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W → ψ x = x)
    (H : (ContinuousMap.id W).Homotopy ψ)
    (hH : ∀ (t : unitInterval) (x : W),
      x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      H.toContinuousMap (t, x) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {u : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1)}
    (hzero : (HomologicalComplex.homologyMap
      (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (B := Kᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u = 0) :
    u = 0 := by
  classical
  have hcompl : ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ⊆ Kᶜ :=
    fun x hx hxK => hKint hxK hx
  have hψ_bnd : ∀ x : W, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      ψ x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W :=
    fun x hx => by rw [hψ_fix x hx]; exact hx
  -- the transfer `M : relChains W (Kᶜ) → relChains W (∂W)`
  set M : Work.Cohomology.relChains W (Kᶜ) ⟶
      Work.Cohomology.relChains W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Work.Cohomology.relChainsMapOf W W (Kᶜ)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ)
      (Work.Cohomology.relMapSub (Kᶜ)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_compl)
      (Work.Cohomology.relMapSub_spec (Kᶜ)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_compl)
    with hM
  set M₀ : Work.Cohomology.relChains W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ⟶
      Work.Cohomology.relChains W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Work.Cohomology.relChainsMapOf W W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ)
      (Work.Cohomology.relMapSub ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_bnd)
      (Work.Cohomology.relMapSub_spec ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_bnd)
    with hM₀
  -- the composite identity `L ≫ M = M₀`
  have hLM : Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (B := Kᶜ) (fun x hx hxK => hKint hxK hx) ≫ M = M₀ := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)))).mp
    rw [← Category.assoc, Work.Orient.relChainsIncl_eq_relCokerMap,
      Work.Cohomology.relCokerMap_comp_π]
    rw [hM, hM₀, Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf,
      Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf]
  -- `M₀` is the identity on homology, by homotopy invariance of pairs
  have hhom := Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic
    (X := W) (Y := W)
    ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (f₀ := 𝟙 W) (f₁ := TopCat.ofHom ψ)
    (Work.Cohomology.relMapSub ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (𝟙 W) (fun x hx => hx))
    (Work.Cohomology.relMapSub ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_bnd)
    (Work.Cohomology.relMapSub_spec ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (𝟙 W) (fun x hx => hx))
    (Work.Cohomology.relMapSub_spec ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (TopCat.ofHom ψ) hψ_bnd)
    H (fun t x hx => hH t x hx) (n + 1)
  have h1 : (HomologicalComplex.homologyMap M₀ (n + 1)).hom u = u := by
    rw [← hhom,
      relChainsMapOf_id_homologyMap W
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (n + 1),
      HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
    rfl
  have h2 : (HomologicalComplex.homologyMap M₀ (n + 1)).hom u
      = (HomologicalComplex.homologyMap M (n + 1)).hom
          ((HomologicalComplex.homologyMap
            (Work.Orient.relChainsIncl W
              (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
              (B := Kᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u) := by
    rw [← hLM, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
  rw [← h1, h2, hzero, map_zero]

/-- **Hatcher 3.27 (a) for the whole interior.**  A class in `H_{n+1}(W, ∂W)` whose localisation
at every interior point vanishes is zero. -/
theorem relLocalisation_injective {n : ℕ} (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ConnectedSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {u : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1)}
    (h : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x hx)
        (n + 1)).hom u = 0) :
    u = 0 := by
  classical
  by_cases hB : ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W).Nonempty
  · -- `∂W ≠ ∅`: use the boundary collapse
    obtain ⟨K, hKc, hKint, ψ, hψ_compl, hψ_fix, H, hH⟩ :=
      exists_boundaryCollapse_gen W (n := n) hB
    have hzero : (HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          (B := Kᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u = 0 := by
      refine Work.Orient.Boundary.HalfCompactZero n W hKc (fun x hx => hKint hx)
        ((HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            (B := Kᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u) (fun x hx => ?_)
      rw [localisation_factor W K hKint (x := x) hx]
      exact h x (hKint hx)
    exact u_eq_zero_of_kills_comp W K hKint ψ hψ_compl hψ_fix H hH hzero
  · -- `∂W = ∅`: `HalfCompactZero` with `K := W`, and the self-inclusion of `∂W`
    have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hB
    have hKint : (Set.univ : Set W) ⊆ ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ :=
      fun x _ => by rw [hb]; exact Set.notMem_empty x
    have hzero : (HomologicalComplex.homologyMap
        (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          (B := (Set.univ : Set W)ᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u = 0 := by
      refine Work.Orient.Boundary.HalfCompactZero n W isCompact_univ
        (fun x _ => by rw [hb]; exact Set.notMem_empty x)
        ((HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            (B := (Set.univ : Set W)ᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u)
        (fun x hx => ?_)
      rw [localisation_factor W (Set.univ : Set W) hKint (x := x) hx]
      exact h x (by rw [hb]; exact Set.notMem_empty x)
    -- the two inclusions `∂W ⊆ Wᶜ ⊆ ∂W` compose to a self-inclusion
    have h₂ : (Set.univ : Set W)ᶜ ⊆ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W :=
      fun x hx => by rw [hb]; exact absurd hx (by simp)
    have hcomp : Work.Orient.relChainsIncl W
          (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          (B := (Set.univ : Set W)ᶜ) (fun x hx hxK => hKint hxK hx)
        ≫ Work.Orient.relChainsIncl W h₂
        = 𝟙 (Work.Cohomology.relChains W
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) := by
      rw [Work.Orient.relChainsIncl_trans]
      exact relChainsIncl_self W _
    have hsplit : u = (HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W h₂) (n + 1)).hom
        ((HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            (B := (Set.univ : Set W)ᶜ) (fun x hx hxK => hKint hxK hx)) (n + 1)).hom u) := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, hcomp,
        HomologicalComplex.homologyMap_id]
      rfl
    rw [hsplit, hzero, map_zero]

end

end Work.PTGeometric
