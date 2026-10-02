import Mathlib
import Submission.Work.StemsB.wedgeCellDefs
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.wedgeFstSnd_injective
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.Serre.Wedge.Main
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.Serre.Wedge.Geom
import Submission.Work.Serre.Wedge.Cell
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins
import Mathlib.RingTheory.OrzechProperty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cell classes generate `π_{n+2}` of the wedge of spheres

This module builds the tools for `Work.StemsB.wedge_cellClass_generate`: the connectivity of the
wedge, the pinch maps onto the cells, and the resulting detection of the cell classes.

The strategy:
* the wedge `wX n S` is `(n+1)`-connected (`Work.RatHurewicz.compressRel_attachCells_range`), so the
  Hurewicz map `π_{n+2} → H_{n+2}` is an isomorphism (`Work.Stems.hurewicz_first_degree`);
* for each cell `s` the pinch `wedgePinch n S s` collapses every other cell to the base point and
  is the inverse of the cell's sphere map on the `s`-th cell; hence on `H_{n+2}` it detects exactly
  the `s`-th cell class;
* combined with `wedgeHomology` (which makes `H_{n+2}` finitely generated and isomorphic to the
  target module) and `OrzechProperty.injective_of_surjective_of_injective`, this makes the
  Hurewicz images of the cell classes generate `H_{n+2}`.
-/

open CategoryTheory CategoryTheory.Limits Classical
open scoped Topology Topology.Homotopy unitInterval

set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

/-! ## Connectivity of the wedge -/

theorem wedge_pi_subsingleton (n : ℕ) (S : Type) (i : ℕ) (hi : i ≤ n + 1) :
    Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S)) := by
  have hcomp : Work.RatHurewicz.CompressRel (Work.Serre.Wedge.wX n S)
      (Set.range (Work.RatHurewicz.attachIncl n PUnit.{1} S (Work.Serre.Wedge.wF n S))) i :=
    Work.RatHurewicz.compressRel_attachCells_range n PUnit.{1} S (Work.Serre.Wedge.wF n S) i hi
  rw [Work.Serre.Wedge.range_attachIncl_wF] at hcomp
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      show Quotient.mk _ p = Quotient.mk _ q
      have key : ∀ r : Ω^ (Fin i) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S),
          r.1.HomotopicRel (ContinuousMap.const _ (Work.Serre.Wedge.wB n S))
            (Cube.boundary (Fin i)) := by
        intro r
        obtain ⟨G, hG0, hGbd, hG1⟩ := hcomp r.1 (fun x hx => r.2 x hx)
        exact ⟨⟨⟨fun z => G (z.2, z.1),
            G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,
          (fun x => hG0 x), (fun x => by simpa using hG1 x)⟩,
          (fun t x hx => hGbd x hx t)⟩
      exact Quotient.sound (ContinuousMap.HomotopicRel.trans (key p)
        (ContinuousMap.HomotopicRel.symm (key q)))


/-! ## The pinch maps -/

/-- The chosen cube/disc homeomorphism of `Work.Serre.cubeDiskHomeo`. -/
def cubeHomeoE (n : ℕ) :
    Work.Stems.Cubical.IC (n + 2) ≃ₜ Work.RatHurewicz.cellDisk n :=
  Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))

theorem cubeHomeoE_boundary (n : ℕ) (x : Work.Stems.Cubical.IC (n + 2)) :
    x ∈ Cube.boundary (Fin (n + 2)) ↔
      ((cubeHomeoE n x : Work.RatHurewicz.cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))
        ∈ Metric.sphere 0 1 :=
  (Classical.choose_spec (Work.Serre.cubeDiskHomeo (n + 2))) x

/-- The base point of the top sphere `S^{n+2}`, the image of the boundary of the cube. -/
def sphTop (n : ℕ) : Work.Stems.sphere (n + 2) :=
  (Work.Stems.collapseMap (n + 2) (by omega)) 0

/-- The map `D^{n+2} → S^{n+2}` collapsing the boundary sphere to the base point. -/
def diskCollapse (n : ℕ) : C(Work.RatHurewicz.cellDisk n, Work.Stems.sphere (n + 2)) :=
  (Work.Stems.collapseMap (n + 2) (by omega)).comp
    ⟨⇑(cubeHomeoE n).symm, (cubeHomeoE n).symm.continuous⟩

theorem diskCollapse_boundary (n : ℕ) (z : Work.RatHurewicz.cellSphere n) :
    diskCollapse n (Work.RatHurewicz.cellSphereToDisk n z) = sphTop n := by
  have hmem : (cubeHomeoE n).symm (Work.RatHurewicz.cellSphereToDisk n z)
      ∈ Cube.boundary (Fin (n + 2)) := by
    rw [cubeHomeoE_boundary, Homeomorph.apply_symm_apply]
    exact z.2
  show (Work.Stems.collapseMap (n + 2) (by omega))
      ((cubeHomeoE n).symm (Work.RatHurewicz.cellSphereToDisk n z)) = sphTop n
  rw [Work.Stems.collapseMap_boundary (n + 2) (by omega) hmem]
  rfl

/-- The attaching data for the pinch map of the `s`-th cell. -/
def pinchData (n : ℕ) (S : Type) (s : S) :
    ∀ t : S, C(Work.RatHurewicz.cellDisk n, Work.Stems.sphere (n + 2)) :=
  fun t => if t = s then diskCollapse n
    else ContinuousMap.const (Work.RatHurewicz.cellDisk n) (sphTop n)

theorem pinchData_boundary (n : ℕ) (S : Type) (s : S) (t : S)
    (z : Work.RatHurewicz.cellSphere n) :
    pinchData n S s t (Work.RatHurewicz.cellSphereToDisk n z) = sphTop n := by
  unfold pinchData
  by_cases ht : t = s
  · rw [if_pos ht]; exact diskCollapse_boundary n z
  · rw [if_neg ht]; rfl

theorem wedgePinch_exists (n : ℕ) (S : Type) (s : S) :
    ∃ g' : C(Work.Serre.Wedge.wX n S, Work.Stems.sphere (n + 2)),
      g'.comp (Work.RatHurewicz.attachIncl n PUnit.{1} S (Work.Serre.Wedge.wF n S))
        = ContinuousMap.const PUnit.{1} (sphTop n) ∧
      ∀ t : S, g'.comp (Work.RatHurewicz.cellMap n PUnit.{1} S (Work.Serre.Wedge.wF n S) t)
        = pinchData n S s t :=
  Work.RatHurewicz.attachCells_extension n PUnit.{1} S (Work.Serre.Wedge.wF n S)
    (ContinuousMap.const PUnit.{1} (sphTop n)) (pinchData n S s)
    (fun t z => by
      show pinchData n S s t (Work.RatHurewicz.cellSphereToDisk n z)
        = (ContinuousMap.const PUnit.{1} (sphTop n)) (Work.Serre.Wedge.wF n S t z)
      rw [pinchData_boundary]
      rfl)

/-- **The pinch map of the `s`-th cell**: the identity (inverse of the cell's sphere map) on the
`s`-th cell and the constant map at the base point on all other cells. -/
def wedgePinch (n : ℕ) (S : Type) (s : S) :
    C(Work.Serre.Wedge.wX n S, Work.Stems.sphere (n + 2)) :=
  Classical.choose (wedgePinch_exists n S s)

theorem wedgePinch_comp_attachIncl (n : ℕ) (S : Type) (s : S) :
    (wedgePinch n S s).comp (Work.RatHurewicz.attachIncl n PUnit.{1} S (Work.Serre.Wedge.wF n S))
      = ContinuousMap.const PUnit.{1} (sphTop n) :=
  (Classical.choose_spec (wedgePinch_exists n S s)).1

theorem wedgePinch_comp_cellMap (n : ℕ) (S : Type) (s t : S) :
    (wedgePinch n S s).comp (Work.RatHurewicz.cellMap n PUnit.{1} S (Work.Serre.Wedge.wF n S) t)
      = pinchData n S s t :=
  (Classical.choose_spec (wedgePinch_exists n S s)).2 t

/-! ## The sphere map underlying a cell class -/

/-- The sphere map underlying the `s`-th cell class: the descent of the cell's cube to `S^{n+2}`. -/
def cellWrap (n : ℕ) (S : Type) (s : S) :
    C(Work.Stems.sphere (n + 2), Work.Serre.Wedge.wX n S) :=
  Work.Stems.cubeLift (n + 2) (by omega) ⟨wCellCube S s, wCellCube_boundary S s⟩

theorem cellWrap_comp_collapse (n : ℕ) (S : Type) (s : S) :
    (cellWrap n S s).comp (Work.Stems.collapseMap (n + 2) (by omega)) = wCellCube S s :=
  Work.Stems.cubeLift_comp (n + 2) (by omega) ⟨wCellCube S s, wCellCube_boundary S s⟩

/-- The cell cube is the cell map composed with the cube/disc homeomorphism. -/
theorem wCellCube_eq (n : ℕ) (S : Type) (s : S) :
    wCellCube S s = (Work.RatHurewicz.cellMap n PUnit.{1} S (Work.Serre.Wedge.wF n S) s).comp
      ⟨⇑(cubeHomeoE n), (cubeHomeoE n).continuous⟩ := rfl

/-- **The pinch of the `s`-th cell is a left inverse of the cell's sphere map.** -/
theorem wedgePinch_comp_cellWrap_self (n : ℕ) (S : Type) (s : S) :
    (wedgePinch n S s).comp (cellWrap n S s) = ContinuousMap.id (Work.Stems.sphere (n + 2)) := by
  have h : ((wedgePinch n S s).comp (cellWrap n S s)).comp
        (Work.Stems.collapseMap (n + 2) (by omega))
      = (ContinuousMap.id (Work.Stems.sphere (n + 2))).comp
        (Work.Stems.collapseMap (n + 2) (by omega)) := by
    rw [ContinuousMap.comp_assoc, cellWrap_comp_collapse, wCellCube_eq]
    rw [← ContinuousMap.comp_assoc, wedgePinch_comp_cellMap]
    unfold pinchData
    rw [if_pos rfl]
    show (diskCollapse n).comp ⟨⇑(cubeHomeoE n), (cubeHomeoE n).continuous⟩
      = (ContinuousMap.id (Work.Stems.sphere (n + 2))).comp
        (Work.Stems.collapseMap (n + 2) (by omega))
    refine ContinuousMap.ext (fun y => ?_)
    show (Work.Stems.collapseMap (n + 2) (by omega))
        ((cubeHomeoE n).symm ((cubeHomeoE n) y)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  refine ContinuousMap.ext (fun x => ?_)
  obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap (n + 2) (by omega)).surjective x
  have hx := congrArg
    (fun F : C(Work.Stems.CubeI (n + 2), Work.Stems.sphere (n + 2)) => F y) h
  simpa using hx

/-- **The pinch of any other cell kills the `s`-th cell's sphere map.** -/
theorem wedgePinch_comp_cellWrap_ne (n : ℕ) (S : Type) (s t : S) (h : s ≠ t) :
    (wedgePinch n S t).comp (cellWrap n S s)
      = ContinuousMap.const (Work.Stems.sphere (n + 2)) (sphTop n) := by
  have h' : ((wedgePinch n S t).comp (cellWrap n S s)).comp
        (Work.Stems.collapseMap (n + 2) (by omega))
      = ContinuousMap.const (Work.Stems.CubeI (n + 2)) (sphTop n) := by
    rw [ContinuousMap.comp_assoc, cellWrap_comp_collapse, wCellCube_eq]
    rw [← ContinuousMap.comp_assoc, wedgePinch_comp_cellMap]
    unfold pinchData
    rw [if_neg h]
    ext y
    rfl
  refine ContinuousMap.ext (fun x => ?_)
  obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap (n + 2) (by omega)).surjective x
  have hx := congrArg
    (fun F : C(Work.Stems.CubeI (n + 2), Work.Stems.sphere (n + 2)) => F y) h'
  simpa using hx


/-! ## The Hurewicz images of the cell classes -/

/-- The Hurewicz image of the `s`-th cell class. -/
def hCell (n : ℕ) (S : Type) (s : S) :
    (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology (n + 2) :=
  Work.Stems.hurewiczChain (n + 2) (by omega) (Work.Serre.Wedge.wB n S)
    ⟨wCellCube S s, wCellCube_boundary S s⟩

theorem hCell_eq (n : ℕ) (S : Type) (s : S) :
    hCell n S s = Work.Stems.hurewiczClass (n + 2) (by omega) (cellWrap n S s) := rfl

/-- A constant map has zero Hurewicz class. -/
theorem hurewiczClass_const (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (b : X) :
    Work.Stems.hurewiczClass n hn (ContinuousMap.const (Work.Stems.sphere n) b) = 0 := by
  rw [Work.Stems.hurewiczClass]
  have h := Work.Stems.wfs_hm_const' n (A := Work.Stems.sphere n) (B := X) b hn
  exact congrArg (fun (l : _ →ₗ[_] _) => l (Work.Stems.sphereGenerator n hn)) h

/-- **The `s`-th pinch sends the `s`-th cell class to the fundamental class of the sphere.** -/
theorem hm_wedgePinch_hCell_self (n : ℕ) (S : Type) (s : S) :
    (Work.Stems.hm (wedgePinch n S s) (n + 2)) (hCell n S s)
      = Work.Stems.sphereGenerator (n + 2) (by omega) := by
  rw [hCell_eq, ← Work.Stems.hurewiczClass_natural (n + 2) (by omega) (wedgePinch n S s)
    (cellWrap n S s), wedgePinch_comp_cellWrap_self]
  show Work.Stems.hurewiczClass (n + 2) (by omega)
      (ContinuousMap.id (Work.Stems.sphere (n + 2))) = _
  rw [Work.Stems.hurewiczClass]
  have h := Work.Stems.wfs_hm_id (n + 2) (A := Work.Stems.sphere (n + 2))
  exact congrArg (fun (l : _ →ₗ[_] _) => l (Work.Stems.sphereGenerator (n + 2) (by omega))) h

/-- **The other pinches kill the `s`-th cell class.** -/
theorem hm_wedgePinch_hCell_ne (n : ℕ) (S : Type) (s t : S) (h : s ≠ t) :
    (Work.Stems.hm (wedgePinch n S t) (n + 2)) (hCell n S s) = 0 := by
  rw [hCell_eq, ← Work.Stems.hurewiczClass_natural (n + 2) (by omega) (wedgePinch n S t)
    (cellWrap n S s), wedgePinch_comp_cellWrap_ne n S s t h]
  exact hurewiczClass_const (n + 2) (by omega) (sphTop n)

/-! ## The finite case: the cell classes generate the homology -/

/-- The chosen identification `H_{n+2}(S^{n+2}) ≅ ℤ`. -/
noncomputable def sphereIso (n : ℕ) (hn : 1 ≤ n) :
    ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology n)
      ≅ ModuleCat.of ℤ ℤ :=
  Classical.choice (Work.Cohomology.sphereHomologyTop n hn)

/-- The pinch coordinates of a homology class of the wedge. -/
noncomputable def pinchCoord (n : ℕ) (S : Type) :
    ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology (n + 2))
      →ₗ[ℤ] (S → ℤ) :=
  LinearMap.pi (fun s : S => ((sphereIso (n + 2) (by omega)).toLinearEquiv).toLinearMap.comp
    (Work.Stems.hm (wedgePinch n S s) (n + 2)))

theorem pinchCoord_apply (n : ℕ) (S : Type)
    (x : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
      (n + 2)) (s : S) :
    pinchCoord n S x s = (sphereIso (n + 2) (by omega)).toLinearEquiv
      ((Work.Stems.hm (wedgePinch n S s) (n + 2)) x) := by
  rw [pinchCoord, LinearMap.pi_apply]
  rfl

theorem pinchCoord_hCell_self (n : ℕ) (S : Type) (s : S) :
    pinchCoord n S (hCell n S s) s = 1 := by
  rw [pinchCoord_apply, hm_wedgePinch_hCell_self]
  exact Work.Stems.sphereGenerator_spec (n + 2) (by omega)

theorem pinchCoord_hCell_ne (n : ℕ) (S : Type) (s t : S) (h : s ≠ t) :
    pinchCoord n S (hCell n S s) t = 0 := by
  rw [pinchCoord_apply, hm_wedgePinch_hCell_ne n S s t h]
  simp

/-- The sum of the cell classes. -/
noncomputable def cellClassSum (n : ℕ) (S : Type) [Fintype S] :
    (S → ℤ) →ₗ[ℤ] ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
      (n + 2)) :=
  ∑ s : S, (LinearMap.toSpanSingleton ℤ _ (hCell n S s)).comp
    (LinearMap.proj (R := ℤ) (φ := fun _ : S => ℤ) s)

theorem cellClassSum_apply (n : ℕ) (S : Type) [Fintype S] (a : S → ℤ) :
    cellClassSum n S a = ∑ s, (LinearMap.toSpanSingleton ℤ _ (hCell n S s)) (a s) := by
  rw [cellClassSum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun s _ => by
    rw [LinearMap.comp_apply, LinearMap.proj_apply])

theorem pinchCoord_comp_cellClassSum (n : ℕ) (S : Type) [Fintype S] :
    (pinchCoord n S).comp (cellClassSum n S) = LinearMap.id := by
  refine LinearMap.ext (fun a => ?_)
  refine funext (fun s => ?_)
  show pinchCoord n S (cellClassSum n S a) s = a s
  rw [cellClassSum_apply]
  have hterm : ∀ t : S, (pinchCoord n S) ((LinearMap.toSpanSingleton ℤ _ (hCell n S t)) (a t))
      = a t • (pinchCoord n S (hCell n S t)) := by
    intro t
    rw [LinearMap.toSpanSingleton_apply, LinearMap.map_smul]
  have h1 : (pinchCoord n S) (∑ t, (LinearMap.toSpanSingleton ℤ _ (hCell n S t)) (a t))
      = ∑ t, a t • (pinchCoord n S (hCell n S t)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun t _ => hterm t)
  rw [h1, Finset.sum_apply, Finset.sum_eq_single s]
  · rw [Pi.smul_apply, pinchCoord_hCell_self]
    simp
  · intro t _ ht
    rw [Pi.smul_apply, pinchCoord_hCell_ne n S t s ht, smul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

/-- `H_{n+2}` of the wedge embeds into functions on the cells (for finitely many cells). -/
theorem exists_injective_coord (n : ℕ) (S : Type) [Fintype S] :
    ∃ i : ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
        (n + 2)) →ₗ[ℤ] (S → ℤ), Function.Injective i := by
  classical
  obtain ⟨e⟩ := Work.Serre.Wedge.wedgeHomology n S
  refine ⟨((e.toLinearEquiv.trans
    ((ModuleCat.coprodIsoDirectSum (fun _ : S => ModuleCat.of ℤ ℤ)).toLinearEquiv.trans
      (DirectSum.linearEquivFunOnFintype ℤ S (fun _ : S => ℤ)))).toLinearMap), ?_⟩
  exact (e.toLinearEquiv.trans
    ((ModuleCat.coprodIsoDirectSum (fun _ : S => ModuleCat.of ℤ ℤ)).toLinearEquiv.trans
      (DirectSum.linearEquivFunOnFintype ℤ S (fun _ : S => ℤ)))).injective

/-- The pinch coordinates detect homology classes (finitely many cells). -/
theorem pinchCoord_injective (n : ℕ) (S : Type) [Fintype S] :
    Function.Injective ⇑(pinchCoord n S) := by
  obtain ⟨i, hi⟩ := exists_injective_coord n S
  have hsurj : Function.Surjective ⇑(pinchCoord n S) := by
    intro y
    exact ⟨cellClassSum n S y, by
      rw [← LinearMap.comp_apply, pinchCoord_comp_cellClassSum, LinearMap.id_apply]⟩
  exact OrzechProperty.injective_of_surjective_of_injective i (pinchCoord n S) hi hsurj

/-- The cell classes span `H_{n+2}` of the finite wedge. -/
theorem cellClassSum_pinchCoord (n : ℕ) (S : Type) [Fintype S]
    (x : ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
      (n + 2))) :
    cellClassSum n S (pinchCoord n S x) = x := by
  refine pinchCoord_injective n S ?_
  rw [← LinearMap.comp_apply, pinchCoord_comp_cellClassSum, LinearMap.id_apply]

/-- **The finite case.**  The Hurewicz images of the cell classes generate `H_{n+2}` of the wedge. -/
theorem wedge_finite_hurewicz_generate (n : ℕ) (S : Type) [Fintype S] :
    ∀ x : ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
      (n + 2)), x ∈ Submodule.span ℤ (Set.range (fun s : S => hCell n S s)) := by
  intro x
  rw [← cellClassSum_pinchCoord n S x, cellClassSum_apply]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [LinearMap.toSpanSingleton_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self s))

/-! ## From homology to the homotopy group -/

/-- The (fork-neutral) Hurewicz map of the wedge, as a function. -/
abbrev wedgeH (n : ℕ) (S : Type) :
    HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S) →
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Serre.Wedge.wX n S))).homology
        (n + 2)) :=
  Work.Stems.hurewiczMapN (n + 2) (by omega) (Work.Serre.Wedge.wB n S)

theorem wedgeH_injective (n : ℕ) (S : Type) : Function.Injective (wedgeH n S) :=
  (Work.Stems.hurewicz_first_degree (n + 2) (by omega) (Work.Serre.Wedge.wB n S)
    (fun i hi => wedge_pi_subsingleton n S i (by omega))).1

theorem wedgeH_mul (n : ℕ) (S : Type)
    (β γ : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S)) :
    wedgeH n S (β * γ) = wedgeH n S β + wedgeH n S γ :=
  Work.Stems.hurewiczMapN_mul (n + 1) (Work.Serre.Wedge.wB n S) β γ

theorem wedgeH_wCellClass (n : ℕ) (S : Type) (s : S) :
    wedgeH n S (wCellClass S s) = hCell n S s := rfl

theorem cubeLift_const (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    Work.Stems.cubeLift n hn (GenLoop.const : Ω^ (Fin n) X x₀)
      = ContinuousMap.const (Work.Stems.sphere n) x₀ := by
  refine ContinuousMap.ext (fun z => ?_)
  obtain ⟨y, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
  have h := congrFun (congrArg DFunLike.coe
    (Work.Stems.cubeLift_comp n hn (GenLoop.const : Ω^ (Fin n) X x₀))) y
  simpa using h

theorem wedgeH_one (n : ℕ) (S : Type) : wedgeH n S 1 = 0 := by
  show Work.Stems.hurewiczMapN (n + 2) (by omega) (Work.Serre.Wedge.wB n S) 1 = 0
  rw [HomotopyGroup.one_def]
  rw [Work.Stems.hurewiczMapN_mk]
  show Work.Stems.hurewiczClass (n + 2) (by omega)
      (Work.Stems.cubeLift (n + 2) (by omega)
        (GenLoop.const : Ω^ (Fin (n+2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))) = 0
  rw [cubeLift_const]
  exact hurewiczClass_const (n + 2) (by omega) (Work.Serre.Wedge.wB n S)

theorem wedgeH_inv (n : ℕ) (S : Type)
    (β : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S)) :
    wedgeH n S β⁻¹ = - wedgeH n S β := by
  have h := wedgeH_mul n S β β⁻¹
  rw [mul_inv_cancel, wedgeH_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem wedgeH_pow (n : ℕ) (S : Type)
    (β : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))
    (k : ℕ) :
    wedgeH n S (β ^ k)
      = (LinearMap.toSpanSingleton ℤ _ (wedgeH n S β)) (k : ℤ) := by
  induction k with
  | zero => rw [pow_zero, wedgeH_one]; exact (map_zero _).symm
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [pow_succ, wedgeH_mul, ih, hcast, map_add,
      LinearMap.toSpanSingleton_apply_one]

theorem wedgeH_zpow (n : ℕ) (S : Type)
    (β : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))
    (m : ℤ) :
    wedgeH n S (β ^ m)
      = (LinearMap.toSpanSingleton ℤ _ (wedgeH n S β)) m := by
  rcases m with k | k
  · have hm : (Int.ofNat k : ℤ) = (k : ℤ) := rfl
    rw [hm, zpow_natCast, wedgeH_pow]
  · have hm : (Int.negSucc k : ℤ) = -((k : ℤ) + 1) := Int.negSucc_eq k
    have hcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hm, zpow_neg, wedgeH_inv, hcast, zpow_natCast, wedgeH_pow, map_neg]

theorem wedgeH_finset_prod (n : ℕ) (S : Type) {ι : Type} (t : Finset ι)
    (f : ι → HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))
    (a : ι → ℤ) :
    wedgeH n S (∏ s ∈ t, (f s) ^ (a s))
      = ∑ s ∈ t, (LinearMap.toSpanSingleton ℤ _ (wedgeH n S (f s))) (a s) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, wedgeH_one]
  | insert s t hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs, wedgeH_mul, ih, wedgeH_zpow]

/-- **The finite case, at the level of the homotopy group.** -/
theorem wedge_finite_generate_pi (n : ℕ) (S : Type) [Fintype S]
    (β : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S)) :
    β ∈ Subgroup.closure (Set.range (wCellClass S)) := by
  classical
  set a : S → ℤ := pinchCoord n S (wedgeH n S β) with ha
  have hsum : (∑ s : S, (LinearMap.toSpanSingleton ℤ _ (wedgeH n S (wCellClass S s))) (a s))
      = cellClassSum n S a := by
    rw [cellClassSum_apply]
    exact Finset.sum_congr rfl (fun s _ => by rw [wedgeH_wCellClass])
  have hcomb : wedgeH n S (∏ s : S, (wCellClass S s) ^ (a s))
      = ∑ s : S, (LinearMap.toSpanSingleton ℤ _ (wedgeH n S (wCellClass S s))) (a s) := by
    simpa using wedgeH_finset_prod n S (Finset.univ : Finset S) (fun s => wCellClass S s) a
  have hx : wedgeH n S (∏ s : S, (wCellClass S s) ^ (a s)) = wedgeH n S β := by
    rw [hcomb, hsum, ha]
    exact cellClassSum_pinchCoord n S (wedgeH n S β)
  have hfin : (∏ s : S, (wCellClass S s) ^ (a s)) = β := wedgeH_injective n S hx
  rw [← hfin]
  exact Subgroup.prod_mem _
    (fun s _ => Subgroup.zpow_mem _
      (Subgroup.subset_closure (Set.mem_range_self s)) _)

/-! ## The sub-wedge over a set of cells, the collapse, and the finite reduction -/

/-- **Uniqueness in the universal property of a cell attachment.** -/
theorem attachCells_ext {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {Z : Type} [TopologicalSpace Z]
    (g₁ g₂ : C(Work.RatHurewicz.attachCells n Y ι f, Z))
    (h₁ : g₁.comp (Work.RatHurewicz.attachIncl n Y ι f)
      = g₂.comp (Work.RatHurewicz.attachIncl n Y ι f))
    (h₂ : ∀ i, g₁.comp (Work.RatHurewicz.cellMap n Y ι f i)
      = g₂.comp (Work.RatHurewicz.cellMap n Y ι f i)) :
    g₁ = g₂ := by
  ext y
  induction y using Quotient.inductionOn with
  | h z =>
    rcases z with y | p
    · have h := congrFun (congrArg DFunLike.coe h₁) y
      exact h
    · obtain ⟨i, u⟩ := p
      have h := congrFun (congrArg DFunLike.coe (h₂ i)) u
      exact h

/-- The inclusion of the sub-wedge over `T` into the wedge over `S`. -/
def wedgeInclData (n : ℕ) (S : Type) (T : Set S) :
    ∀ t : ↥T, C(Work.RatHurewicz.cellDisk n, Work.Serre.Wedge.wX n S) :=
  fun t => Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) t.1

theorem wedgeInclCompat (n : ℕ) (S : Type) (T : Set S) :
    ∀ (t : ↥T) (z : Work.RatHurewicz.cellSphere n),
      wedgeInclData n S T t (Work.RatHurewicz.cellSphereToDisk n z)
        = (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S))
          (Work.Serre.Wedge.wF n ↥T t z) := by
  intro t z
  show Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) t.1
      (Work.RatHurewicz.cellSphereToDisk n z) = Work.Serre.Wedge.wB n S
  rw [← Work.RatHurewicz.attachIncl_attachRel]
  rfl

/-- The inclusion of the sub-wedge, as a function on the quotient. -/
def wedgeInclFun (n : ℕ) (S : Type) (T : Set S) :
    Work.Serre.Wedge.wX n ↥T → Work.Serre.Wedge.wX n S :=
  Quotient.lift
    (s := Relation.EqvGen.setoid
      (Work.RatHurewicz.attachRel n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)))
    (Work.RatHurewicz.attachCellsGlue n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S)) (wedgeInclData n S T))
    (Work.RatHurewicz.attachCellsGlue_rel n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S)) (wedgeInclData n S T)
      (wedgeInclCompat n S T))

theorem continuous_wedgeInclFun (n : ℕ) (S : Type) (T : Set S) :
    Continuous (wedgeInclFun n S T) := by
  rw [wedgeInclFun]
  exact (Work.RatHurewicz.continuous_attachCellsGlue n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S))
      (wedgeInclData n S T)).quotient_lift
    (s := Relation.EqvGen.setoid
      (Work.RatHurewicz.attachRel n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)))
    (Work.RatHurewicz.attachCellsGlue_rel n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S)) (wedgeInclData n S T)
      (wedgeInclCompat n S T))

/-- The inclusion of the sub-wedge over `T` into the wedge over `S`. -/
def wedgeIncl (n : ℕ) (S : Type) (T : Set S) :
    C(Work.Serre.Wedge.wX n ↥T, Work.Serre.Wedge.wX n S) :=
  ⟨wedgeInclFun n S T, continuous_wedgeInclFun n S T⟩

theorem wedgeIncl_comp_attachIncl (n : ℕ) (S : Type) (T : Set S) :
    (wedgeIncl n S T).comp (Work.RatHurewicz.attachIncl n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T))
      = ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n S) := by
  ext y
  rfl

theorem wedgeIncl_comp_cellMap (n : ℕ) (S : Type) (T : Set S) (t : ↥T) :
    (wedgeIncl n S T).comp (Work.RatHurewicz.cellMap n PUnit.{1} ↥T (Work.Serre.Wedge.wF n ↥T) t)
      = Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) t.1 := by
  ext u
  rfl

theorem wedgeIncl_apply_wB (n : ℕ) (S : Type) (T : Set S) :
    wedgeIncl n S T (Work.Serre.Wedge.wB n ↥T) = Work.Serre.Wedge.wB n S := rfl

/-- The gluing data for the collapse of the cells outside `T`. -/
def wedgeCollapseData (n : ℕ) (S : Type) (T : Set S) :
    ∀ s : S, C(Work.RatHurewicz.cellDisk n, Work.Serre.Wedge.wX n ↥T) :=
  fun s => if h : s ∈ T then
      Work.RatHurewicz.cellMap n PUnit ↥T (Work.Serre.Wedge.wF n ↥T) ⟨s, h⟩
    else ContinuousMap.const (Work.RatHurewicz.cellDisk n) (Work.Serre.Wedge.wB n ↥T)

theorem wedgeCollapseCompat (n : ℕ) (S : Type) (T : Set S) :
    ∀ (s : S) (z : Work.RatHurewicz.cellSphere n),
      wedgeCollapseData n S T s (Work.RatHurewicz.cellSphereToDisk n z)
        = (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T))
          (Work.Serre.Wedge.wF n S s z) := by
  intro s z
  show (if h : s ∈ T then
      Work.RatHurewicz.cellMap n PUnit ↥T (Work.Serre.Wedge.wF n ↥T) ⟨s, h⟩
    else ContinuousMap.const (Work.RatHurewicz.cellDisk n) (Work.Serre.Wedge.wB n ↥T))
    (Work.RatHurewicz.cellSphereToDisk n z) = Work.Serre.Wedge.wB n ↥T
  by_cases h : s ∈ T
  · rw [dif_pos h, ← Work.RatHurewicz.attachIncl_attachRel]
    rfl
  · rw [dif_neg h]
    rfl

/-- The collapse of the cells outside `T`. -/
def wedgeCollapse (n : ℕ) (S : Type) (T : Set S) :
    C(Work.Serre.Wedge.wX n S, Work.Serre.Wedge.wX n ↥T) where
  toFun := Quotient.lift
    (Work.RatHurewicz.attachCellsGlue n PUnit.{1} S (Work.Serre.Wedge.wF n S)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T)) (wedgeCollapseData n S T))
    (Work.RatHurewicz.attachCellsGlue_rel n PUnit.{1} S (Work.Serre.Wedge.wF n S)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T)) (wedgeCollapseData n S T)
      (wedgeCollapseCompat n S T))
  continuous_toFun :=
    (Work.RatHurewicz.continuous_attachCellsGlue n PUnit.{1} S (Work.Serre.Wedge.wF n S)
      (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T)) (wedgeCollapseData n S T)).quotient_lift
      (Work.RatHurewicz.attachCellsGlue_rel n PUnit.{1} S (Work.Serre.Wedge.wF n S)
        (ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T)) (wedgeCollapseData n S T)
        (wedgeCollapseCompat n S T))

theorem wedgeCollapse_comp_attachIncl (n : ℕ) (S : Type) (T : Set S) :
    (wedgeCollapse n S T).comp (Work.RatHurewicz.attachIncl n PUnit.{1} S (Work.Serre.Wedge.wF n S))
      = ContinuousMap.const PUnit.{1} (Work.Serre.Wedge.wB n ↥T) := by
  ext y
  rfl

theorem wedgeCollapse_comp_cellMap (n : ℕ) (S : Type) (T : Set S) (s : S) :
    (wedgeCollapse n S T).comp (Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s)
      = wedgeCollapseData n S T s := by
  ext u
  rfl

theorem wedgeCollapse_apply_wB (n : ℕ) (S : Type) (T : Set S) :
    wedgeCollapse n S T (Work.Serre.Wedge.wB n S) = Work.Serre.Wedge.wB n ↥T := rfl

/-- The collapse is a left inverse of the inclusion. -/
theorem wedgeCollapse_wedgeIncl (n : ℕ) (S : Type) (T : Set S) :
    (wedgeCollapse n S T).comp (wedgeIncl n S T)
      = ContinuousMap.id (Work.Serre.Wedge.wX n ↥T) := by
  refine attachCells_ext (Work.Serre.Wedge.wF n ↥T) _ _ ?_ ?_
  · rw [ContinuousMap.comp_assoc, wedgeIncl_comp_attachIncl, ContinuousMap.comp_const,
      wedgeCollapse_apply_wB, ContinuousMap.id_comp]
    ext y
    rfl
  · intro t
    rw [ContinuousMap.comp_assoc, wedgeIncl_comp_cellMap, wedgeCollapse_comp_cellMap,
      ContinuousMap.id_comp]
    unfold wedgeCollapseData
    rw [dif_pos t.2]

theorem wedgeIncl_wedgeCollapse_cellMap (n : ℕ) (S : Type) (T : Set S) {s : S} (h : s ∈ T) :
    (wedgeIncl n S T).comp ((wedgeCollapse n S T).comp
        (Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s))
      = Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s := by
  rw [wedgeCollapse_comp_cellMap]
  unfold wedgeCollapseData
  rw [dif_pos h, wedgeIncl_comp_cellMap]

/-! ## The finite reduction -/

/-- Every point of the wedge is the base point or lies in an open cell. -/
theorem eq_wB_or_mem_cellInterior (n : ℕ) (S : Type) (x : Work.Serre.Wedge.wX n S) :
    x = Work.Serre.Wedge.wB n S ∨
      ∃ s : S, x ∈ Work.RatHurewicz.cellInterior n PUnit S (Work.Serre.Wedge.wF n S) s := by
  by_cases h : x ∈ Work.Serre.Wedge.wV n S
  · right
    rw [Work.Serre.Wedge.wV, Set.mem_iUnion] at h
    exact h
  · left
    have h' : x ∈ (Work.Serre.Wedge.wV n S)ᶜ := h
    rw [Work.Serre.Wedge.wV_compl] at h'
    exact Set.mem_singleton_iff.mp h'

/-- The round trip through the collapse fixes the points in the `T`-part. -/
theorem wedgeIncl_wedgeCollapse_eq_self (n : ℕ) (S : Type) (T : Set S) {x : Work.Serre.Wedge.wX n S}
    (hx : x = Work.Serre.Wedge.wB n S ∨
      ∃ s ∈ T, x ∈ Work.RatHurewicz.cellInterior n PUnit S (Work.Serre.Wedge.wF n S) s) :
    wedgeIncl n S T (wedgeCollapse n S T x) = x := by
  rcases hx with hx | ⟨s, hs, hxs⟩
  · rw [hx, wedgeCollapse_apply_wB, wedgeIncl_apply_wB]
  · rw [Work.RatHurewicz.cellInterior, Set.mem_image] at hxs
    obtain ⟨u, -, rfl⟩ := hxs
    have h := congrFun (congrArg DFunLike.coe (wedgeIncl_wedgeCollapse_cellMap n S T hs)) u
    simpa only [ContinuousMap.comp_apply] using h

theorem piMapN_wCellClass (n : ℕ) (S : Type) (T : Set S) (t : ↥T) :
    Work.Serre.piMapN (wedgeIncl n S T) (n + 2) (Work.Serre.Wedge.wB n ↥T)
        (wCellClass ↥T t)
      = wCellClass S t.1 := by
  show Quotient.mk _
      (Work.StemsB.genLoopMap (wedgeIncl n S T) (n + 2)
        (⟨wCellCube ↥T t, wCellCube_boundary ↥T t⟩ :
          Ω^ (Fin (n + 2)) (Work.Serre.Wedge.wX n ↥T) (Work.Serre.Wedge.wB n ↥T)))
    = Quotient.mk _
      (⟨wCellCube S t.1, wCellCube_boundary S t.1⟩ :
        Ω^ (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))
  congr 1

/-- **The cell classes generate `π_{n+2}` of the wedge, for an arbitrary index type.** -/
theorem wedge_generate (n : ℕ) (S : Type)
    (β : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S)) :
    β ∈ Subgroup.closure (Set.range (wCellClass S)) := by
  classical
  refine Quotient.inductionOn β (fun p => ?_)
  set T : Set S := {s : S |
    (Set.range p.1 ∩ Work.RatHurewicz.cellInterior n PUnit S (Work.Serre.Wedge.wF n S) s).Nonempty}
    with hTdef
  have hTfin : T.Finite :=
    Work.AttachPush.finite_meets_cellInterior n PUnit S (Work.Serre.Wedge.wF n S)
      (isCompact_range p.1.continuous)
  letI : Fintype ↥T := hTfin.fintype
  set q : Ω^ (Fin (n + 2)) (Work.Serre.Wedge.wX n ↥T) (Work.Serre.Wedge.wB n ↥T) :=
    Work.StemsB.genLoopMap (wedgeCollapse n S T) (n + 2) p with hq
  have hq_apply : ∀ y, q y = wedgeCollapse n S T (p y) := fun y =>
    Work.StemsB.genLoopMap_apply (wedgeCollapse n S T) (n + 2) p y
  have hmem : ∀ y, p y = Work.Serre.Wedge.wB n S ∨
      ∃ s ∈ T, p y ∈ Work.RatHurewicz.cellInterior n PUnit S (Work.Serre.Wedge.wF n S) s := by
    intro y
    rcases eq_wB_or_mem_cellInterior n S (p y) with h | ⟨s, hs⟩
    · exact Or.inl h
    · refine Or.inr ⟨s, ?_, hs⟩
      rw [hTdef]
      exact ⟨p.1 y, ⟨y, rfl⟩, hs⟩
  have hround : Work.StemsB.genLoopMap (wedgeIncl n S T) (n + 2) q = p := by
    apply GenLoop.ext
    intro y
    rw [Work.StemsB.genLoopMap_apply, hq_apply]
    exact wedgeIncl_wedgeCollapse_eq_self n S T (hmem y)
  obtain ⟨F, hF⟩ := Work.Serre.piMapN_monoidHom (wedgeIncl n S T) (n + 2)
    (Work.Serre.Wedge.wB n ↥T)
  have hle : Subgroup.closure (Set.range (wCellClass ↥T)) ≤
      Subgroup.comap F (Subgroup.closure (Set.range (wCellClass S))) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rw [Subgroup.mem_comap]
      obtain ⟨t, rfl⟩ := hy
      show F (wCellClass ↥T t) ∈ Subgroup.closure (Set.range (wCellClass S))
      rw [hF, piMapN_wCellClass]
      exact Subgroup.subset_closure (Set.mem_range_self t.1)
    | one => rw [Subgroup.mem_comap, map_one]; exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      rw [Subgroup.mem_comap] at iha ihb ⊢
      rw [map_mul]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      rw [Subgroup.mem_comap] at iha ⊢
      rw [map_inv]
      exact Subgroup.inv_mem _ iha
  have hqmem : Quotient.mk _ q ∈ Subgroup.closure (Set.range (wCellClass ↥T)) :=
    wedge_finite_generate_pi n ↥T (Quotient.mk _ q)
  have htarget := hle hqmem
  rw [Subgroup.mem_comap] at htarget
  rw [hF] at htarget
  have hβ : Work.Serre.piMapN (wedgeIncl n S T) (n + 2) (Work.Serre.Wedge.wB n ↥T)
      (Quotient.mk _ q) = Quotient.mk _ p := by
    show Quotient.mk _ (Work.StemsB.genLoopMap (wedgeIncl n S T) (n + 2) q) = Quotient.mk _ p
    rw [hround]
  rwa [hβ] at htarget


end

end Work.StemsB
