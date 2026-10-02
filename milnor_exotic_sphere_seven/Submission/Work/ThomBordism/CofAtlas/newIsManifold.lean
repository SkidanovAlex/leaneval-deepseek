import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The corrected chart structure on the coframed level set is a `C^∞` manifold

`Work.ThomBordism.CofAtlas.newChartedSpace D` puts on the coframed level set `D.S.Pre` the charts
`newChart D x = ((lvlChart x) ≫ₕ (reflectMap x)).restr (src x)`: the `Lvl` chart at `x`, possibly
post-composed with the reflection `reflOph` of the half-space, restricted to the connected source
`src x`.  This file proves that these charts are pairwise `C^∞`-compatible, i.e. that
`D.S.Pre` is a `C^∞` manifold for the new chart structure (with the same model `𝓡∂ 9`).

The mathematical content is only that both operations used to build `newChart` preserve the
`C^∞` structure groupoid:

* `reflectMap D x` is either the reflection `reflOph` (which is `C^∞`, `reflOph_mem_contDiffGroupoid`)
  or the identity, so it lies in the groupoid `G9 = contDiffGroupoid ∞ (𝓡∂ 9)`;
* the `Lvl` charts are pairwise compatible, because the `Lvl` chart structure is a `C^∞` manifold
  (`Lvl.Setup.instIsManifold`);
* `a ↦ a.restr s` for `s` open is groupoid-preserving (`ClosedUnderRestriction`), and the
  transition of two restrictions of groupoid-compatible charts is again in the groupoid
  (`restr_trans_restr_mem`).

Note that this is the *smoothness* half of `Work.ThomBordism.levelSet_positiveAtlas_of_coframing`;
positivity of the transition determinants is not proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold ModelWithCorners
open Work.PTGeometric

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- The `C^∞` structure groupoid of the half-space model `𝓡∂ 9`. -/
abbrev G9 : StructureGroupoid (EuclideanHalfSpace 9) :=
  contDiffGroupoid ((⊤ : ENat) : WithTop ENat) (modelWithCornersEuclideanHalfSpace 9)

/-! ## A groupoid lemma for restrictions -/

/-- **The transition of two restrictions of groupoid-compatible open partial homeomorphisms is in
the groupoid.**  If `a.symm ≫ₕ b ∈ G` and `s ⊆ a.source` is open, then
`(a.restr s).symm ≫ₕ (b.restr t) ∈ G` for any open `t`: restricting `a` and `b` only shrinks the
sources, and the groupoid is closed under restriction. -/
theorem restr_trans_restr_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {G : StructureGroupoid Y} [ClosedUnderRestriction G]
    {a b : OpenPartialHomeomorph X Y} {s t : Set X}
    (hab : a.symm.trans b ∈ G) (hs : IsOpen s) (hsa : s ⊆ a.source)
    (ht : IsOpen t) :
    (a.restr s).symm.trans (b.restr t) ∈ G := by
  have hs' : IsOpen (a '' s) := a.isOpen_image_of_subset_source hs hsa
  have h1 := OpenPartialHomeomorph.restr_symm_trans (e := a) (e' := b.restr t) hs hs' hsa
  have h2 := OpenPartialHomeomorph.symm_trans_restr (e := b) (s := t) (e' := a) ht
  have hu_eq : (a.symm.trans (OpenPartialHomeomorph.ofSet t ht)).source
      = a.target ∩ a.symm ⁻¹' t := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source,
      OpenPartialHomeomorph.symm_source]
  have hu : IsOpen (a.target ∩ a.symm ⁻¹' t) := hu_eq ▸
    (a.symm.trans (OpenPartialHomeomorph.ofSet t ht)).open_source
  have h3 : (a.symm.trans b).restr (a.target ∩ a.symm ⁻¹' t) ∈ G :=
    closedUnderRestriction' hab hu
  have h4 : ((a.symm.trans b).restr (a.target ∩ a.symm ⁻¹' t)).restr (a '' s) ∈ G :=
    closedUnderRestriction' h3 hs'
  have h5 := h2.restr (a '' s)
  exact (G.mem_iff_of_eqOnSource (Setoid.trans h1 h5)).mpr h4

/-! ## The two charts whose composition is a `newChart` -/

/-- **The reflection used at `x` lies in the `C^∞` groupoid.** -/
theorem reflectMap_mem (D : Cof k n M) (x : D.S.Pre) : D.reflectMap x ∈ G9 := by
  by_cases h : D.flipBool x
  · rw [reflectMap_of_flip D x h]
    exact reflOph_mem_contDiffGroupoid
  · rw [reflectMap_of_not_flip D x (Bool.eq_false_iff.mpr h)]
    exact StructureGroupoid.id_mem G9

/-- The source of `(lvlChart x) ≫ₕ (reflectMap x)` is the source of the `Lvl` chart. -/
theorem bChart_source (D : Cof k n M) (x : D.S.Pre) :
    ((D.lvlChart x).trans (D.reflectMap x)).source = (D.lvlChart x).source := by
  rw [OpenPartialHomeomorph.trans_source, reflectMap_source, preimage_univ, inter_univ]

/-- **The `Lvl` charts are `C^∞`-compatible**, because the `Lvl` chart structure is a `C^∞`
manifold. -/
theorem lvlChart_trans_mem (D : Cof k n M) (x y : D.S.Pre) :
    (D.lvlChart x).symm.trans (D.lvlChart y) ∈ G9 := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace (S := D.S)
  haveI : IsManifold (𝓡∂ 9) ∞ D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instIsManifold (S := D.S)
  have hx : D.lvlChart x ∈ atlas (EuclideanHalfSpace 9) D.S.Pre := ⟨x, rfl⟩
  have hy : D.lvlChart y ∈ atlas (EuclideanHalfSpace 9) D.S.Pre := ⟨y, rfl⟩
  exact StructureGroupoid.compatible G9 hx hy

/-- **The charts `(lvlChart x) ≫ₕ (reflectMap x)` are `C^∞`-compatible.** -/
theorem bChart_symm_trans_mem (D : Cof k n M) (x y : D.S.Pre) :
    ((D.lvlChart x).trans (D.reflectMap x)).symm.trans
      ((D.lvlChart y).trans (D.reflectMap y)) ∈ G9 := by
  have hgx : (D.reflectMap x) ∈ G9 := reflectMap_mem D x
  have hgy : (D.reflectMap y) ∈ G9 := reflectMap_mem D y
  have hl : (D.lvlChart x).symm.trans (D.lvlChart y) ∈ G9 := lvlChart_trans_mem D x y
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rw [OpenPartialHomeomorph.trans_assoc]
  rw [← OpenPartialHomeomorph.trans_assoc (D.lvlChart x).symm (D.lvlChart y) (D.reflectMap y)]
  exact G9.trans (G9.symm hgx) (G9.trans hl hgy)

/-! ## The corrected chart structure is a `C^∞` manifold -/

theorem newIsManifold
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) :
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
      Work.ThomBordism.CofAtlas.newChartedSpace D
    IsManifold (modelWithCornersEuclideanHalfSpace 9) ((⊤ : ENat) : WithTop ENat) D.S.Pre := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.ThomBordism.CofAtlas.newChartedSpace D
  haveI : HasGroupoid D.S.Pre
      (contDiffGroupoid ((⊤ : ENat) : WithTop ENat)
        (modelWithCornersEuclideanHalfSpace 9)) :=
    ⟨fun {e e'} he he' => by
      rcases he with ⟨x, rfl⟩
      rcases he' with ⟨y, rfl⟩
      have hsa : D.src x ⊆ ((D.lvlChart x).trans (D.reflectMap x)).source := by
        rw [bChart_source]
        exact D.src_subset_chartSource x
      exact restr_trans_restr_mem (G := G9) (bChart_symm_trans_mem D x y)
        (D.src_open x) hsa (D.src_open y)⟩
  exact IsManifold.mk' (𝓡∂ 9) ((⊤ : ENat) : WithTop ENat) D.S.Pre

end

end Work.ThomBordism.CofAtlas
