import Mathlib
import Submission.Work.Serre.Wedge.Defs
import Submission.Work.Serre.Wedge.LES
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.compressRel_cellU
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.simpHomExists
import Submission.Work.Serre.simpHomVanishing
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cover of the wedge of spheres

For `X = Work.Serre.Wedge.wX n ι` (the wedge of `ι` copies of `S^{n+2}`) we use the open cover

* `wOuter n ι = Work.Serre.cellU (wF n ι) (1/2)` — the complement of the closed balls of radius
  `1/2` around the cell centres ("outer part": the base point and the outer shells), and
* `wV n ι` — the union of the open cells ("inner part").

`wOuter` and `wV` are open, they cover `X`, and their intersection is the disjoint union of the
open shells `{1/2 < ‖x‖ < 1}`.  The pair `(wOuter, {base point})` has the compression property
(`Work.Serre.CellStep.compressRel_cellU`), so `H_m(wOuter, {base point}) = 0` and hence
`H_m(wOuter) = 0` in positive degrees.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option maxHeartbeats 8000000

namespace Work.Serre.Wedge

noncomputable section

/-- The "outer part" of the wedge: the complement of the closed balls of radius `1/2` around the
cell centres. -/
abbrev wOuter (n : ℕ) (ι : Type) : Set (wX n ι) := Work.Serre.cellU (wF n ι) (1 / 2)

theorem isOpen_wOuter (n : ℕ) (ι : Type) : IsOpen (wOuter n ι) :=
  Work.Serre.isOpen_cellU (wF n ι) (by norm_num)

/-- The inner part `cellV f 1` is the union of the open cells. -/
theorem cellV_one_eq_wV (n : ℕ) (ι : Type) : Work.Serre.cellV (wF n ι) 1 = wV n ι := by
  have hset : Work.Serre.cellOpenBallSet n 1 = Work.RatHurewicz.cellInner n := rfl
  rw [Work.Serre.cellV, Work.Serre.cellOpenBallImg, wV, hset]
  rfl

theorem wOuter_union_wV (n : ℕ) (ι : Type) : wOuter n ι ∪ wV n ι = Set.univ := by
  rw [wOuter, ← cellV_one_eq_wV]
  exact Work.Serre.cellU_union_cellV (wF n ι) (by norm_num)

theorem wOuter_inter_wV (n : ℕ) (ι : Type) :
    wOuter n ι ∩ wV n ι = Work.Serre.cellShellImg (wF n ι) (1 / 2) 1 := by
  rw [wOuter, ← cellV_one_eq_wV]
  exact Work.Serre.cellU_inter_cellV (wF n ι) (by norm_num) (by norm_num)

theorem wB_mem_wOuter (n : ℕ) (ι : Type) : wB n ι ∈ wOuter n ι := by
  rw [wOuter, Work.Serre.cellU, Set.mem_compl_iff]
  exact Set.disjoint_right.mp (Work.Serre.disjoint_cellBallImg_range (wF n ι) (by norm_num))
    (by rw [range_attachIncl_wF]; exact Set.mem_singleton _)

/-- The base point of the wedge, as a point of the outer part. -/
def wB' (n : ℕ) (ι : Type) : ↥(wOuter n ι) := ⟨wB n ι, wB_mem_wOuter n ι⟩

/-- The old part inside the outer part is the single point `wB'`. -/
theorem range_attachIncl_eq_wB' (n : ℕ) (ι : Type) :
    {x : ↥(wOuter n ι) |
        (x : wX n ι) ∈ Set.range (Work.RatHurewicz.attachIncl n PUnit ι (wF n ι))}
      = {wB' n ι} := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff, range_attachIncl_wF]
  constructor
  · intro hx
    exact Subtype.ext (Set.mem_singleton_iff.mp hx)
  · intro hx
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hx)

/-- The compression property in the `HomotopicRel` form. -/
theorem homotopicRel_of_compressRel {Y : Type} [TopologicalSpace Y] {A : Set Y} {d : ℕ}
    (h : Work.RatHurewicz.CompressRel Y A d) (f : C(Work.Stems.Cubical.IC d, Y))
    (hf : ∀ t, t ∈ Cube.boundary (Fin d) → f t ∈ A) :
    ∃ g : C(Work.Stems.Cubical.IC d, Y), (∀ t, g t ∈ A) ∧
      ContinuousMap.HomotopicRel f g (Cube.boundary (Fin d)) := by
  obtain ⟨G, hG0, hGfix, hG1⟩ := h f hf
  refine ⟨⟨fun t => G (t, 1), G.continuous.comp (continuous_id.prodMk continuous_const)⟩,
    fun t => hG1 t, ⟨ContinuousMap.HomotopyWith.mk
      { toContinuousMap :=
          ⟨fun z : unitInterval × Work.Stems.Cubical.IC d => G (z.2, z.1),
            G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
        map_zero_left := fun x => hG0 x
        map_one_left := fun x => rfl }
      (fun t x hx => hGfix x hx t)⟩⟩

/-- **The compression property of the pair `(wOuter, {base point})`**, inherited from the radial
push-off of the punctured cells of `Work.Serre.CellStep.compressRel_cellU`. -/
theorem compressRel_wOuter (n : ℕ) (ι : Type) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥(wOuter n ι)
      {x : ↥(wOuter n ι) |
        (x : wX n ι) ∈ Set.range (Work.RatHurewicz.attachIncl n PUnit ι (wF n ι))} d :=
  Work.Serre.CellStep.compressRel_cellU (n := n) (Γ := PUnit) (ι := ι) (f := wF n ι)
    (ρ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) d

/-- **The compression criterion for relative homology** (the `CompressRel`-form of
`Work.Serre.SerreE2b`, avoiding the unfolding of that definition). -/
theorem isZero_relChains_of_compressRel {X : Type} [TopologicalSpace X] (A : Set X) (N : ℕ)
    (h : ∀ d ≤ N, Work.RatHurewicz.CompressRel X A d) (m : ℕ) (hm : m ≤ N) :
    IsZero ((Work.Cohomology.relChains (TopCat.of X) A).homology m) := by
  have hc : Work.Serre.CompressHyp X A N := h
  obtain ⟨H⟩ := Work.Serre.simpHom_of_compress (X := X) (A := A) N hc
  exact Work.Serre.simpHomVanishing H m hm

/-- **The pair `(wOuter, {base point})` has vanishing relative homology in every degree.** -/
theorem isZero_relChains_wOuter (n : ℕ) (ι : Type) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(wOuter n ι))
      {x : ↥(wOuter n ι) |
        (x : wX n ι) ∈ Set.range (Work.RatHurewicz.attachIncl n PUnit ι (wF n ι))}).homology m) :=
  isZero_relChains_of_compressRel _ m (fun d _ => compressRel_wOuter n ι d) m le_rfl

/-- **The pair `(wOuter, {base point})` has vanishing relative homology in every degree**, in the
singleton form. -/
theorem isZero_relChains_wOuter' (n : ℕ) (ι : Type) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(wOuter n ι)) {wB' n ι}).homology m) := by
  have h := isZero_relChains_wOuter n ι m
  rwa [range_attachIncl_eq_wB' n ι] at h

/-- **The outer part of the wedge has vanishing homology in positive degrees.** -/
theorem isZero_homology_wOuter (n : ℕ) (ι : Type) (k : ℕ) (hk : 1 ≤ k) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(wOuter n ι))).homology k) :=
  isZero_homology_of_isZero_rel_of_isZero (TopCat.of ↥(wOuter n ι)) {wB' n ι} k
    (isZero_homology_singleton (TopCat.of ↥(wOuter n ι)) (wB' n ι) k hk)
    (isZero_relChains_wOuter' n ι k)

end

end Work.Serre.Wedge
