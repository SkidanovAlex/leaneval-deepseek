import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.homotopyExcision
import Submission.Work.RatHurewicz.compressRel_cellDisk_compl_centre
import Submission.Work.RatHurewicz.AttachPush.PushOff
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology unitInterval

namespace Work.RatHurewicz

/-- **Attaching `(n+2)`-cells to `Y` does not change the homotopy groups in degrees `≤ n`**, in
compression form: the pair `(attachCells n Y ι f, range (attachIncl n Y ι f))` is `(n+1)`-connected,
i.e. every map of pairs `(I^d, ∂I^d) → (Y', range attachIncl)` with `d ≤ n+1` is homotopic, relative
to `∂I^d`, into `range (attachIncl n Y ι f)`.  Route (Hatcher, Lemma 4.10 and Corollary 4.12,
"push the cube off the cells"), using `d ≤ n+1 < n+2`: the cell-part of a map `I^d → Y'` lifts into
`cellDisk n` and the boundary of the domain maps off the cells' interiors; (i) *general position*:
after a sufficiently fine subdivision of the cube, a map that is linear on the cells of the
subdivision (using convexity of the disc) has its image in a finite union of affine subspaces of
dimension `≤ d < n+2`, so it misses a point of a given cell; (ii) *push-off*: the radial retraction
of a punctured cell onto its boundary sphere fixes the sphere pointwise, hence descends to `Y'`, so
a map missing a point of a cell can be deformed into the complement of that cell's interior;
iterating over the cells met by the image and finally pushing the outer collars onto the boundary
spheres gives the compression.  Note that no connectivity hypothesis on `Y` is needed and `ι` is
arbitrary; Blakers–Massey does not apply directly (it needs an open triad).  The local input (the
punctured disc pair is `(n+1)`-connected) is `Work.RatHurewicz.compressRel_cellDisk_compl_centre`
(proved, importable). -/
theorem compressRel_attachCells_range (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel (Work.RatHurewicz.attachCells n Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) d := by
  intro d hd
  intro g hg
  -- step 1: general position: homotope `g` (relative to the boundary) off the cell centres
  obtain ⟨g₁, H₁, h₁0, h₁bd, h₁1, havoid⟩ :=
    Work.AttachPush.exists_homotopy_avoids_cellOrigins (d := d) n Y ι f hd g hg
  -- step 2: push the (punctured) cells onto their boundary spheres
  obtain ⟨H₂, h₂0, h₂A, h₂1⟩ :=
    Work.RatHurewicz.exists_pushOff_homotopy (X := ICube d) n Y ι f g₁ havoid
  -- `g₁` still maps the boundary into the range of `attachIncl`
  have hg₁ : ∀ x, x ∈ Cube.boundary (Fin d) → g₁ x ∈ Set.range (attachIncl n Y ι f) := by
    intro x hx
    rw [← h₁1 x, h₁bd x hx]
    exact hg x hx
  -- the concatenated homotopy
  set Gfun : ICube d × I → attachCells n Y ι f := fun p =>
    if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then H₁ (p.1, clampI (2 * (p.2 : ℝ)))
    else H₂ (p.1, clampI (2 * (p.2 : ℝ) - 1)) with Gfun_def
  have hGcont : Continuous Gfun := by
    rw [Gfun_def]
    refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact H₁.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact H₂.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
    · intro p hp
      have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
      have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
        have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
        rw [h2', clampI_zero']
      rw [h1, h2, h₁1, h₂0]
  refine ⟨⟨Gfun, hGcont⟩, ?_, ?_, ?_⟩
  · -- the homotopy starts at `g`
    intro x
    change (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then H₁ (x, clampI (2 * (((0 : I)) : ℝ)))
      else H₂ (x, clampI (2 * (((0 : I)) : ℝ) - 1))) = g x
    rw [if_pos (by norm_num), show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero']
    exact h₁0 x
  · -- the homotopy is relative to the boundary
    intro x hx t
    change (if (2 : ℝ) * (t : ℝ) ≤ 1 then H₁ (x, clampI (2 * (t : ℝ)))
      else H₂ (x, clampI (2 * (t : ℝ) - 1))) = g x
    by_cases hle : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [if_pos hle]
      exact h₁bd x hx _
    · rw [if_neg hle, h₂A x (hg₁ x hx)]
      exact (h₁1 x).symm.trans (h₁bd x hx 1)
  · -- the homotopy ends in the range of `attachIncl`
    intro x
    change (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then H₁ (x, clampI (2 * (((1 : I)) : ℝ)))
      else H₂ (x, clampI (2 * (((1 : I)) : ℝ) - 1))) ∈ Set.range (attachIncl n Y ι f)
    rw [if_neg (by norm_num : ¬ (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1),
      show 2 * (((1 : I)) : ℝ) - 1 = 1 by norm_num, clampI_one']
    exact h₂1 x

end Work.RatHurewicz
