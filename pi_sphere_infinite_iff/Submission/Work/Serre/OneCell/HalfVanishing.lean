import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.OneCell.compressRel_oneCellHalf
import Submission.Work.Serre.CellStep.Tools

set_option synthInstance.maxHeartbeats 400000


/-!
# Vanishing of the rational homology of a half-cell and of its preimage

The half `oneCellHalf Y ι f i ε` is a model interval with one endpoint removed: it compresses onto
the point `oneCellHalfPt Y ι f i ε` (`compressRel_oneCellHalf`), and the pair
`(half, {point})` therefore has vanishing relative homology; the exact sequence of the pair with
`H_k(*) = 0` then gives the vanishing of `H_k(half)` in positive degrees.

The same pair of facts, pulled back along a Serre fibration whose fibres are rationally acyclic,
gives the vanishing of `H_k(q⁻¹half)` in degrees `0 < k ≤ N`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- **The rational homology of a half-cell vanishes in positive degrees.** -/
theorem isZero_ratH_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) (ε : Bool) (k : ℕ) (hk : 0 < k) :
    CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥(oneCellHalf Y ι f i ε)) k) := by
  refine Work.Serre.pp_isZero_absH_of_isZero_rel ↥(oneCellHalf Y ι f i ε)
    {x : ↥(oneCellHalf Y ι f i ε) |
      (x : attachOneCells Y ι f) = (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)} k ?hA ?hrel
  ·
    exact isZero_ratH_subsingleton
      (S := {x : ↥(oneCellHalf Y ι f i ε) |
        (x : attachOneCells Y ι f) = (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)})
      (fun a ha b hb => Subtype.ext (ha.trans hb.symm)) ⟨oneCellHalfPt Y ι f i ε, rfl⟩ k hk
  · refine isZero_ppRelH_of_isZero_relChains _ _ k ?_
    exact Work.Serre.isZero_relChains_of_compress
      (fun d => compressRel_oneCellHalf Y ι f i ε d) k

/-- **The rational homology of the preimage of a half-cell vanishes below `N`.** -/
theorem isZero_ratH_preimage_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (N : ℕ)
    (hacyc : ∀ z : attachOneCells Y ι f,
      (∀ k : ℕ, 0 < k → k ≤ N → CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology k)) ∧
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q z))).homology 0 ≅ ModuleCat.of ℚ ℚ))
    (i : ι) (ε : Bool) (k : ℕ) (hk0 : 0 < k) (hkN : k ≤ N) :
    CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥(q ⁻¹' oneCellHalf Y ι f i ε)) k) := by
  classical
  set c : attachOneCells Y ι f := (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)
  refine Work.Serre.pp_isZero_absH_of_isZero_rel ↥(q ⁻¹' oneCellHalf Y ι f i ε)
    {x : ↥(q ⁻¹' oneCellHalf Y ι f i ε) |
      (x : E) ∈ q ⁻¹' ({c} : Set (attachOneCells Y ι f))} k ?hA ?hrel
  · have hset : {x : ↥(q ⁻¹' oneCellHalf Y ι f i ε) |
        (x : E) ∈ q ⁻¹' ({c} : Set (attachOneCells Y ι f))} =
        {x : ↥(q ⁻¹' oneCellHalf Y ι f i ε) | q (x : E) = c} := by
      ext x; simp
    rw [hset]
    have hc : c ∈ oneCellHalf Y ι f i ε := (oneCellHalfPt Y ι f i ε).2
    exact isZero_ratH_of_homeo (homeoSubFibre q hc) k ((hacyc c).1 k hk0 hkN)
  · have hrelZ : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' oneCellHalf Y ι f i ε))
          {x : ↥(q ⁻¹' oneCellHalf Y ι f i ε) |
            (x : E) ∈ q ⁻¹' ({c} : Set (attachOneCells Y ι f))}).homology k) := by
      refine Work.Serre.isZero_relChains_preimage_of_base_compress q hq
        ({c} : Set (attachOneCells Y ι f)) (oneCellHalf Y ι f i ε) ?hW ?hb k
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (oneCellHalfPt Y ι f i ε).2
      · intro d
        have hset : {x : ↥(oneCellHalf Y ι f i ε) |
            (x : attachOneCells Y ι f) ∈ ({c} : Set (attachOneCells Y ι f))} =
            {x : ↥(oneCellHalf Y ι f i ε) |
              (x : attachOneCells Y ι f) =
                (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)} := by
          ext x; simp [c]
        rw [hset]
        exact compressRel_oneCellHalf Y ι f i ε d
    exact isZero_ppRelH_of_isZero_relChains _ _ k hrelZ

end

end Work.Serre.OneCell
