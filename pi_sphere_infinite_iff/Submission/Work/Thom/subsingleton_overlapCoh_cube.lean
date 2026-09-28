import Mathlib
import Submission.Work.Thom.CubeSetup
import Submission.Work.Thom.EucCube
import Submission.Work.Cohomology.subsingleton_relCohomology_of_open_subset

/-!
# The vanishing of the cohomology of the Mayer–Vietoris overlap of the cube cover

This file proves `Work.Thom.subsingleton_overlapCoh_cube`, the vanishing statement needed for the
*overlap* term of the relative Mayer–Vietoris induction computing `H^m(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ)`
(see `Work.Thom.subsingleton_relComplex_cube`).

The overlap of the two halves `pieceTop n W = {last > -1/2}` and `pieceBot n W = {last < 1/2}` of
`W × ↥(euCube (n+1))` is the "thickened" cube `{|last| < 1/2}`.  Splitting off the last coordinate
turns the pair `(overlap, overlap ∩ ∂)` into the product of the interval `(-1/2, 1/2)` with the
pair `(W × ↥(euCube n), W × ∂[-1,1]ⁿ)`, and the interval is simply carried along in the base.
Concretely there is a homeomorphism of pairs

`(↥(pieceTop n W ∩ pieceBot n W), bdrySet) ≅ ((W × ↥(Ioo (-1/2) (1/2))) × ↥(euCube n), euCubeBdry n)`

(`Work.Thom.OverlapCoh.overlapHomeo`, `Work.Thom.OverlapCoh.overlapHomeo_mem_bdry`), so relative
cohomology is invariant under it (`Work.Cohomology.relCohomology_homeomorph_pairs`) and the claim
reduces to the hypothesis `h` with `Z := W × ↥(Ioo (-1/2) (1/2))`.
-/

open CategoryTheory

namespace Work.Thom
namespace OverlapCoh

noncomputable section

/-- The last-coordinate splitting of the overlap, as a map into the product of the open interval
and the `n`-cube. -/
def toProd (n : ℕ) (W : Type) [TopologicalSpace W]
    (y : ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W)) :
    (W × ↥(Set.Ioo (-1/2:ℝ) (1/2))) × ↥(euCube n) :=
  ((y.1.1, ⟨((euCubeSplit n) (y.1.2 : Fin (n+1) → ℝ)).2, by
      have hlt := Cube.abs_last_lt_of_mem_inter y.2
      rw [euCubeSplit_apply, Set.mem_Ioo]
      exact ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2⟩⟩),
   ⟨((euCubeSplit n) (y.1.2 : Fin (n+1) → ℝ)).1, by
      simp only [mem_euCube, euCubeSplit_apply]
      intro i
      exact (mem_euCube.mp y.1.2.2) i.castSucc⟩)

/-- The inverse of `toProd`: reassemble the last coordinate into the cube. -/
def ofProd (n : ℕ) (W : Type) [TopologicalSpace W]
    (q : (W × ↥(Set.Ioo (-1/2:ℝ) (1/2))) × ↥(euCube n)) :
    ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W) :=
  ⟨(q.1.1, ⟨(euCubeSplit n).symm ((q.2 : Fin n → ℝ), (q.1.2 : ℝ)), by
      simp only [mem_euCube, euCubeSplit_symm_apply]
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
        exact abs_le.mpr ⟨by linarith [(Set.mem_Ioo.mp q.1.2.2).1],
                          by linarith [(Set.mem_Ioo.mp q.1.2.2).2]⟩
      · intro j
        rw [Fin.snoc_castSucc]
        exact (mem_euCube.mp q.2.2) j⟩),
   by
    rw [Cube.mem_piece_inter]
    simp only [euCubeSplit_symm_apply, Fin.snoc_last]
    exact Set.mem_Ioo.mp q.1.2.2⟩

/-- **The overlap of the cube cover is a product with an interval.**  Splitting off the last
coordinate identifies the overlap `pieceTop n W ∩ pieceBot n W ⊆ W × ↥(euCube (n+1))` with
`(W × ↥(Ioo (-1/2) (1/2))) × ↥(euCube n)`. -/
def overlapHomeo (n : ℕ) (W : Type) [TopologicalSpace W] :
    ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W) ≃ₜ
      (W × ↥(Set.Ioo (-1/2:ℝ) (1/2))) × ↥(euCube n) where
  toFun := toProd n W
  invFun := ofProd n W
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp only [ofProd, toProd]
      exact (euCubeSplit n).symm_apply_apply (y.1.2 : Fin (n+1) → ℝ)
  right_inv q := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [ofProd, toProd]
        exact congrArg Prod.snd
          ((euCubeSplit n).apply_symm_apply ((q.2 : Fin n → ℝ), (q.1.2 : ℝ)))
    · apply Subtype.ext
      simp only [ofProd, toProd]
      exact congrArg Prod.fst
        ((euCubeSplit n).apply_symm_apply ((q.2 : Fin n → ℝ), (q.1.2 : ℝ)))
  continuous_toFun := by
    have hB : Continuous fun y : ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W) =>
        (euCubeSplit n) (y.1.2 : Fin (n+1) → ℝ) := by fun_prop
    refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_
    · fun_prop
    · exact Continuous.subtype_mk hB.snd _
    · exact Continuous.subtype_mk hB.fst _
  continuous_invFun := by
    have hu : Continuous fun q : (W × ↥(Set.Ioo (-1/2:ℝ) (1/2))) × ↥(euCube n) =>
        (euCubeSplit n).symm ((q.2 : Fin n → ℝ), (q.1.2 : ℝ)) := by fun_prop
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · fun_prop
    · exact Continuous.subtype_mk hu _

/-- The overlap homeomorphism carries the boundary part of the overlap onto the boundary part of
the product. -/
theorem overlapHomeo_mem_bdry (n : ℕ) (W : Type) [TopologicalSpace W]
    (y : ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W)) :
    (y : W × ↥(euCube (n+1))) ∈ Cube.bdrySet (n+1) W ↔
      ((overlapHomeo n W y).2 : Fin n → ℝ) ∈ euCubeBdry n := by
  have hlt := Cube.abs_last_lt_of_mem_inter y.2
  have hiff := euCubeSplit_mem_cubeBdry (y.1.2 : Fin (n+1) → ℝ) hlt
  simp only [Cube.mem_bdrySet, overlapHomeo]
  exact hiff.symm

end

end OverlapCoh

theorem subsingleton_overlapCoh_cube (n : ℕ) (W : Type) [TopologicalSpace W]
    (h : ∀ (Z : Type) [TopologicalSpace Z] (m : ℕ), m < n →
      Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (Z × ↥(Work.Thom.euCube n)))
        {p : Z × ↥(Work.Thom.euCube n) | (p.2 : Fin n → ℝ) ∈ Work.Thom.euCubeBdry n}).homology m))
    (k : ℕ) (hk : k < n) : Subsingleton (Work.Thom.Cube.overlapCoh n W k) := by
  let Z := W × ↥(Set.Ioo (-1/2:ℝ) (1/2))
  have hmodel : Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (Z × ↥(euCube n)))
      {p : Z × ↥(euCube n) | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}).homology k) := h Z k hk
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Cube.pieceTop n W ∩ Cube.pieceBot n W) |
      (y : W × ↥(euCube (n+1))) ∈ Cube.bdrySet (n+1) W}
    {p : Z × ↥(euCube n) | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}
    (OverlapCoh.overlapHomeo n W) (fun y => OverlapCoh.overlapHomeo_mem_bdry n W y) k
  exact Work.Cohomology.subsingleton_of_iso iso.symm hmodel

end Work.Thom
