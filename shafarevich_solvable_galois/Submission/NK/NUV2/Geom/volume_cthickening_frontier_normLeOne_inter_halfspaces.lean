/-
# Boundary layer of the frontier of the truncated fundamental cone, cut by half-spaces

This file proves `NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces`: the
`ε`-thickening of the frontier of
`fundamentalCone.normLeOne K ∩ {x | ∀ i, f i x < 0}`
has volume `O(ε)`.  This is the Minkowski-content (boundary-layer) input of the lattice-point
asymptotics `NK.NUV2.Geom.latticeCount_sub_volume_isBigO`.

The set is the intersection of the truncated fundamental cone with the open cone cut out by
finitely many continuous linear functionals `f i`, so its frontier is contained in the union of
the frontier of the truncated cone and of the finitely many hyperplanes `f i = 0`:

* the cone part is bounded by `normLeOne_frontier_cthickening_volume`;
* each hyperplane part is bounded by `volume_cthickening_hyperplane_le`, the standard
  "slab" bound `vol(cthickening ε (ker g) ∩ B(0,R)) ≤ C ε` for a nonzero continuous linear
  functional `g`.

Both inputs are proved elsewhere in the workspace
(`Submission/Work/NUV2/Geom/normLeOne_frontier_cthickening_volume.lean` and
`Submission/Work/NUV2/Geom/volume_cthickening_hyperplane_le.lean`).
-/
import Mathlib
import Submission.NK.NUV2.Geom.TubeDefs
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne
import Submission.NK.NUV2.Geom.volume_cthickening_hyperplane_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Geom

set_option autoImplicit false
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Classical

/-- For a finite family of sets, the `ε`-thickening of the union is contained in the union of the
`ε`-thickenings.  (`Metric.cthickening_union` gives this with equality for a binary union; this is
the `Finset`/`Fintype` version needed to pass from a union of hyperplanes to the individual ones.) -/
theorem cthickening_biUnion_subset {α : Type*} [PseudoEMetricSpace α] {ι : Type*}
    (ε : ℝ) (s : Finset ι) (t : ι → Set α) :
    Metric.cthickening ε (⋃ i ∈ s, t i) ⊆ ⋃ i ∈ s, Metric.cthickening ε (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, Metric.cthickening_union]
      exact Set.union_subset_union (Set.Subset.refl _) ih

/-- `Fintype` version of `cthickening_biUnion_subset`. -/
theorem cthickening_iUnion_subset {α : Type*} [PseudoEMetricSpace α] {ι : Type*} [Fintype ι]
    (ε : ℝ) (t : ι → Set α) :
    Metric.cthickening ε (⋃ i, t i) ⊆ ⋃ i, Metric.cthickening ε (t i) := by
  classical
  have h := cthickening_biUnion_subset (α := α) ε (Finset.univ : Finset ι) t
  simpa using h

theorem volume_cthickening_frontier_normLeOne_inter_halfspaces
    (K : Type*) [Field K] [NumberField K]
    (ι : Type*) [Fintype ι] (f : ι → mixedSpace K →L[ℝ] ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε
        (frontier (fundamentalCone.normLeOne K ∩ {x | ∀ i, f i x < 0})))
        ≤ ENNReal.ofReal (c * ε) := by
  classical
  by_cases hzero : ∃ i, f i = 0
  · -- If some functional vanishes, the open cone `U` is empty and so is the thickening.
    obtain ⟨i0, hi0⟩ := hzero
    refine ⟨1, one_pos, fun ε hε hε1 => ?_⟩
    have hU : {x : mixedSpace K | ∀ i, f i x < 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      simpa [hi0] using h i0
    rw [hU, Set.inter_empty, frontier_empty, Metric.cthickening_empty, measure_empty]
    simp
  · push_neg at hzero
    -- The boundedness constant for the truncated cone.
    obtain ⟨cP, hcP0, hP⟩ := volume_cthickening_frontier_normLeOne K
    obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.mp
      (NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K).closure
    set R : ℝ := max R0 1 + 1 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    -- The slab constants, one for each `f i`.
    choose Ci hCi using fun i => volume_cthickening_hyperplane_le (g := f i) (hzero i) R hRpos
    set c : ℝ := cP + ∑ i, Ci i with hcdef
    have hsum0 : 0 ≤ ∑ i, Ci i := Finset.sum_nonneg fun i _ => (hCi i).1.le
    have hc0 : 0 < c := by rw [hcdef]; linarith
    refine ⟨c, hc0, fun ε hε hε1 => ?_⟩
    set P : Set (mixedSpace K) := fundamentalCone.normLeOne K with hPdef
    set U : Set (mixedSpace K) := {x | ∀ i, f i x < 0} with hUdef
    -- Step 1: the frontier of an intersection is inside the union of the frontiers.
    have hsub : frontier (P ∩ U) ⊆ frontier P ∪ frontier U := by
      intro x hx
      rcases (Set.mem_union x (frontier P ∩ closure U) (closure P ∩ frontier U)).mp
        (frontier_inter_subset P U hx) with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    -- Step 2: the frontier of the open cone is inside the union of the hyperplanes `f i = 0`.
    have hUsub : frontier U ⊆ ⋃ i, {x : mixedSpace K | f i x = 0} := by
      intro x hx
      rw [Set.mem_iUnion]
      by_contra hcon
      push_neg at hcon
      have hxcl : x ∈ closure U := hx.1
      have hle : ∀ i, f i x ≤ 0 := by
        intro i
        have hcl : IsClosed {y : mixedSpace K | f i y ≤ 0} :=
          isClosed_le (f i).continuous continuous_const
        have hsub' : U ⊆ {y : mixedSpace K | f i y ≤ 0} := fun y hy => (hy i).le
        exact (hcl.closure_subset_iff).mpr hsub' hxcl
      have hopen : IsOpen U := by
        have heq : U = ⋂ i, {y : mixedSpace K | f i y < 0} := by
          ext y; simp [hUdef, Set.mem_iInter]
        rw [heq]
        exact isOpen_iInter_of_finite fun i => isOpen_lt (f i).continuous continuous_const
      have hxU : x ∈ U := fun i => lt_of_le_of_ne (hle i) (hcon i)
      have hxint : x ∈ interior U := by rw [hopen.interior_eq]; exact hxU
      exact hx.2 hxint
    -- Step 3: the closed thickening is bounded (it lies near the bounded frontier of `P`).
    have hbdd : Bornology.IsBounded (frontier (P ∩ U)) :=
      ((NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K).closure).subset
        (Set.Subset.trans frontier_subset_closure
          (closure_mono (by rw [hPdef]; exact Set.inter_subset_left)))
    have hcompact : IsCompact (frontier (P ∩ U)) :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_frontier, hbdd⟩
    have hbounded : Metric.cthickening ε (frontier (P ∩ U)) ⊆ Metric.closedBall 0 R := by
      intro x hx
      rw [hcompact.cthickening_eq_biUnion_closedBall hε.le] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨y, hyE, hxy⟩ := hx
      have hy : ‖y‖ ≤ R0 := hR0 y (Set.Subset.trans frontier_subset_closure
        (closure_mono (by rw [hPdef]; exact Set.inter_subset_left)) hyE)
      have hxy' : dist x y ≤ ε := Metric.mem_closedBall.mp hxy
      rw [Metric.mem_closedBall]
      calc dist x 0 = ‖x‖ := dist_zero_right x
        _ = ‖(x - y) + y‖ := by rw [show (x - y) + y = x by abel]
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
        _ = dist x y + ‖y‖ := by rw [dist_eq_norm]
        _ ≤ ε + R0 := by linarith
        _ ≤ max R0 1 + 1 := by
              have h1 : R0 ≤ max R0 1 := le_max_left R0 1
              linarith
        _ = R := by rw [hRdef]
    -- Step 4: reduction to the cone part plus the hyperplane parts, all inside the ball.
    have h1 : Metric.cthickening ε (frontier (P ∩ U))
        ⊆ Metric.cthickening ε (frontier P) ∪
          (Metric.cthickening ε (frontier U) ∩ Metric.closedBall 0 R) := by
      intro x hx
      have hx' : x ∈ Metric.cthickening ε (frontier P) ∪ Metric.cthickening ε (frontier U) := by
        rw [← Metric.cthickening_union]
        exact (Metric.cthickening_subset_of_subset ε hsub) hx
      rcases (Set.mem_union x (Metric.cthickening ε (frontier P))
        (Metric.cthickening ε (frontier U))).mp hx' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hbounded hx⟩
    have h2 : Metric.cthickening ε (frontier U) ∩ Metric.closedBall 0 R
        ⊆ ⋃ i, (Metric.cthickening ε ({x : mixedSpace K | f i x = 0}) ∩
            Metric.closedBall 0 R) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx3 : x ∈ Metric.cthickening ε (⋃ i, {y : mixedSpace K | f i y = 0}) :=
        (Metric.cthickening_subset_of_subset ε hUsub) hx1
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        ((cthickening_iUnion_subset ε (fun i => {y : mixedSpace K | f i y = 0})) hx3)
      exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hx2⟩⟩
    -- Step 5: assemble the estimate.
    calc volume (Metric.cthickening ε (frontier (P ∩ U)))
        ≤ volume (Metric.cthickening ε (frontier P) ∪
            (Metric.cthickening ε (frontier U) ∩ Metric.closedBall 0 R)) :=
          measure_mono h1
      _ ≤ volume (Metric.cthickening ε (frontier P))
            + volume (Metric.cthickening ε (frontier U) ∩ Metric.closedBall 0 R) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (cP * ε) + ∑ i, ENNReal.ofReal (Ci i * ε) := by
          refine add_le_add ?_ ?_
          · rw [hPdef]; exact hP ε hε hε1
          · refine (measure_mono h2).trans ?_
            refine (measure_iUnion_le _).trans ?_
            rw [tsum_fintype]
            exact Finset.sum_le_sum fun i _ => (hCi i).2 ε hε hε1
      _ = ENNReal.ofReal (c * ε) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
            (f := fun i => Ci i * ε) (fun i _ => mul_nonneg (hCi i).1.le hε.le)]
          have hp : 0 ≤ cP * ε := mul_nonneg hcP0.le hε.le
          have hq : 0 ≤ ∑ i, Ci i * ε :=
            Finset.sum_nonneg fun i _ => mul_nonneg (hCi i).1.le hε.le
          rw [← ENNReal.ofReal_add hp hq]
          congr 1
          rw [hcdef, ← Finset.sum_mul]
          ring

end NK.NUV2.Geom
