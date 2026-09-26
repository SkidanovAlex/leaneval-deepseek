import Submission.Work.PinchCounted.Pardon3

/-!
# The residual's hypotheses are satisfiable: a concrete, if degenerate, witness

`Work.PinchCounted.PardonLemma3` is an implication, so it is worth recording that its hypotheses are
not vacuous.  This module provides

* `slicedSphere_of_disjoint` — a sphere disjoint from the surface admits the **empty slicing**
  (`Work.BoxShrink.SlicedSphere` is a `Prop`-valued datum about the trace, so the empty family is a
  legitimate witness when the trace is empty).  This is a small but reusable certificate that the
  general-position datum is not empty;
* `farCentre`, a box centre at distance `100` from the torus in the `z`-direction;
* `boxNorm_farCentre_ge` — every point of the standard torus has box norm `≥ 99/2 > 1` in that box;
* `pardonLemma3_nonvacuous` — a configuration at which `0 < s`, the sphere is sliced *and* Pardon's
  double-bubble inequality `|S ∩ β| + 2 |D ∩ β| < I(F,β)` holds for the standard `(2,3)` curve,
  with the conclusion `BubbleHalf` holding as well.

The witness is degenerate (the box is disjoint from the surface, so the region inside the box is
empty): it certifies satisfiability of the residual's *hypotheses*, not of its interesting content.
The interesting content is certified, non-vacuously, by the instances of the conclusion in `Api.lean`
and `Discs.lean` (laminar disc coverings of the slice) and by the refutation of the conclusion at
`s = 3/2` (`Excluded.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **A sphere disjoint from the surface admits the empty slicing.** -/
theorem slicedSphere_of_disjoint {S : Set R3} (h : P.carrier ∩ S = ∅) :
    Work.BoxShrink.SlicedSphere P S :=
  ⟨{ ι := Empty
     fintype := Fintype.ofIsEmpty
     c := fun i => Empty.elim i
     simple := fun i => Empty.elim i
     disjoint := fun i => Empty.elim i
     mem := fun i => Empty.elim i
     covers := fun γ hγ => absurd (show γ 0 ∈ (∅ : Set R3) from by
        rw [← h]; exact ⟨γ.mem 0, hγ 0⟩) (Set.notMem_empty (γ 0))
     disc := fun i => Empty.elim i
     disc_inj := fun i => Empty.elim i
     disc_boundary := fun i => Empty.elim i
     disc_mem := fun i => Empty.elim i
     rank := fun i => Empty.elim i
     inside := fun i => Empty.elim i
     inside_subset := fun i => Empty.elim i
     covers_interior := fun i => Empty.elim i }⟩

/-! ## A box far from the torus -/

/-- The centre of a box at distance `100` from the standard torus in the `z`-direction. -/
def farCentre : R3 := WithLp.toLp 2 (fun m : Fin 3 => if m = 2 then 100 else 0)

@[simp] theorem farCentre_apply (m : Fin 3) : farCentre m = if m = 2 then 100 else 0 := rfl

@[simp] theorem farCentre_two : farCentre 2 = 100 := by simp [farCentre]

/-- Every point of the standard torus has `z`-coordinate of modulus at most `1`. -/
theorem standard_abs_three (y : R3) (hy : y ∈ Work.CoreTopology.standard.carrier) : |y 2| ≤ 1 := by
  rw [Work.CoreTopology.ParamTorus.mem_carrier_iff] at hy
  obtain ⟨θ, φ, rfl⟩ := hy
  rw [Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_two]
  exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- **Every point of the standard torus has box norm at least `99/2` in the far box.** -/
theorem boxNorm_farCentre_ge (y : R3) (hy : y ∈ Work.CoreTopology.standard.carrier) :
    99 / 2 ≤ Submission.boxNorm farCentre (Equiv.refl (Fin 3)) y := by
  have hz : |y 2| ≤ 1 := standard_abs_three y hy
  have h99 : (99 : ℝ) ≤ |y 2 - 100| := by
    have h2 : |y 2 - 100| = |100 - y 2| := by rw [abs_sub_comm]
    rw [h2]
    have h3 : |(100 : ℝ)| - |y 2| ≤ |100 - y 2| := abs_sub_abs_le_abs_sub 100 (y 2)
    norm_num at h3
    linarith
  have hden : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := Submission.rpow_two_thirds_le_two
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : 99 / 2 ≤ 99 / (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have hone : 1 / 2 ≤ 1 / (2 : ℝ) ^ (2 / 3 : ℝ) :=
      one_div_le_one_div_of_le hpos hden
    calc (99 : ℝ) / 2 = 99 * (1 / 2) := by ring
      _ ≤ 99 * (1 / (2 : ℝ) ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
      _ = 99 / (2 : ℝ) ^ (2 / 3 : ℝ) := by ring
  have h2 : 99 / (2 : ℝ) ^ (2 / 3 : ℝ) ≤ |y 2 - 100| / (2 : ℝ) ^ (2 / 3 : ℝ) :=
    div_le_div_of_nonneg_right h99 (le_of_lt hpos)
  have h3 : |y 2 - 100| / (2 : ℝ) ^ (2 / 3 : ℝ) =
      |y 2 - farCentre (Equiv.refl (Fin 3) 2)| / Submission.boxSide 2 := by
    simp [Submission.boxSide_two]
  rw [h3] at h2
  refine le_trans h1 (le_trans h2 ?_)
  rw [Submission.boxNorm]
  exact le_max_right _ _

/-- **No point of the standard torus lies in the far box.** -/
theorem not_mem_PBox_farCentre (y : R3) (hy : y ∈ Work.CoreTopology.standard.carrier) :
    y ∉ Submission.PBox 1 farCentre (Equiv.refl (Fin 3)) := by
  rw [Submission.mem_PBox_iff]
  intro h
  have := boxNorm_farCentre_ge y hy
  linarith

/-- The standard torus misses the far box sphere. -/
theorem standard_carrier_inter_sphereSet_farCentre :
    Work.CoreTopology.standard.carrier ∩
        Work.BoxShrink.Core.sphereSet farCentre (Equiv.refl (Fin 3)) 1 = ∅ := by
  ext y
  constructor
  · rintro ⟨hyc, hys⟩
    rw [Work.BoxShrink.Core.mem_sphereSet] at hys
    have := boxNorm_farCentre_ge y hyc
    simp only [Set.mem_empty_iff_false]
    linarith
  · intro h
    exact absurd h (Set.notMem_empty y)

/-! ## The certificate -/

/-- **The hypotheses of `PardonLemma3` are satisfiable.**  At the standard torus with `s = 1`, the
far centre `farCentre`, `σ = refl` and `u = 0`: the level is positive, the box sphere is sliced (it
misses the surface, `slicedSphere_of_disjoint`), Pardon's double-bubble inequality holds for the
standard `(2,3)` curve (both intersections are empty, and `I(F,β) = min 2 3 = 2 > 0`), and the
conclusion holds (the region inside the far box is empty). -/
theorem pardonLemma3_nonvacuous :
    ∃ (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      0 < s ∧
      Work.BoxShrink.SlicedSphere Work.CoreTopology.standard
        (Work.BoxShrink.Core.sphereSet c σ s) ∧
      (Set.encard (Set.range (Work.CoreTopology.standardCurve 2 3).γ ∩
          Work.BoxShrink.Core.sphereSet c σ s)
        + 2 * Set.encard (Set.range (Work.CoreTopology.standardCurve 2 3).γ ∩
          Work.BoxShrink.Core.cutDisc s c σ u)
        < Work.CoreTopology.pardonsI Work.CoreTopology.standard
          (Work.CoreTopology.standardCurve 2 3)) ∧
      Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard s c σ u := by
  refine ⟨1, farCentre, Equiv.refl (Fin 3), 0, by norm_num, ?_, ?_, ?_⟩
  · exact slicedSphere_of_disjoint standard_carrier_inter_sphereSet_farCentre
  · have h1 : Set.range (Work.CoreTopology.standardCurve 2 3).γ ∩
        Work.BoxShrink.Core.sphereSet farCentre (Equiv.refl (Fin 3)) 1 = ∅ := by
      ext y
      constructor
      · rintro ⟨hy, hys⟩
        obtain ⟨t, rfl⟩ := hy
        rw [Work.BoxShrink.Core.mem_sphereSet] at hys
        have := boxNorm_farCentre_ge _ ((Work.CoreTopology.standardCurve 2 3).mem t)
        simp only [Set.mem_empty_iff_false]
        linarith
      · intro h
        exact absurd h (Set.notMem_empty y)
    have h2 : Set.range (Work.CoreTopology.standardCurve 2 3).γ ∩
        Work.BoxShrink.Core.cutDisc 1 farCentre (Equiv.refl (Fin 3)) 0 = ∅ := by
      ext y
      constructor
      · rintro ⟨hy, hyd⟩
        obtain ⟨t, rfl⟩ := hy
        rw [Work.BoxShrink.Core.mem_cutDisc] at hyd
        have := not_mem_PBox_farCentre _ ((Work.CoreTopology.standardCurve 2 3).mem t)
        simp only [Set.mem_empty_iff_false]
        exact this hyd.1
      · intro h
        exact absurd h (Set.notMem_empty y)
    rw [h1, h2, Set.encard_empty]
    rw [Work.CoreTopology.pardonsI_standard 2 3 (by norm_num) (by norm_num) (by decide)]
    norm_num
  · intro h
    obtain ⟨γ, -, hγ⟩ := h
    exact absurd (hγ 0).2 (not_mem_PBox_farCentre (γ 0) (hγ 0).1)

end

end Work.PinchCounted
