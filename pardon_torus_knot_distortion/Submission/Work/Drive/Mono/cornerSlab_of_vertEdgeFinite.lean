import Mathlib
import Submission.Work.Drive.Mono.Geom2Defs
import Submission.Work.Drive.Mono.BoxGenE

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

/-- **The thin-slab estimate.**  If `z` lies on the box sphere of level `s` (`boxNorm c σ z = s`)
and its `σ 2`-coordinate is *extremal* (`|z (σ 2) − c (σ 2)| = boxSide 2 · s`), then the slab
functional at `z` is bounded below by `boxSide 2 · s` minus the tilt error
`‖v − shiftVσ σ 1‖ · (boxSide 0 + boxSide 1 + boxSide 2) · s` minus `|u|` — the tilt error being
estimated by the sup norm of the box coordinates, all of which are at most `boxSide i · s` on the
box sphere.  Hence under the thinness hypothesis the point is strictly outside the closed slab.

The decomposition is `⟪v, z − c⟫ − u = ⟪e, z − c⟫ + ⟪v − e, z − c⟫ − u` with
`e = shiftVσ σ 1`, whose functional is the `σ 2`-coordinate, so `|⟪e, z − c⟫| = boxSide 2 · s`. -/
private theorem abs_slab_gt_of_coord_two {c v z : R3} {σ : Equiv.Perm (Fin 3)} {s u h : ℝ}
    (hzbox : Submission.boxNorm c σ z = s)
    (hσ2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s)
    (hthin : h + |u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ *
        ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s)
      < Submission.boxSide 2 * s) :
    h < |inner ℝ v z - (inner ℝ v c + u)| := by
  -- Every box coordinate of `z − c` is bounded by `boxSide i · s`.
  have hsum : ∑ m : Fin 3, |(z - c) m| ≤
      (Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s := by
    have hcoord : ∀ i : Fin 3, |(z - c) (σ i)| ≤ Submission.boxSide i * s := by
      intro i
      have h1 : Work.Smooth.BoxGeneric.faceNorm c σ i z ≤ s :=
        le_of_le_of_eq (Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i z) hzbox
      rw [Work.Smooth.BoxGeneric.faceNorm_apply] at h1
      have h2 := (div_le_iff₀ (Submission.boxSide_pos i)).mp h1
      rw [PiLp.sub_apply]; linarith
    calc ∑ m : Fin 3, |(z - c) m| = ∑ i : Fin 3, |(z - c) (σ i)| :=
          (Equiv.sum_comp σ (fun m => |(z - c) m|)).symm
      _ ≤ ∑ i : Fin 3, Submission.boxSide i * s := Finset.sum_le_sum fun i _ => hcoord i
      _ = (∑ i : Fin 3, Submission.boxSide i) * s := (Finset.sum_mul _ _ _).symm
      _ = (Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s := by
          rw [Fin.sum_univ_three]
  -- The tilt error is at most `‖v − e‖ · (boxSide 0 + boxSide 1 + boxSide 2) · s`.
  have herr : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| ≤
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ *
        ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s) := by
    have hinner : inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)
        = ∑ m : Fin 3, (z - c) m * (v - Work.BoxShrink.shiftVσ σ 1) m := by
      rw [PiLp.inner_apply]; simp
    rw [hinner]
    calc |∑ m : Fin 3, (z - c) m * (v - Work.BoxShrink.shiftVσ σ 1) m|
        ≤ ∑ m : Fin 3, |(z - c) m| * |(v - Work.BoxShrink.shiftVσ σ 1) m| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => abs_mul _ _
      _ ≤ ∑ m : Fin 3, |(z - c) m| * ‖v - Work.BoxShrink.shiftVσ σ 1‖ :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
            (by simpa [Real.norm_eq_abs] using
              PiLp.norm_apply_le (v - Work.BoxShrink.shiftVσ σ 1) m) (abs_nonneg _)
      _ = (∑ m : Fin 3, |(z - c) m|) * ‖v - Work.BoxShrink.shiftVσ σ 1‖ := by
          rw [Finset.sum_mul]
      _ ≤ ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s) *
          ‖v - Work.BoxShrink.shiftVσ σ 1‖ :=
          mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
      _ = ‖v - Work.BoxShrink.shiftVσ σ 1‖ *
          ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s) := by ring
  -- The functional of `e = shiftVσ σ 1` is the `σ 2`-coordinate.
  have hE : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c) = z (σ 2) - c (σ 2) := by
    rw [PiLp.inner_apply]
    simp [Work.BoxShrink.shiftVσ_apply, PiLp.sub_apply]
  have hdecomp : inner ℝ v z - (inner ℝ v c + u)
      = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) - u := by
    have h1 : inner ℝ v z - (inner ℝ v c + u) = inner ℝ v (z - c) - u := by
      rw [inner_sub_right]; ring
    have h2 : inner ℝ v (z - c) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      rw [← inner_add_left]; congr 1; abel
    rw [h1, h2]
  have htri : |inner ℝ v z - (inner ℝ v c + u)|
      ≥ |inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)|
        - |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| - |u| := by
    rw [hdecomp]
    have h1 : |inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)|
        - |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)|
        ≤ |inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
            + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| := by
      have h := abs_sub_abs_le_abs_sub (inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c))
        (-(inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)))
      rw [sub_neg_eq_add, abs_neg] at h
      exact h
    have h2 := abs_sub_abs_le_abs_sub
      (inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)) u
    linarith
  have hb2 : |inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)| = Submission.boxSide 2 * s := by
    rw [hE]; exact hσ2
  linarith [herr, htri, hthin, hb2]

/-- **The box-edge points of the box sphere in a thin slab are finite.**

`Work.Drive.Mono.VertEdgeFinite` (a conjunct of `Work.Drive.Mono.BoxGenE`) makes the points of the
surface with **two extremal `σ 0`/`σ 1`-coordinates** finite — the points on the *vertical* edge lines
of the box.  Together with the thin-slab estimate

`h + |u| + ‖v - shiftVσ σ 1‖ * ((boxSide 0 + boxSide 1 + boxSide 2) * s) < boxSide 2 * s`

this makes the points of the surface on the **edges of the box sphere inside the closed slab** a
finite set — the `cornerSlab` field of `Work.Drive.Mono.Geom2DataPlus`, hence the finite exceptional
set for clause (c) of `Work.Drive.Mono.JunctionGenC`
(`Work.Drive.Mono.junctionGenC_of_geom2DataPlus`).

Indeed, a point with an extremal `σ 2`-coordinate has `|z (σ 2) - c (σ 2)| = boxSide 2 * s`, hence
`|⟪v,z-c⟫| ≥ (1-ε) boxSide 2 * s - ε (boxSide 0 + boxSide 1) * s` with
`ε = ‖v - shiftVσ σ 1‖`, which exceeds `h + |u|` by the hypothesis: such a point is outside the
closed slab.  The remaining points — those with *both* `σ 0`- and `σ 1`-coordinates extremal — are a
subset of the finite `VertEdgeFinite` locus.

(The companion condition `noCornerFace` — no such point on a slab **face** — is *not* implied by
thinness for the vertical edge points, whose `σ 2`-coordinate is free; it is obtained by choosing the
box level and the window away from the finite set of slab-values of the corner locus, and is a
separate obligation of the data producer.) -/
theorem cornerSlab_of_vertEdgeFinite
    (ψ : Submission.Diffeo) (s u h : ℝ) (c v : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    (hVE : Work.Drive.Mono.VertEdgeFinite ψ c σ s)
    (hv : ‖v‖ = 1)
    (hthin : h + |u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ *
        ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s)
      < Submission.boxSide 2 * s) :
    ({z : LeanEval.KnotTheory.PardonDistortion.R3 |
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧ Submission.boxNorm c σ z = s ∧
          |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧
          (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
            |z (σ j) - c (σ j)| = Submission.boxSide j * s)}).Finite := by
  -- A corner point with an extremal `σ 2`-coordinate lies strictly outside the slab.
  have key : ∀ z : R3, Submission.boxNorm c σ z = s →
      |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s →
      h < |inner ℝ v z - (inner ℝ v c + u)| := fun z hzbox hσ2 =>
    abs_slab_gt_of_coord_two hzbox hσ2 hthin
  -- Hence the only corner points in the slab are the vertical edge points.
  refine hVE.subset ?_
  rintro z ⟨hzcar, hzbox, hzslab, hwit⟩
  obtain ⟨i, j, hij, hi, hj⟩ := hwit
  have hnot2 : i ≠ 2 ∧ j ≠ 2 := by
    constructor
    · intro hi2
      have hσ2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by rw [← hi2]; exact hi
      exact absurd (key z hzbox hσ2) (not_lt.mpr hzslab)
    · intro hj2
      have hσ2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by rw [← hj2]; exact hj
      exact absurd (key z hzbox hσ2) (not_lt.mpr hzslab)
  obtain ⟨hi2, hj2⟩ := hnot2
  have hpairs : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hzcar, hi, hj⟩
  · exact ⟨hzcar, hj, hi⟩

end Work.Drive.Mono
