import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.slabInBelt_of_thin
import Submission.Work.Drive.Mono.junctionGoodAux
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Mono.ae_exists_goodV
import Submission.Work.Drive.Mono.Geom2DataCore_exists
import Submission.Work.Drive.Mono.offK_null

/-!
# The `Geom3Data` extra clauses that are elementary consequences of the tilt data

`Submission/Work/Drive/Mono/geom3Data_exists.lean` must produce, besides the conjuncts of
`Work.Drive.Mono.Geom2Data` (delivered by the fleet's producers), the ten extra conjuncts of
`Work.Drive.Mono.G3Extra`.  This module proves the ones that follow from the *size/thinness* data of
the tilt plus the margin of the vertical-edge locus:

* `g3_slabFn_eq_coord`, `g3_tilt_error_le` — the decomposition of the slab height;
* `g3_traceBand` — conjunct 7 of `Geom2Data` (the trace band);
* `g3_slabInBelt` — `SlabInBelt`, a clause of `G3Extra`;
* `g3_corner_empty` — the surface meets the box sphere inside the closed slab in points with at most
  one extremal coordinate; equivalently the `cornerSlab` set of `Geom2Data` is empty (conjunct 8) and
  the no-corner-face clause of `Geom2DataPlus` holds;
* `g3_edgeFree_of_margin` — `EdgeFree` (a clause of `G3Extra`) from the vertical-edge margin, with the
  distance bound `RF` required only at the surface's *corner* points (the version of
  `Work.Drive.Mono.edgeFree_of_margin` that a producer can actually instantiate);
* `g3_cornerDir_bad_null` — the set of pairs `(h, τ)` at which the corner push direction
  `crossDir v (σ i)` is annihilated by the wall functional is null (finitely many `τ`), which is the
  avoidance the producer needs for the `G3Extra` corner-direction clause;
* `g3_cornerEvent_bad_null` — the set of pairs `(h, τ)` at which a corner event lies on the knot is
  null (finitely many `h`), the avoidance the producer needs for `offK` at the corner events.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-! ## Elementary absolute-value inequalities -/

private theorem g3_abs_sub_le (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  have h2 : (a - b) + b = a := by ring
  have h : |a| ≤ |a - b| + |b| := by
    calc |a| = |(a - b) + b| := by rw [h2]
      _ ≤ |a - b| + |b| := abs_add_le _ _
  linarith

private theorem g3_abs_add_sub_le (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := g3_abs_sub_le a (-b)
  simpa [abs_neg, sub_neg_eq_add] using h

private theorem g3_abs_sub_le_sub (a b : ℝ) : |a| - |b| ≤ |a - b| := g3_abs_sub_le a b

section

/-- The `k`-th coordinate of a point divided by the `k`-th box side is at most its box norm. -/
theorem g3_boxNorm_coord_le (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (k : Fin 3) :
    |z (σ k) - c (σ k)| / Submission.boxSide k ≤ Submission.boxNorm c σ z := by
  rw [Submission.boxNorm]
  fin_cases k <;> simp

end

set_option maxHeartbeats 800000

/-! ## The decomposition of the slab height -/

/-- **The slab height splits into the flat `σ 2`-coordinate and the tilt error.** -/
theorem g3_slabFn_eq_coord (c : R3) (u : ℝ) (v z : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.Drive.Final.slabFn c u v z
      = (z (σ 2) - (c (σ 2) + u))
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
  have h1 : Work.Drive.Final.slabFn c u v z = inner ℝ v (z - c) - u := by
    rw [Work.Drive.Final.slabFn_apply, inner_sub_right]; ring
  have h2 : inner ℝ v (z - c) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
      + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
    rw [← inner_add_left]; congr 1; abel
  have h3 : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c) = z (σ 2) - c (σ 2) := by
    rw [Work.Drive.Mono.inner_shiftVσ_one, PiLp.sub_apply]
  rw [h1, h2, h3]; ring

/-- The tilt error is at most `‖v - e‖` times the distance to the centre. -/
theorem g3_tilt_error_le {v z c : R3} {σ : Equiv.Perm (Fin 3)} {R : ℝ}
    (hz : ‖z - c‖ ≤ R) :
    |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| ≤
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R := by
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

/-! ## The trace band (conjunct 7 of `Geom2Data`) -/

/-- **The trace band**: a point of the surface on the box sphere inside the closed slab has its flat
`σ 2`-coordinate within `2h` of the cutting level. -/
theorem g3_traceBand {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h) :
    ∀ z : R3, Submission.boxNorm c σ z = s → |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h := by
  intro z hznorm hzslab
  have hs0 : 0 ≤ s := by
    by_contra hcon
    push Not at hcon
    have h1 : Submission.boxNorm c σ z < 0 := by rw [hznorm]; exact hcon
    exact absurd (Submission.boxNorm_nonneg c σ z) (not_le.mpr h1)
  have hR : ‖z - c‖ ≤ 5 / 2 * s :=
    Work.Drive.Mono.norm_sub_le_of_boxNorm_eq hs0 hznorm
  have herr := g3_tilt_error_le (v := v) (z := z) (c := c) (σ := σ) hR
  have hkey := g3_slabFn_eq_coord c u v z σ
  have hsplit : z (σ 2) - (c (σ 2) + u)
      = Work.Drive.Final.slabFn c u v z
        - inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
    rw [hkey]; ring
  have h1 : |z (σ 2) - (c (σ 2) + u)|
      ≤ |Work.Drive.Final.slabFn c u v z| +
        |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| := by
    rw [hsplit]; exact abs_sub _ _
  linarith [h1, herr, hzslab, hsize]

/-! ## `SlabInBelt` -/

/-- **`SlabInBelt`**: the surface's part of the closed slab stays strictly inside the box in the
`σ 2`-direction.  From `h + |u| < boxWidth` (hence `2h + |u| < boxSide 2 * s` in the regime of the
producer) and the size condition `‖v - e‖ * (5/2 * s) < h`. -/
theorem g3_slabInBelt {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hs : 0 < s)
    (hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h)
    (hhalf : h < (Submission.boxSide 2 * s - |u|) / 2) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hthin : h + |u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)
      < Submission.boxSide 2 * s := by linarith
  intro z _hzcar hzcl hzslab
  exact Work.Drive.Mono.slabInBelt_of_thin (R := 5 / 2 * s)
    (fun w hw => Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0 hw) hthin z hzcl hzslab

/-! ## The corner locus of the closed slab is empty -/

/-- **No corner of the box sphere lies in the closed slab on the surface**: a point of the surface on
the box sphere inside the closed slab has at most one extremal coordinate.  The `σ 2`-coordinate
cannot be extremal (`SlabInBelt`) and two horizontal coordinates cannot both be extremal
(`EdgeFree`). -/
theorem g3_corner_empty {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hs : 0 < s)
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |Work.Drive.Final.slabFn c u v z| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False := by
  intro z hzcar hznorm hzslab ⟨i, j, hij, hi, hj⟩
  rw [Work.Drive.Final.slabFn_apply] at hzslab
  have hzcl : z ∈ closure (Submission.PBox s c σ) := by
    rw [Work.Drive.Mono.closure_PBox_eq hs c σ]
    intro k
    have h := g3_boxNorm_coord_le c σ z k
    rw [hznorm] at h
    have hb := Submission.boxSide_pos k
    rw [div_le_iff₀ hb] at h
    rwa [mul_comm] at h
  rcases eq_or_ne i 2 with hi2 | hi2
  · -- the `σ 2`-coordinate is extremal: this contradicts `SlabInBelt`
    have h2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by rw [← hi2]; exact hi
    exact absurd h2 (ne_of_lt (hbelt z hzcar hzcl hzslab))
  · rcases eq_or_ne j 2 with hj2 | hj2
    · have h2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by rw [← hj2]; exact hj
      exact absurd h2 (ne_of_lt (hbelt z hzcar hzcl hzslab))
    · -- two horizontal coordinates are extremal: `EdgeFree`
      have hlt := hEF z hzcar hznorm ⟨i, j, hij, hi, hj⟩
      linarith

/-! ## `EdgeFree` from the vertical-edge margin -/

/-- **`EdgeFree` from the vertical-edge margin**, with the distance bound `RF` required only at the
surface's corner points (the version a producer can instantiate: the corners are the points with two
extremal coordinates).  The proof is that of `Work.Drive.Mono.edgeFree_of_margin`. -/
theorem g3_edgeFree_of_margin {ψ : Submission.Diffeo} {s u h RF mE : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)}
    (hRF : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → ‖z - c‖ ≤ RF)
    (hedge : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (hver : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF < mE)
    (hhor : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF < Submission.boxSide 2 * s - |u|) :
    Work.Drive.Mono.EdgeFree ψ s c σ u v h := by
  intro z hz _hbox hext
  obtain ⟨i, j, hij, hi, hj⟩ := hext
  have hdecomp : Work.Drive.Final.slabFn c u v z
      = (z (σ 2) - (c (σ 2) + u))
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) :=
    g3_slabFn_eq_coord c u v z σ
  have hbound : |z (σ 2) - (c (σ 2) + u)| - ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF
      ≤ |inner ℝ v z - (inner ℝ v c + u)| := by
    have hds : inner ℝ v z - (inner ℝ v c + u)
        = (z (σ 2) - (c (σ 2) + u))
          + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      rw [← Work.Drive.Final.slabFn_apply]; exact g3_slabFn_eq_coord c u v z σ
    rw [hds]
    have h1 : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)|
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖ := abs_real_inner_le_norm _ _
    have h2 : ‖z - c‖ ≤ RF := hRF z hz ⟨i, j, hij, hi, hj⟩
    have h3 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h4 := g3_abs_add_sub_le (z (σ 2) - (c (σ 2) + u))
      (inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c))
    linarith
  by_cases h2 : i = 2 ∨ j = 2
  · have hz2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by
      rcases h2 with hh | hh
      · rw [hh] at hi; exact hi
      · rw [hh] at hj; exact hj
    have hbase : Submission.boxSide 2 * s - |u| ≤ |z (σ 2) - (c (σ 2) + u)| := by
      have h5 := g3_abs_sub_le (z (σ 2) - c (σ 2)) u
      rw [show z (σ 2) - c (σ 2) - u = z (σ 2) - (c (σ 2) + u) by ring, hz2] at h5
      exact h5
    linarith [hbound, hbase, hhor]
  · simp only [not_or] at h2
    obtain ⟨hi2, hj2⟩ := h2
    have hpairs : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmE := hedge z hz hi hj
      linarith [hbound, hmE, hver]
    · have hmE := hedge z hz hj hi
      linarith [hbound, hmE, hver]

/-! ## The bad sets of the corner clauses

The two null sets that the producer needs for the `G3Extra` corner-direction clause and for `offK` at
the corner events are proved in their own modules (they are delegated statements, not part of this
file's elementary content):

* `Work.Drive.Mono.g3_corner_dir_bad_null` (`Submission/Work/Drive/Mono/g3_corner_dir_bad_null.lean`);
* `Work.Drive.Mono.g3_corner_event_bad_null`
  (`Submission/Work/Drive/Mono/g3_corner_event_bad_null.lean`).
-/

end

end Work.Drive.Mono
