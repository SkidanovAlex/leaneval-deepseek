import Mathlib
import Submission.Work.Drive.EpsFormSphere.OpenTiltedRegion

/-!
# The frontier of the tilted swept ball, closed wall vs. open wall

The open region of the tilted sweep at the level `lam` is

`PBox s c σ \ (tiltedSlabClosed a v h ∩ {ℓ ≤ lam})`  (`a = ⟪v,c⟫ + u`)

whereas the *count* (`encard_frontier_tiltedSweptBall_lt_min`) and the in-flight slicing lemma are
stated with the open wall `{ℓ < lam}`.  The two regions differ exactly by the 1-dimensional wall
trace `PBox ∩ tiltedSlabClosed ∩ {ℓ = lam}`, and this module proves that the two sets have the
*same frontier*:

`frontier (PBox \ (slab ∩ {ℓ ≤ lam})) = frontier (PBox \ (slab ∩ {ℓ < lam}))`.

This is what lets the trace (and hence the counting) be transported between the two spellings of
the sweep.

## The mathematics

Write `A` for the box (an **open** set), `B = slab ∩ {ℓ < lam}` for the removed region of the
open-wall spelling, and `D = slab ∩ {ℓ = lam}`, so that the closed-wall removed region is
`B ∪ D = slab ∩ {ℓ ≤ lam}`, and put `P = A \ B`, `Q = A \ (B ∪ D) = P \ D`.

Since `Q ⊆ P`, we have `closure Q ⊆ closure P` and `closure Qᶜ ⊇ closure Pᶜ`, and `frontier` is
interchange for the two claims

* `closure P = closure Q`, for which it suffices that `A ∩ D ⊆ closure Q` — a point of `A` with
  `ℓ = lam` is approached by points of `A` with `ℓ > lam` (a nonzero continuous functional is
  locally surjective), and those miss both `B` and `D`;
* `closure Pᶜ = closure Qᶜ`, for which it suffices that `A ∩ D ⊆ closure (Aᶜ ∪ B)` — a point of
  `A` in the slab with `ℓ = lam` is approached, inside the slab, by points of `A` with `ℓ < lam`;
  move along a vector `w` orthogonal to `v` with `ℓ w ≠ 0` (possible because `ℓ v = 0` and
  `ℓ ≠ 0`), which keeps `⟪v,·⟫` — hence the slab condition — unchanged.

Both are the content of the two "geometric" lemmas below; the purely topological lemma
`frontier_sdiff_sdiff_eq` packages the argument, and the target theorem is its instantiation.
-/

namespace Work.Drive.EpsFormSphere

open Set
open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## The purely topological step -/

/-- **Frontier of a set, versus frontier after removing a `D` contained in its closure (both ways).**

If `A \ B ⊆ closure (A \ (B ∪ D))` and `(A \ (B ∪ D))ᶜ ⊆ closure ((A \ B)ᶜ)`, then removing
`D` from `A \ B` does not change the frontier.  The two hypotheses say exactly that `A \ B` and
`A \ (B ∪ D)` have the same closure, and that their complements have the same closure. -/
theorem frontier_sdiff_sdiff_eq {X : Type*} [TopologicalSpace X] {A B D : Set X}
    (h₁ : A \ B ⊆ closure (A \ (B ∪ D)))
    (h₂ : (A \ (B ∪ D))ᶜ ⊆ closure ((A \ B)ᶜ)) :
    frontier (A \ B) = frontier (A \ (B ∪ D)) := by
  have hP : closure (A \ B) = closure (A \ (B ∪ D)) :=
    le_antisymm (closure_minimal h₁ isClosed_closure)
      (closure_mono (Set.sdiff_subset_sdiff (subset_refl A) subset_union_left))
  have hmono : (A \ B)ᶜ ⊆ (A \ (B ∪ D))ᶜ := by
    intro x hx hxQ
    exact hx ⟨hxQ.1, fun h => hxQ.2 (Or.inl h)⟩
  have hQ : closure (A \ B)ᶜ = closure (A \ (B ∪ D))ᶜ :=
    le_antisymm (closure_mono hmono) (closure_minimal h₂ isClosed_closure)
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure, hP, hQ]

/-! ## The two geometric inputs -/

/-- A nonzero continuous linear functional on `R3` takes a nonzero value. -/
theorem exists_apply_ne_zero {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : ∃ w : R3, ℓ w ≠ 0 := by
  by_contra h
  exact hℓ (ContinuousLinearMap.ext fun w => by
    simpa using not_not.mp (not_exists.mp h w))

/-- A nonzero continuous linear functional on `R3` is positive on a vector of norm `< ε`. -/
theorem exists_norm_lt_apply_pos {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : R3, ‖w‖ < ε ∧ 0 < ℓ w := by
  obtain ⟨w₀, hw₀⟩ := exists_apply_ne_zero hℓ
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, 0 < ℓ w₁ := by
    rcases lt_or_gt_of_ne hw₀ with hneg | hpos
    · exact ⟨-w₀, by simpa using hneg⟩
    · exact ⟨w₀, hpos⟩
  set ρ : ℝ := ε / (2 * (‖w₁‖ + 1)) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  refine ⟨ρ • w₁, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hρ, div_mul_eq_mul_div, div_lt_iff₀]
    · nlinarith [norm_nonneg w₁, hε]
    · positivity
  · rw [map_smul, smul_eq_mul]
    exact mul_pos hρpos hw₁

/-- **A point of the box can be moved a little so as to strictly increase the value of a nonzero
functional `ℓ`.** -/
theorem exists_dist_lt_mem_PBox_apply_gt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {y : R3} (hy : y ∈ Submission.PBox s c σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : R3, dist z y < ε ∧ z ∈ Submission.PBox s c σ ∧ ℓ y < ℓ z := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.isOpen_iff.mp (Work.Topology.SphereSlicing.isOpen_PBox s c σ) y hy
  obtain ⟨w, hw, hwpos⟩ := exists_norm_lt_apply_pos hℓ (lt_min hε hδpos)
  refine ⟨y + w, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hw (min_le_left _ _)
  · refine hδ (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hw (min_le_right _ _)
  · rw [map_add]
    linarith

/-- **Inside the box, a point of the tilted slab with `ℓ = lam` is approached by points of the slab
with `ℓ < lam`.**  The motion is along a vector `w` with `⟪v,w⟫ = 0` (so the slab condition is
untouched) and `ℓ w < 0` (so `ℓ` drops below `lam`); such a `w` exists because `v ≠ 0`,
`ℓ v = 0` and `ℓ ≠ 0`. -/
theorem exists_dist_lt_mem_PBox_tiltedSlab_apply_lt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {a h lam : ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓ : ℓ ≠ 0) {y : R3} (hy : y ∈ Submission.PBox s c σ)
    (hyslab : y ∈ Work.Drive.EpsForm.tiltedSlabClosed a v h) (hyℓ : ℓ y = lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : R3, dist z y < ε ∧ z ∈ Submission.PBox s c σ ∧
      z ∈ Work.Drive.EpsForm.tiltedSlabClosed a v h ∧ ℓ z < lam := by
  have hv2 : ‖v‖ ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  obtain ⟨w₀, hw₀⟩ := exists_apply_ne_zero hℓ
  have hproj : inner ℝ v (w₀ - (inner ℝ v w₀ / ‖v‖ ^ 2) • v) = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hprojℓ : ℓ (w₀ - (inner ℝ v w₀ / ‖v‖ ^ 2) • v) = ℓ w₀ := by
    rw [map_sub, map_smul, smul_eq_mul, hℓv, mul_zero, sub_zero]
  obtain ⟨w, hwv, hwneg⟩ : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 := by
    rcases lt_or_gt_of_ne hw₀ with hneg | hpos
    · exact ⟨_, hproj, by rw [hprojℓ]; exact hneg⟩
    · refine ⟨-(w₀ - (inner ℝ v w₀ / ‖v‖ ^ 2) • v), ?_, ?_⟩
      · rw [inner_neg_right, hproj, neg_zero]
      · rw [map_neg, hprojℓ]
        exact neg_lt_zero.mpr hpos
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.isOpen_iff.mp (Work.Topology.SphereSlicing.isOpen_PBox s c σ) y hy
  have hmin : 0 < min ε δ := lt_min hε hδpos
  set ρ : ℝ := min ε δ / (2 * (‖w‖ + 1)) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρnorm : ρ * ‖w‖ < min ε δ := by
    rw [hρ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w‖ + 1))]
    nlinarith [norm_nonneg w, hmin]
  refine ⟨y + ρ • w, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
    exact lt_of_lt_of_le hρnorm (min_le_left _ _)
  · refine hδ (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
    exact lt_of_lt_of_le hρnorm (min_le_right _ _)
  · have hinner : inner ℝ v (y + ρ • w) = inner ℝ v y := by
      rw [inner_add_right, inner_smul_right, hwv, mul_zero, add_zero]
    simpa [Work.Drive.EpsForm.tiltedSlabClosed, hinner] using hyslab
  · rw [map_add, map_smul, smul_eq_mul, hyℓ]
    have : ρ * ℓ w < 0 := mul_neg_of_pos_of_neg hρpos hwneg
    linarith

/-! ## The target -/

/-- **The frontier of the tilted swept ball is the same with the closed wall `{ℓ ≤ lam}` and with the
open wall `{ℓ < lam}`.**  The two sets differ by the wall trace `PBox ∩ tiltedSlabClosed ∩ {ℓ = lam}`,
which lies in the frontier of both. -/
theorem frontier_tiltedSweptBall_eq {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} (σ : Equiv.Perm (Fin 3))
    (u : ℝ) {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) {lam : ℝ}
    (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    frontier (Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y ≤ lam})) =
      frontier (Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y < lam})) := by
  set W : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h with hW
  have hUnion : (W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam})
      = W ∩ {y : R3 | ℓ y ≤ lam} := by
    ext y
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_of_lt h2⟩
      · exact ⟨h1, le_of_eq h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le h2 with h2' | h2'
      · exact Or.inl ⟨h1, h2'⟩
      · exact Or.inr ⟨h1, h2'⟩
  -- A point of the box in the wall is a limit point of the open-wall region ...
  have h₁ : Submission.PBox s c σ \ (W ∩ {y : R3 | ℓ y < lam}) ⊆
      closure (Submission.PBox s c σ \
        ((W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam}))) := by
    rintro y ⟨hyA, hyB⟩
    by_cases hy : y ∈ Submission.PBox s c σ \
        ((W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam}))
    · exact subset_closure hy
    · have hylam : ℓ y = lam := by
        have hmem : y ∈ (W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam}) := by
          by_contra hcon
          exact hy ⟨hyA, hcon⟩
        rcases hmem with h | h
        · exact absurd ⟨h.1, h.2⟩ hyB
        · exact h.2
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨z, hzε, hzA, hzgt⟩ := exists_dist_lt_mem_PBox_apply_gt hℓne hyA hε
      rw [hylam] at hzgt
      refine ⟨z, ⟨hzA, ?_⟩, ?_⟩
      · rintro (⟨-, hlt⟩ | ⟨-, heq⟩)
        · exact absurd hlt (not_lt.mpr (le_of_lt hzgt))
        · exact absurd (heq ▸ rfl : ℓ z = lam) (ne_of_gt hzgt)
      · rwa [dist_comm]
  -- ... and the complement of the closed-wall region is a subset of the closure of the complement of
  -- the open-wall region.
  have h₂ : (Submission.PBox s c σ \
        ((W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam})))ᶜ ⊆
      closure ((Submission.PBox s c σ \ (W ∩ {y : R3 | ℓ y < lam}))ᶜ) := by
    intro y hy
    by_cases hyA : y ∈ Submission.PBox s c σ
    · have hmem : y ∈ (W ∩ {y : R3 | ℓ y < lam}) ∪ (W ∩ {y : R3 | ℓ y = lam}) := by
        by_contra hcon
        exact hy ⟨hyA, hcon⟩
      rcases hmem with h | h
      · exact subset_closure (by intro hyAB; exact hyAB.2 h)
      · rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨z, hzε, hzA, hzslab, hzlt⟩ :=
          exists_dist_lt_mem_PBox_tiltedSlab_apply_lt hv hℓv hℓne hyA h.1 h.2 hε
        refine ⟨z, ?_, ?_⟩
        · intro hzAB
          exact hzAB.2 ⟨hW ▸ hzslab, hzlt⟩
        · rwa [dist_comm]
    · apply subset_closure
      intro hyAB
      exact hyA hyAB.1
  have key := frontier_sdiff_sdiff_eq (A := Submission.PBox s c σ)
    (B := W ∩ {y : R3 | ℓ y < lam}) (D := W ∩ {y : R3 | ℓ y = lam}) h₁ h₂
  rw [hUnion] at key
  rw [hW] at key
  exact key.symm

end

end Work.Drive.EpsFormSphere
