import Mathlib
import Submission.Work.Step2.Defs

/-!
# The two halves of Pardon's double bubble are frontiers of the half-boxes

Pardon's Step 2 replaces the box sphere `∂PBox s c σ` by the *double bubble* obtained by cutting the
sphere along the plane `{y (σ 2) = c (σ 2) + u}` and gluing in the flat disc `cutDisc s c σ u` (the
trace of that plane in the box).  The two halves of the bubble are `halfAbove s c σ u` (the closed
upper cap together with the disc) and `halfBelow s c σ u`.

This file shows that `halfAbove` really *is* a sphere: it is the topological boundary of the solid
upper half-box `upperBody s c σ u = PBox s c σ ∩ {c (σ 2) + u < y (σ 2)}`:

  `halfAbove s c σ u = frontier (upperBody s c σ u)`.

The proof is pure point-set topology of `ℝ³`; the only geometric input is the transversality of the
cutting plane to the box sphere in the `σ 2` direction, i.e. `|u| < boxSide 2 * s` (`hu`), which says
that the plane does not touch the top face of the box.  Concretely, writing

* `A = upperBody s c σ u = {y | boxNorm c σ y < s ∧ c (σ 2) + u < y (σ 2)}` (open, so it is its own
  interior), and
* `C = {y | boxNorm c σ y ≤ s ∧ c (σ 2) + u ≤ y (σ 2)}` (closed),

one has `A ∪ halfAbove = C` (`upperBody_union_halfAbove`), hence `closure A ⊆ A ∪ halfAbove`, while
conversely every point of `halfAbove` is a limit of points of `A`
(`halfAbove_subset_closure_upperBody`):
points of `A` are pushed up in the `σ 2`-direction and radially towards the centre `c`.

The membership reformulations `mem_upperBody_of_boxNorm`/`mem_halfAbove_of_boxNorm` are the bridge between
the set-theoretic vocabulary of `Defs.lean` and the box norm of `Submission/Box.lean`.

The file is self-contained (it only imports the vocabulary module `Step2.Defs`), but the two analytic
steps are also available as standalone, verified lemmas:
`Work.Step2.closedBox_subset_closure_PBox` and `Work.Step2.mem_closure_PBox_inter_upperHalf`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## Coordinates and the box norm -/

/-- The box norm controls each coordinate from above. -/
theorem abs_sub_le_of_boxNorm_le {y : R3} (h : Submission.boxNorm c σ y ≤ s) (i : Fin 3) :
    |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have h2 : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
    rw [Submission.boxNorm] at h
    rcases max_le_iff.mp h with ⟨h3, h4⟩
    rcases max_le_iff.mp h3 with ⟨h5, h6⟩
    fin_cases i
    · exact h5
    · exact h6
    · exact h4
  rw [div_le_iff₀ (Submission.boxSide_pos i)] at h2
  simpa [mul_comm] using h2

/-- The strict version, i.e. the coordinate form of membership in the open box. -/
theorem abs_sub_lt_of_boxNorm_lt {y : R3} (h : Submission.boxNorm c σ y < s) (i : Fin 3) :
    |y (σ i) - c (σ i)| < Submission.boxSide i * s :=
  Submission.mem_PBox.mp ((Submission.mem_PBox_iff s c σ y).mpr h) i

/-! ## The membership of the two sets in coordinates -/

/-- The upper half-box is the part of the box above the cutting plane. -/
theorem mem_upperBody_of_boxNorm {y : R3} :
    y ∈ upperBody s c σ u ↔ Submission.boxNorm c σ y < s ∧ c (σ 2) + u < y (σ 2) := by
  simp only [upperBody, Set.mem_inter_iff, Submission.mem_PBox_iff,
    Work.BoxShrink.Core.mem_upperHalf]

/-- The half `H₁` of the double bubble: the sphere part of `halfAbove` is exactly the box sphere,
and the flat part is the trace of the cutting plane in the *open* box. -/
theorem mem_halfAbove_of_boxNorm {y : R3} :
    y ∈ halfAbove s c σ u ↔
      (Submission.boxNorm c σ y = s ∧ c (σ 2) + u ≤ y (σ 2)) ∨
        (Submission.boxNorm c σ y < s ∧ y (σ 2) = c (σ 2) + u) := by
  simp only [halfAbove, closedUpperCap, Work.BoxShrink.Core.cutDisc, Set.mem_union,
    Set.mem_inter_iff, Work.BoxShrink.Core.mem_sphereSet, Work.BoxShrink.Core.mem_cutPlane,
    Submission.mem_PBox_iff, Set.mem_ofPred_eq]

/-- **The half-box together with the corresponding half of the double bubble is the closed box
truncated by the half-space.**  This is the decomposition of the closed upper half-box into its
interior (`= upperBody`) and its boundary (`= halfAbove`). -/
theorem upperBody_union_halfAbove :
    upperBody s c σ u ∪ halfAbove s c σ u =
      {y : R3 | Submission.boxNorm c σ y ≤ s ∧ c (σ 2) + u ≤ y (σ 2)} := by
  ext y
  rw [mem_union, mem_upperBody_of_boxNorm, mem_halfAbove_of_boxNorm]
  constructor
  · rintro (⟨hb, hlt⟩ | ⟨hb, hle⟩ | ⟨hb, heq⟩)
    · exact ⟨le_of_lt hb, le_of_lt hlt⟩
    · exact ⟨le_of_eq hb, hle⟩
    · exact ⟨le_of_lt hb, le_of_eq heq.symm⟩
  · rintro ⟨hb, hu'⟩
    rcases lt_or_eq_of_le hb with h | h
    · rcases lt_or_eq_of_le hu' with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (Or.inr ⟨h, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h, hu'⟩)

/-! ## The three elementary facts about `upperBody` and `halfAbove` -/

/-- The upper half-box is open: it is the trace of the open box in an open half-space. -/
theorem isOpen_upperBody : IsOpen (upperBody s c σ u) :=
  (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
    (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)))

/-- The union of the half-box and the half of the bubble is closed: by
`upperBody_union_halfAbove` it is the closed box truncated by a closed half-space. -/
theorem isClosed_upperBody_union_halfAbove :
    IsClosed (upperBody s c σ u ∪ halfAbove s c σ u) := by
  rw [upperBody_union_halfAbove]
  exact IsClosed.inter
    (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const)
    (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)))

/-- The half of the bubble is disjoint from the half-box it bounds: no point is both on the
boundary of the box (or on the cutting plane) and in the open box above the plane. -/
theorem disjoint_upperBody_halfAbove : Disjoint (upperBody s c σ u) (halfAbove s c σ u) := by
  rw [Set.disjoint_left]
  rintro y hyA hyH
  rw [mem_upperBody_of_boxNorm] at hyA
  rw [mem_halfAbove_of_boxNorm] at hyH
  rcases hyH with ⟨heq, -⟩ | ⟨-, heq⟩
  · rw [heq] at hyA; exact lt_irrefl s hyA.1
  · rw [heq] at hyA; exact lt_irrefl _ hyA.2

/-! ## Limits of the open box -/

/-- **Every point of the closed box is a limit of points of the open box**: shrink towards the
centre.  (The converse `closure (PBox s c σ) ⊆ {y | boxNorm c σ y ≤ s}` is
`Work.PinchLemma3.ClosedDiscA.closure_PBox_subset_closedBox`.) -/
theorem mem_closure_PBox_of_boxNorm_le (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    {y : R3} (hy : Submission.boxNorm c σ y ≤ s) :
    y ∈ closure (Submission.PBox s c σ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / (2 * (dist y c + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hδhalf : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδdist : δ ≤ ε / (2 * (dist y c + 1)) := by rw [hδdef]; exact min_le_right _ _
  rw [dist_eq_norm] at hδdist
  refine ⟨(1 - δ) • y + δ • c, ?_, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    have hcoord : ((1 - δ) • y + δ • c) (σ i) - c (σ i) = (1 - δ) * (y (σ i) - c (σ i)) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hnonneg : (0 : ℝ) ≤ 1 - δ := by linarith
    rw [hcoord, abs_mul, abs_of_nonneg hnonneg]
    have h1 := abs_sub_le_of_boxNorm_le hy i
    have hbs : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
    have h2 : (1 - δ) * |y (σ i) - c (σ i)| ≤ (1 - δ) * (Submission.boxSide i * s) :=
      mul_le_mul_of_nonneg_left h1 hnonneg
    nlinarith [h2, hbs, hδpos]
  · rw [dist_eq_norm]
    have hsub : y - ((1 - δ) • y + δ • c) = δ • (y - c) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδpos)]
    have h1 : δ * ‖y - c‖ ≤ δ * (‖y - c‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hδpos)
    have h2 : δ * (‖y - c‖ + 1) ≤ ε / 2 := by
      have hstep := mul_le_mul_of_nonneg_right hδdist (by positivity : (0 : ℝ) ≤ ‖y - c‖ + 1)
      have heq : ε / (2 * (‖y - c‖ + 1)) * (‖y - c‖ + 1) = ε / 2 := by field_simp
      linarith [hstep, heq.le]
    linarith

/-! ## Limits of the open upper half-box -/

/-- **A point of the closed box lying on the cutting plane is a limit of points of the open box
strictly above it.**  The hypothesis `|u| < boxSide 2 * s` says that the `σ 2`-coordinate of `y`
is never the binding coordinate of the box norm, so there is room to move `y` up by a small
`δ · (|u| + 1)` in the `σ 2`-direction while shrinking it towards the centre `c` by the same `δ`:
the resulting point is still in the open box, is strictly above the plane, and tends to `y`. -/
theorem mem_closure_PBox_inter_upperHalf_of_mem_cutPlane (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {u : ℝ} (hu : |u| < Submission.boxSide 2 * s) {y : R3}
    (hbox : Submission.boxNorm c σ y ≤ s) (hy2 : y (σ 2) = c (σ 2) + u) :
    y ∈ closure (Submission.PBox s c σ ∩ Work.BoxShrink.Core.upperHalf c σ u) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set Q : ℝ := |u| + 1 with hQdef
  have hQ : (0 : ℝ) < Q := by rw [hQdef]; positivity
  have hQu : u < Q := by rw [hQdef]; linarith [le_abs_self u]
  set δ : ℝ := min (1 / 2) (min ((Submission.boxSide 2 * s - |u|) / 2)
        (ε / (2 * (dist y c + Q + 1)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (by norm_num) (lt_min ?_ (div_pos hε (by positivity)))
    linarith [hu]
  have hδhalf : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδroom : δ < Submission.boxSide 2 * s - |u| := by
    have h1 : δ ≤ (Submission.boxSide 2 * s - |u|) / 2 := by
      rw [hδdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hu, hδpos]
  have hδdist : δ ≤ ε / (2 * (dist y c + Q + 1)) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  rw [dist_eq_norm] at hδdist
  have hnonneg : (0 : ℝ) ≤ 1 - δ := by linarith
  have hcoord : ∀ i : Fin 3,
      ((1 - δ) • y + δ • c + (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)) (σ i) - c (σ i)
        = (1 - δ) * (y (σ i) - c (σ i)) + (δ * Q) * (if i = 2 then 1 else 0) := by
    intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
      Equiv.apply_eq_iff_eq]
    ring
  have hQval : Q = |u| + 1 := hQdef
  refine ⟨(1 - δ) • y + δ • c + (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3), ⟨?_, ?_⟩, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    have hi2 := hcoord i
    have hbs : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
    by_cases hi : i = 2
    · subst hi
      rw [hi2, if_pos rfl, mul_one]
      have hy2' : y (σ 2) - c (σ 2) = u := by rw [hy2]; ring
      rw [hy2']
      have hkey : |(1 - δ) * u + δ * Q| ≤ |u| + δ := by
        have e1 : |(1 - δ) * u| = (1 - δ) * |u| := by rw [abs_mul, abs_of_nonneg hnonneg]
        have e2 : |δ * Q| = δ * Q := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hδpos), abs_of_pos hQ]
        calc |(1 - δ) * u + δ * Q| ≤ |(1 - δ) * u| + |δ * Q| := abs_add_le _ _
          _ = (1 - δ) * |u| + δ * Q := by rw [e1, e2]
          _ = |u| + δ := by rw [hQval]; ring
      linarith [hkey, hδroom]
    · rw [hi2, if_neg hi, mul_zero, add_zero, abs_mul, abs_of_nonneg hnonneg]
      have h1 := abs_sub_le_of_boxNorm_le hbox i
      have h2 : (1 - δ) * |y (σ i) - c (σ i)| ≤ (1 - δ) * (Submission.boxSide i * s) :=
        mul_le_mul_of_nonneg_left h1 hnonneg
      nlinarith [h2, hbs, hδpos]
  · have hi2 := hcoord 2
    rw [if_pos rfl, mul_one] at hi2
    have hy2' : y (σ 2) - c (σ 2) = u := by rw [hy2]; ring
    rw [hy2'] at hi2
    show c (σ 2) + u < ((1 - δ) • y + δ • c + (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)) (σ 2)
    have hkey : 0 < δ * (Q - u) := mul_pos hδpos (by linarith)
    nlinarith [hi2, hkey]
  · rw [dist_eq_norm]
    have hsub : y - ((1 - δ) • y + δ • c + (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3))
        = δ • (y - c) - (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3) := by module
    rw [hsub]
    have he : ‖(PiLp.single 2 (σ 2) (1 : ℝ) : R3)‖ = 1 := by
      rw [PiLp.norm_single]; simp
    have hnorm1 : ‖δ • (y - c)‖ = δ * ‖y - c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδpos)]
    have hnorm2 : ‖(δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)‖ = δ * Q := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (mul_pos hδpos hQ))]
    calc ‖δ • (y - c) - (δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)‖
        ≤ ‖δ • (y - c)‖ + ‖(δ * Q) • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)‖ := norm_sub_le _ _
      _ = δ * ‖y - c‖ + δ * Q := by rw [hnorm1, hnorm2]
      _ = δ * (‖y - c‖ + Q) := by ring
      _ < ε := by
          have h1 : δ * (‖y - c‖ + Q) ≤ δ * (‖y - c‖ + Q + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hδpos)
          have h2 : δ * (‖y - c‖ + Q + 1) ≤ ε / 2 := by
            have hstep := mul_le_mul_of_nonneg_right hδdist (by positivity : (0 : ℝ) ≤ ‖y - c‖ + Q + 1)
            have heq : ε / (2 * (‖y - c‖ + Q + 1)) * (‖y - c‖ + Q + 1) = ε / 2 := by
              field_simp
            linarith [hstep, heq.le]
          nlinarith [h1, h2, hε]

/-! ## The half of the bubble is contained in the closure of the half-box -/

/-- **`halfAbove ⊆ closure (upperBody)`**: every point of the half of the bubble is a limit of
points of the open upper half-box.  On the sphere part above the plane this is the shrink towards
the centre; on the flat part (the cutting plane) it needs `hu` as in
`mem_closure_PBox_inter_upperHalf_of_mem_cutPlane`. -/
theorem halfAbove_subset_closure_upperBody (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    {u : ℝ} (hu : |u| < Submission.boxSide 2 * s) :
    halfAbove s c σ u ⊆ closure (upperBody s c σ u) := by
  intro y hy
  rw [mem_halfAbove_of_boxNorm] at hy
  rcases hy with ⟨hb, hle⟩ | ⟨hb, heq⟩
  · rcases lt_or_eq_of_le hle with hlt | heq'
    · have h1 : y ∈ closure (Submission.PBox s c σ) :=
        mem_closure_PBox_of_boxNorm_le hs c σ (le_of_eq hb)
      have h2 : y ∈ Work.BoxShrink.Core.upperHalf c σ u := hlt
      have h3 := IsOpen.closure_inter (t := Work.BoxShrink.Core.upperHalf c σ u)
        (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)))
        ⟨h1, h2⟩
      simpa only [upperBody] using h3
    · exact mem_closure_PBox_inter_upperHalf_of_mem_cutPlane hs c σ hu (le_of_eq hb) heq'.symm
  · exact mem_closure_PBox_inter_upperHalf_of_mem_cutPlane hs c σ hu (le_of_lt hb) heq

/-! ## The main statement -/

/-- **Pardon's first half of the double bubble is the boundary of the upper half-box.** -/
theorem halfAbove_eq_frontier_upperBody {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.Step2.halfAbove s c σ u = frontier (Work.Step2.upperBody s c σ u) := by
  have hsub := halfAbove_subset_closure_upperBody hs c σ hu
  have hcl : closure (upperBody s c σ u) ⊆ upperBody s c σ u ∪ halfAbove s c σ u :=
    (isClosed_upperBody_union_halfAbove (s := s) (c := c) (σ := σ) (u := u)).closure_subset_iff.mpr
      subset_union_left
  have hInt : interior (upperBody s c σ u) = upperBody s c σ u :=
    (isOpen_upperBody (s := s) (c := c) (σ := σ) (u := u)).interior_eq
  ext y
  rw [frontier, Set.mem_sdiff, hInt]
  constructor
  · intro hy
    exact ⟨hsub hy,
      fun h => (Set.disjoint_left.mp (disjoint_upperBody_halfAbove (s := s) (c := c) (σ := σ)
        (u := u))) h hy⟩
  · rintro ⟨hycl, hyA⟩
    rcases hcl hycl with h | h
    · exact absurd h hyA
    · exact h

end

end Work.Step2
