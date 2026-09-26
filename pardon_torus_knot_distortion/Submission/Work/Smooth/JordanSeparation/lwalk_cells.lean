import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.lattice_edge_inter
import Submission.Work.Smooth.JordanSeparation.lwalk_basic
import Submission.Work.Smooth.JordanSeparation.lwalk_range
import Submission.Work.Smooth.JordanSeparation.lwalk_region

/-!
# The cells of the lattice, and the boundary edges of a union of cells

For a mesh `c > 0` and a lattice point `p : ℤ × ℤ`, `unitCell c p` is the open unit square of the
scaled lattice with lower-left corner `c • gpt p`, and `cellCl c p` its closure.  `cellSet Q` is
the union of the closed cells over `Q : Set (ℤ × ℤ)`, and `cellRim Q` is its "unitCell boundary": the
union of the closed unit lattice edges that have exactly one adjacent unitCell in `Q`.

This is the combinatorial substrate of the peel in `_LWALK_PEEL_NOTES.md`, step 3.  What is used
by the peel, and still to be proved on top of these definitions:

* `smul_gpt_mem_cellCl : c • gpt p ∈ cellCl c p` and the other three corners;
* `convex_cellCl`, `isClosed_cellCl` (each closed unitCell is compact convex, hence simply connected:
  the flip in the peel is a homotopy inside a single closed unitCell);
* the *degeneracy* of the lattice: the relative interior of a unit lattice edge contains no lattice
  point, and two unit lattice edges meet only at a common endpoint or coincide — this gives
  "every point of the curve off the vertices lies in a well-defined unitCell, and nothing else";
* the *local structure at an interior point of a walk edge*: for `z` in the relative interior of an
  edge, a small disc around `z` meets exactly two cells, one contained in the bounded side `V` and
  the other in the unbounded side;
* hence `LWalk.edgeSet W = cellRim Q₀` where `Q₀ = {C | unitCell c C ⊆ S.V}` is the set of cells of the
  bounded side.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- The open unit unitCell of mesh `c` with lower-left corner `p`. -/
def unitCell (c : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z | (p.1 : ℝ) * c < z.re ∧ z.re < ((p.1 : ℝ) + 1) * c ∧
       (p.2 : ℝ) * c < z.im ∧ z.im < ((p.2 : ℝ) + 1) * c}

/-- The closed unit unitCell of mesh `c` with lower-left corner `p`. -/
def cellCl (c : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z | (p.1 : ℝ) * c ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) * c ∧
       (p.2 : ℝ) * c ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) * c}

@[simp] theorem mem_cell {c : ℝ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ unitCell c p ↔ (p.1 : ℝ) * c < z.re ∧ z.re < ((p.1 : ℝ) + 1) * c ∧
       (p.2 : ℝ) * c < z.im ∧ z.im < ((p.2 : ℝ) + 1) * c := Iff.rfl

@[simp] theorem mem_cellCl {c : ℝ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ cellCl c p ↔ (p.1 : ℝ) * c ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) * c ∧
       (p.2 : ℝ) * c ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) * c := Iff.rfl

theorem cell_subset_cellCl (c : ℝ) (p : ℤ × ℤ) : unitCell c p ⊆ cellCl c p := by
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

/-- The union of the closed cells of a set of lattice points. -/
def cellSet (c : ℝ) (Q : Set (ℤ × ℤ)) : Set ℂ := ⋃ p ∈ Q, cellCl c p

/-- The horizontal unit lattice edge with lower-left endpoint `p`. -/
def edgeH (c : ℝ) (p : ℤ × ℤ) : Set ℂ := segment ℝ (c • gpt p) (c • gpt (p + (1, 0)))

/-- The vertical unit lattice edge with lower-left endpoint `p`. -/
def edgeV (c : ℝ) (p : ℤ × ℤ) : Set ℂ := segment ℝ (c • gpt p) (c • gpt (p + (0, 1)))

/-- The two cells adjacent to the horizontal edge with lower-left endpoint `p` (above, below). -/
def cellsOfH (p : ℤ × ℤ) : (ℤ × ℤ) × (ℤ × ℤ) := (p, (p.1, p.2 - 1))

/-- The two cells adjacent to the vertical edge with lower-left endpoint `p` (right, left). -/
def cellsOfV (p : ℤ × ℤ) : (ℤ × ℤ) × (ℤ × ℤ) := (p, (p.1 - 1, p.2))

/-- `e` is a boundary edge of the unitCell set `Q`: exactly one of its two adjacent cells lies in `Q`.
`horiz` selects the horizontal (`true`) or vertical (`false`) family. -/
def IsRim (Q : Set (ℤ × ℤ)) (horiz : Bool) (p : ℤ × ℤ) : Prop :=
  ((horiz = true ∧ (cellsOfH p).1 ∈ Q ∧ (cellsOfH p).2 ∉ Q) ∨
   (horiz = true ∧ (cellsOfH p).1 ∉ Q ∧ (cellsOfH p).2 ∈ Q) ∨
   (horiz = false ∧ (cellsOfV p).1 ∈ Q ∧ (cellsOfV p).2 ∉ Q) ∨
   (horiz = false ∧ (cellsOfV p).1 ∉ Q ∧ (cellsOfV p).2 ∈ Q))

/-- The union of the closed unit lattice edges that are boundary edges of the unitCell set `Q`. -/
def cellRim (c : ℝ) (Q : Set (ℤ × ℤ)) : Set ℂ :=
  (⋃ p ∈ {p : ℤ × ℤ | IsRim Q true p}, edgeH c p) ∪
  (⋃ p ∈ {p : ℤ × ℤ | IsRim Q false p}, edgeV c p)

/-! ### Coordinates of the scaled lattice points, and the corners of a unitCell -/

theorem gpt_re (p : ℤ × ℤ) : (gpt p).re = (p.1 : ℝ) := by
  simp only [gpt, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem gpt_im (p : ℤ × ℤ) : (gpt p).im = (p.2 : ℝ) := by
  simp only [gpt, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]

theorem re_smul_gpt (c : ℝ) (p : ℤ × ℤ) : (c • gpt p).re = (p.1 : ℝ) * c := by
  rw [Complex.smul_re, gpt_re]
  ring

theorem im_smul_gpt (c : ℝ) (p : ℤ × ℤ) : (c • gpt p).im = (p.2 : ℝ) * c := by
  rw [Complex.smul_im, gpt_im]
  ring

/-- **The scaled lattice point `c • gpt q` lies in the closed unitCell of `p` iff its lattice
coordinates are within the unit square.** -/
theorem smul_gpt_mem_cellCl_iff (c : ℝ) (hc : 0 < c) (p q : ℤ × ℤ) :
    c • gpt q ∈ cellCl c p ↔ ((p.1 : ℝ) ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ (p.2 : ℝ) + 1) := by
  have hc0 : 0 ≤ c := le_of_lt hc
  rw [mem_cellCl, re_smul_gpt, im_smul_gpt]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨le_of_mul_le_mul_right h1 hc, le_of_mul_le_mul_right h2 hc,
      le_of_mul_le_mul_right h3 hc, le_of_mul_le_mul_right h4 hc⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨mul_le_mul_of_nonneg_right h1 hc0, mul_le_mul_of_nonneg_right h2 hc0,
      mul_le_mul_of_nonneg_right h3 hc0, mul_le_mul_of_nonneg_right h4 hc0⟩

/-- The lower-left corner of a unitCell lies in its closure. -/
theorem smul_gpt_mem_cellCl (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) : c • gpt p ∈ cellCl c p := by
  rw [smul_gpt_mem_cellCl_iff c hc p p]
  exact ⟨le_rfl, by linarith, le_rfl, by linarith⟩

/-- The lower-right corner of a unitCell lies in its closure. -/
theorem smul_gpt_add_one_zero_mem_cellCl (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) :
    c • gpt (p + (1, 0)) ∈ cellCl c p := by
  have h1 : (p + (1, 0) : ℤ × ℤ).1 = p.1 + 1 := by simp
  have h2 : (p + (1, 0) : ℤ × ℤ).2 = p.2 := by simp
  rw [smul_gpt_mem_cellCl_iff c hc p (p + (1, 0)), h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-- The upper-left corner of a unitCell lies in its closure. -/
theorem smul_gpt_add_zero_one_mem_cellCl (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) :
    c • gpt (p + (0, 1)) ∈ cellCl c p := by
  have h1 : (p + (0, 1) : ℤ × ℤ).1 = p.1 := by simp
  have h2 : (p + (0, 1) : ℤ × ℤ).2 = p.2 + 1 := by simp
  rw [smul_gpt_mem_cellCl_iff c hc p (p + (0, 1)), h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-- The upper-right corner of a unitCell lies in its closure. -/
theorem smul_gpt_add_one_one_mem_cellCl (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) :
    c • gpt (p + (1, 1)) ∈ cellCl c p := by
  have h1 : (p + (1, 1) : ℤ × ℤ).1 = p.1 + 1 := by simp
  have h2 : (p + (1, 1) : ℤ × ℤ).2 = p.2 + 1 := by simp
  rw [smul_gpt_mem_cellCl_iff c hc p (p + (1, 1)), h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-! ### Convexity and closedness -/

/-- A weighted average with weights summing to one is the value itself. -/
theorem smul_add_smul_of_add_eq_one {k a b : ℝ} (hab : a + b = 1) : a * k + b * k = k := by
  rw [← add_mul, hab, one_mul]

/-- **Every closed unitCell is convex.** -/
theorem convex_cellCl (c : ℝ) (_hc : 0 < c) (p : ℤ × ℤ) : Convex ℝ (cellCl c p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [mem_cellCl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    have h1 := add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
    have h2 := smul_add_smul_of_add_eq_one (k := (p.1 : ℝ) * c) hab
    linarith
  · rw [hre]
    have h1 := add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
    have h2 := smul_add_smul_of_add_eq_one (k := ((p.1 : ℝ) + 1) * c) hab
    linarith
  · rw [him]
    have h1 := add_le_add (mul_le_mul_of_nonneg_left hx3 ha) (mul_le_mul_of_nonneg_left hy3 hb)
    have h2 := smul_add_smul_of_add_eq_one (k := (p.2 : ℝ) * c) hab
    linarith
  · rw [him]
    have h1 := add_le_add (mul_le_mul_of_nonneg_left hx4 ha) (mul_le_mul_of_nonneg_left hy4 hb)
    have h2 := smul_add_smul_of_add_eq_one (k := ((p.2 : ℝ) + 1) * c) hab
    linarith

/-- **Every closed unitCell is closed.** -/
theorem isClosed_cellCl (c : ℝ) (p : ℤ × ℤ) : IsClosed (cellCl c p) := by
  have h : cellCl c p = {z : ℂ | (p.1 : ℝ) * c ≤ z.re} ∩ {z : ℂ | z.re ≤ ((p.1 : ℝ) + 1) * c} ∩
      {z : ℂ | (p.2 : ℝ) * c ≤ z.im} ∩ {z : ℂ | z.im ≤ ((p.2 : ℝ) + 1) * c} := by
    ext z; simp only [mem_cellCl, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [h]
  exact IsClosed.inter (IsClosed.inter (IsClosed.inter
    (isClosed_le continuous_const Complex.continuous_re)
    (isClosed_le Complex.continuous_re continuous_const))
    (isClosed_le continuous_const Complex.continuous_im))
    (isClosed_le Complex.continuous_im continuous_const)

/-- **Every closed unitCell is compact**: it is the image of the compact box
`[p₁c, (p₁+1)c] × [p₂c, (p₂+1)c]` under the continuous map `(x,y) ↦ x + y·I`. -/
theorem isCompact_cellCl (c : ℝ) (_hc : 0 < c) (p : ℤ × ℤ) : IsCompact (cellCl c p) := by
  have h : cellCl c p =
      (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ''
        (Set.Icc ((p.1 : ℝ) * c) (((p.1 : ℝ) + 1) * c) ×ˢ
         Set.Icc ((p.2 : ℝ) * c) (((p.2 : ℝ) + 1) * c)) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1, hz.2.2.2⟩, ?_⟩
      simpa using Complex.re_add_im z
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
      rw [mem_cellCl]
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, sub_zero,
        add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
      exact ⟨hq1, hq2, hq3, hq4⟩
  rw [h]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

/-! ### Coordinates of the four edge endpoints of a unitCell -/

theorem re_smul_gpt_add_one_zero (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (1, 0))).re = ((p.1 : ℝ) + 1) * c := by
  rw [re_smul_gpt]
  rw [show (p + (1, 0) : ℤ × ℤ).1 = p.1 + 1 from by simp]
  push_cast
  ring

theorem im_smul_gpt_add_one_zero (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (1, 0))).im = (p.2 : ℝ) * c := by
  rw [im_smul_gpt]
  rw [show (p + (1, 0) : ℤ × ℤ).2 = p.2 from by simp]

theorem re_smul_gpt_add_zero_one (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (0, 1))).re = (p.1 : ℝ) * c := by
  rw [re_smul_gpt]
  rw [show (p + (0, 1) : ℤ × ℤ).1 = p.1 from by simp]

theorem im_smul_gpt_add_zero_one (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (0, 1))).im = ((p.2 : ℝ) + 1) * c := by
  rw [im_smul_gpt]
  rw [show (p + (0, 1) : ℤ × ℤ).2 = p.2 + 1 from by simp]
  push_cast
  ring

theorem re_smul_gpt_add_one_one (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (1, 1))).re = ((p.1 : ℝ) + 1) * c := by
  rw [re_smul_gpt]
  rw [show (p + (1, 1) : ℤ × ℤ).1 = p.1 + 1 from by simp]
  push_cast
  ring

theorem im_smul_gpt_add_one_one (c : ℝ) (p : ℤ × ℤ) :
    (c • gpt (p + (1, 1))).im = ((p.2 : ℝ) + 1) * c := by
  rw [im_smul_gpt]
  rw [show (p + (1, 1) : ℤ × ℤ).2 = p.2 + 1 from by simp]
  push_cast
  ring

theorem add_add_one (p : ℤ × ℤ) : ((p + (1, 0)) + (0, 1) : ℤ × ℤ) = p + (1, 1) := by
  ext <;> simp

theorem add_add_one' (p : ℤ × ℤ) : ((p + (0, 1)) + (1, 0) : ℤ × ℤ) = p + (1, 1) := by
  ext <;> simp

/-! ### Coordinates of an interpolated point of an edge -/

theorem re_interp_smul_gpt (c t : ℝ) (p q : ℤ × ℤ) :
    ((1 - t) • (c • gpt p) + t • (c • gpt q)).re
      = (1 - t) * ((p.1 : ℝ) * c) + t * ((q.1 : ℝ) * c) := by
  simp only [Complex.add_re, Complex.smul_re, gpt_re, smul_eq_mul]
  ring

theorem im_interp_smul_gpt (c t : ℝ) (p q : ℤ × ℤ) :
    ((1 - t) • (c • gpt p) + t • (c • gpt q)).im
      = (1 - t) * ((p.2 : ℝ) * c) + t * ((q.2 : ℝ) * c) := by
  simp only [Complex.add_im, Complex.smul_im, gpt_im, smul_eq_mul]
  ring

/-- **Cells sharing a vertical side meet in that side.** -/
theorem cellCl_inter_cellCl_v (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) :
    cellCl c p ∩ cellCl c (p + (1, 0)) = edgeV c (p + (1, 0)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h1 : ((p + (1, 0) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) + 1 := by simp
  have h2 : ((p + (1, 1) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) + 1 := by simp
  have h3 : ((p + (1, 0) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) := by simp
  have h4 : ((p + (1, 1) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) + 1 := by simp
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    rw [mem_cellCl] at hz1 hz2
    obtain ⟨h1a, h1b, h1c, h1d⟩ := hz1
    obtain ⟨h2a, h2b, h2c, h2d⟩ := hz2
    rw [h1] at h2a
    have hre : z.re = ((p.1 : ℝ) + 1) * c := le_antisymm h1b (by linarith)
    have hlo : (p.2 : ℝ) * c ≤ z.im := by linarith
    have hhi : z.im ≤ ((p.2 : ℝ) + 1) * c := by linarith
    rw [edgeV, segment_eq_image]
    refine ⟨(z.im - (p.2 : ℝ) * c) / c, ⟨?_, ?_⟩, ?_⟩
    · rw [div_nonneg_iff]
      exact Or.inl ⟨by linarith, le_of_lt hc⟩
    · rw [div_le_iff₀ hc]
      linarith
    · have ht : (z.im - (p.2 : ℝ) * c) / c * c = z.im - (p.2 : ℝ) * c :=
        div_mul_cancel₀ _ hcne
      rw [add_add_one]
      apply Complex.ext
      · rw [re_interp_smul_gpt, h1, h2, hre]
        ring
      · rw [im_interp_smul_gpt, h3, h4]
        have hB : ((p.2 : ℝ) + 1) * c = (p.2 : ℝ) * c + c := by ring
        rw [hB]
        have hC : (1 - (z.im - (p.2 : ℝ) * c) / c) * ((p.2 : ℝ) * c)
            + (z.im - (p.2 : ℝ) * c) / c * ((p.2 : ℝ) * c + c)
            = (p.2 : ℝ) * c + (z.im - (p.2 : ℝ) * c) / c * c := by ring
        rw [hC, ht]
        ring
  · intro hz
    rw [edgeV] at hz
    have hseg := hz
    refine ⟨?_, ?_⟩
    · refine (convex_cellCl c hc p).segment_subset ?_ ?_ hseg
      · exact smul_gpt_add_one_zero_mem_cellCl c hc p
      · rw [add_add_one]
        exact smul_gpt_add_one_one_mem_cellCl c hc p
    · refine (convex_cellCl c hc (p + (1, 0))).segment_subset ?_ ?_ hseg
      · exact smul_gpt_mem_cellCl c hc _
      · exact smul_gpt_add_zero_one_mem_cellCl c hc _

/-- **Cells sharing a horizontal side meet in that side.** -/
theorem cellCl_inter_cellCl_h (c : ℝ) (hc : 0 < c) (p : ℤ × ℤ) :
    cellCl c p ∩ cellCl c (p + (0, 1)) = edgeH c (p + (0, 1)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h1 : ((p + (0, 1) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) + 1 := by simp
  have h2 : ((p + (1, 1) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) + 1 := by simp
  have h3 : ((p + (0, 1) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) := by simp
  have h4 : ((p + (1, 1) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) + 1 := by simp
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    rw [mem_cellCl] at hz1 hz2
    obtain ⟨h1a, h1b, h1c, h1d⟩ := hz1
    obtain ⟨h2a, h2b, h2c, h2d⟩ := hz2
    rw [h1] at h2c
    have him : z.im = ((p.2 : ℝ) + 1) * c := le_antisymm h1d (by linarith)
    have hlo : (p.1 : ℝ) * c ≤ z.re := by linarith
    have hhi : z.re ≤ ((p.1 : ℝ) + 1) * c := by linarith
    rw [edgeH, segment_eq_image]
    refine ⟨(z.re - (p.1 : ℝ) * c) / c, ⟨?_, ?_⟩, ?_⟩
    · rw [div_nonneg_iff]
      exact Or.inl ⟨by linarith, le_of_lt hc⟩
    · rw [div_le_iff₀ hc]
      linarith
    · have ht : (z.re - (p.1 : ℝ) * c) / c * c = z.re - (p.1 : ℝ) * c :=
        div_mul_cancel₀ _ hcne
      rw [add_add_one']
      apply Complex.ext
      · rw [re_interp_smul_gpt, h3, h4]
        have hB : ((p.1 : ℝ) + 1) * c = (p.1 : ℝ) * c + c := by ring
        rw [hB]
        have hC : (1 - (z.re - (p.1 : ℝ) * c) / c) * ((p.1 : ℝ) * c)
            + (z.re - (p.1 : ℝ) * c) / c * ((p.1 : ℝ) * c + c)
            = (p.1 : ℝ) * c + (z.re - (p.1 : ℝ) * c) / c * c := by ring
        rw [hC, ht]
        ring
      · rw [im_interp_smul_gpt, h1, h2, him]
        ring
  · intro hz
    rw [edgeH] at hz
    have hseg := hz
    refine ⟨?_, ?_⟩
    · refine (convex_cellCl c hc p).segment_subset ?_ ?_ hseg
      · exact smul_gpt_add_zero_one_mem_cellCl c hc p
      · rw [add_add_one']
        exact smul_gpt_add_one_one_mem_cellCl c hc p
    · refine (convex_cellCl c hc (p + (0, 1))).segment_subset ?_ ?_ hseg
      · exact smul_gpt_mem_cellCl c hc _
      · exact smul_gpt_add_one_zero_mem_cellCl c hc _

/-! ### The lattice points of a unit lattice edge

A unit lattice edge contains exactly two lattice points, its endpoints. -/

theorem smul_gpt_mem_edgeH_iff (c : ℝ) (hc : 0 < c) (p q : ℤ × ℤ) :
    c • gpt q ∈ edgeH c p ↔ q = p ∨ q = p + (1, 0) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc1 : ((p + (1, 0) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) + 1 := by simp
  have hc2 : ((p + (1, 0) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) := by simp
  constructor
  · intro hz
    rw [edgeH, segment_eq_image] at hz
    obtain ⟨t, ht, htq⟩ := hz
    have hre := congrArg Complex.re htq
    have him := congrArg Complex.im htq
    rw [re_interp_smul_gpt, re_smul_gpt, hc1] at hre
    rw [im_interp_smul_gpt, im_smul_gpt, hc2] at him
    have h2 : (p.2 : ℝ) = (q.2 : ℝ) := by
      have hA : (1 - t) * ((p.2 : ℝ) * c) + t * ((p.2 : ℝ) * c) = (p.2 : ℝ) * c := by ring
      exact mul_right_cancel₀ hcne (hA.symm.trans him)
    have h1 : (q.1 : ℝ) = (p.1 : ℝ) + t := by
      have hfact : ((p.1 : ℝ) + t) * c = (q.1 : ℝ) * c := by
        ring_nf
        linarith [hre]
      exact (mul_right_cancel₀ hcne hfact).symm
    have htm : t = ((q.1 - p.1 : ℤ) : ℝ) := by
      push_cast
      linarith
    rcases real_eq_zero_or_one_of_eq_int ht htm with h0 | h1'
    · left
      refine Prod.ext (by exact_mod_cast (by linarith : (q.1 : ℝ) = (p.1 : ℝ))) ?_
      exact_mod_cast h2.symm
    · right
      refine Prod.ext (by exact_mod_cast (by linarith : (q.1 : ℝ) = (p.1 : ℝ) + 1)) ?_
      rw [show (p + (1, 0) : ℤ × ℤ).2 = p.2 from by simp]
      exact_mod_cast h2.symm
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

theorem smul_gpt_mem_edgeV_iff (c : ℝ) (hc : 0 < c) (p q : ℤ × ℤ) :
    c • gpt q ∈ edgeV c p ↔ q = p ∨ q = p + (0, 1) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc1 : ((p + (0, 1) : ℤ × ℤ).1 : ℝ) = (p.1 : ℝ) := by simp
  have hc2 : ((p + (0, 1) : ℤ × ℤ).2 : ℝ) = (p.2 : ℝ) + 1 := by simp
  constructor
  · intro hz
    rw [edgeV, segment_eq_image] at hz
    obtain ⟨t, ht, htq⟩ := hz
    have hre := congrArg Complex.re htq
    have him := congrArg Complex.im htq
    rw [re_interp_smul_gpt, re_smul_gpt, hc1] at hre
    rw [im_interp_smul_gpt, im_smul_gpt, hc2] at him
    have h2 : (p.1 : ℝ) = (q.1 : ℝ) := by
      have hA : (1 - t) * ((p.1 : ℝ) * c) + t * ((p.1 : ℝ) * c) = (p.1 : ℝ) * c := by ring
      exact mul_right_cancel₀ hcne (hA.symm.trans hre)
    have h1 : (q.2 : ℝ) = (p.2 : ℝ) + t := by
      have hfact : ((p.2 : ℝ) + t) * c = (q.2 : ℝ) * c := by
        ring_nf
        linarith [him]
      exact (mul_right_cancel₀ hcne hfact).symm
    have htm : t = ((q.2 - p.2 : ℤ) : ℝ) := by
      push_cast
      linarith
    rcases real_eq_zero_or_one_of_eq_int ht htm with h0 | h1'
    · left
      refine Prod.ext (by exact_mod_cast h2.symm) ?_
      exact_mod_cast (by linarith : (q.2 : ℝ) = (p.2 : ℝ))
    · right
      refine Prod.ext ?_ (by exact_mod_cast (by linarith : (q.2 : ℝ) = (p.2 : ℝ) + 1))
      rw [show (p + (0, 1) : ℤ × ℤ).1 = p.1 from by simp]
      exact_mod_cast h2.symm
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

/-! ### An open unitCell never meets the trace of a lattice walk

Every edge of the walk is a unit lattice edge, hence lies on a grid line, and an open unitCell contains
no grid line.  This is ingredient (a) of the local two-sided structure of the bounded side
(`_LWALK_PEEL_NOTES.md`). -/

theorem notMem_cell_of_int_mul_re {c : ℝ} (hc : 0 < c) {C : ℤ × ℤ} {z : ℂ} {n : ℤ}
    (h : z.re = (n : ℝ) * c) (hz : z ∈ unitCell c C) : False := by
  rw [mem_cell] at hz
  rw [h] at hz
  have h1 : (C.1 : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_right hz.1 (le_of_lt hc)
  have h2 : (n : ℝ) < (C.1 : ℝ) + 1 := lt_of_mul_lt_mul_right hz.2.1 (le_of_lt hc)
  have h1' : C.1 < n := by exact_mod_cast h1
  have h2' : n < C.1 + 1 := by exact_mod_cast h2
  omega

theorem notMem_cell_of_int_mul_im {c : ℝ} (hc : 0 < c) {C : ℤ × ℤ} {z : ℂ} {n : ℤ}
    (h : z.im = (n : ℝ) * c) (hz : z ∈ unitCell c C) : False := by
  rw [mem_cell] at hz
  rw [h] at hz
  have h1 : (C.2 : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_right hz.2.2.1 (le_of_lt hc)
  have h2 : (n : ℝ) < (C.2 : ℝ) + 1 := lt_of_mul_lt_mul_right hz.2.2.2 (le_of_lt hc)
  have h1' : C.2 < n := by exact_mod_cast h1
  have h2' : n < C.2 + 1 := by exact_mod_cast h2
  omega

/-- **An open unitCell never meets the trace of a lattice walk.** -/
theorem cell_disjoint_range_curve (W : LWalk) (C : ℤ × ℤ) :
    unitCell W.c C ∩ Set.range W.curve = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz, hzr⟩
  rw [W.range_curve_eq_range_path, W.range_path] at hzr
  rcases hzr with hzr | hzr
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzr
    obtain ⟨hklt, hzk⟩ := Set.mem_iUnion.mp hk
    rw [LWalk.edge, segPath_range, segment_eq_image] at hzk
    obtain ⟨t, ht, htq⟩ := hzk
    obtain ⟨s, hs, hdir⟩ := gridStep_vert_or_horiz (W.step k hklt)
    have hpt : ∀ j : ℕ, W.pt j = W.c • gpt (W.v j) := by
      intro j
      rw [LWalk.pt, Complex.real_smul]
    rcases hdir with ⟨hp1, hp2⟩ | ⟨hp2, hp1⟩
    · -- vertical edge: `re` is constant along it
      refine notMem_cell_of_int_mul_re W.cpos (n := (W.v k).1) ?_ hz
      have hre := congrArg Complex.re htq
      simp only [] at hre
      rw [hpt k, hpt (k + 1), re_interp_smul_gpt] at hre
      rw [← hre, show ((W.v (k + 1)).1 : ℝ) * W.c = ((W.v k).1 : ℝ) * W.c from by rw [hp1]]
      ring
    · -- horizontal edge: `im` is constant along it
      refine notMem_cell_of_int_mul_im W.cpos (n := (W.v k).2) ?_ hz
      have him := congrArg Complex.im htq
      simp only [] at him
      rw [hpt k, hpt (k + 1), im_interp_smul_gpt] at him
      rw [← him, show ((W.v (k + 1)).2 : ℝ) * W.c = ((W.v k).2 : ℝ) * W.c from by rw [hp2]]
      ring
  · rw [Set.mem_singleton_iff] at hzr
    rw [hzr] at hz
    have hre : (W.pt 0).re = ((W.v 0).1 : ℝ) * W.c := by
      show (W.c * gpt (W.v 0)).re = _
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, gpt_re, gpt_im]
      ring
    exact notMem_cell_of_int_mul_re W.cpos (n := (W.v 0).1) hre hz

/-! ### Convexity of an open unitCell, and the side each unitCell lies on -/

/-- A strict convex combination with a strict lower bound. -/
theorem lt_mul_add_mul {A X Y a b : ℝ} (hX : A < X) (hY : A < Y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : A < a * X + b * Y := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · have hb1 : b = 1 := by linarith
    rw [h0.symm, hb1]
    simpa using hY
  · have h1 : a * A < a * X := mul_lt_mul_of_pos_left hX hpos
    have h2 : b * A ≤ b * Y := mul_le_mul_of_nonneg_left (le_of_lt hY) hb
    have h3 : a * A + b * A = A := smul_add_smul_of_add_eq_one hab
    linarith

/-- A strict convex combination with strict upper bounds stays strictly below. -/
theorem mul_add_mul_lt {X Y A a b : ℝ} (hX : X < A) (hY : Y < A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * X + b * Y < A := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · have hb1 : b = 1 := by linarith
    rw [h0.symm, hb1]
    simpa using hY
  · have h1 : a * X < a * A := mul_lt_mul_of_pos_left hX hpos
    have h2 : b * Y ≤ b * A := mul_le_mul_of_nonneg_left (le_of_lt hY) hb
    have h3 : a * A + b * A = A := smul_add_smul_of_add_eq_one hab
    linarith

/-- **Every open cell is convex.** -/
theorem convex_unitCell (c : ℝ) (_hc : 0 < c) (p : ℤ × ℤ) : Convex ℝ (unitCell c p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [mem_cell]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; exact lt_mul_add_mul hx1 hy1 ha hb hab
  · rw [hre]; exact mul_add_mul_lt hx2 hy2 ha hb hab
  · rw [him]; exact lt_mul_add_mul hx3 hy3 ha hb hab
  · rw [him]; exact mul_add_mul_lt hx4 hy4 ha hb hab

/-- **Every open cell of a lattice walk lies entirely on one side of its curve.** -/
theorem cell_subset_U_or_V (W : LWalk) (S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve)
    (C : ℤ × ℤ) : unitCell W.c C ⊆ S.U ∨ unitCell W.c C ⊆ S.V := by
  have hdisj : unitCell W.c C ⊆ (Set.range W.curve)ᶜ := by
    intro z hz hzr
    have hmem : z ∈ unitCell W.c C ∩ Set.range W.curve := ⟨hz, hzr⟩
    rw [cell_disjoint_range_curve W C] at hmem
    exact hmem
  have hpc : IsPreconnected (unitCell W.c C) := (convex_unitCell W.c W.cpos C).isPreconnected
  exact LWalk.subset_U_or_subset_V S hpc hdisj

/-! ### Edge ranges inside the trace (ingredients of local straightness, (c)) -/

theorem edge_range_subset_curve (W : LWalk) {k : ℕ} (hk : k < W.n) :
    Set.range (W.edge k) ⊆ Set.range W.curve := by
  intro z hz
  rw [W.range_curve_eq_range_path, W.range_path]
  exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hz⟩)

theorem pt_zero_mem_range_curve (W : LWalk) : W.pt 0 ∈ Set.range W.curve := by
  rw [W.range_curve_eq_range_path, W.range_path]
  exact Or.inr rfl

/-- A point of the trace is either the base point or lies on one of the edges. -/
theorem mem_range_curve_iff (W : LWalk) {z : ℂ} :
    z ∈ Set.range W.curve ↔ z = W.pt 0 ∨ ∃ k < W.n, z ∈ Set.range (W.edge k) := by
  rw [W.range_curve_eq_range_path, W.range_path]
  constructor
  · intro hz
    rw [Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hklt, hzk⟩ := Set.mem_iUnion.mp hk
      exact Or.inr ⟨k, hklt, hzk⟩
    · exact Or.inl (Set.mem_singleton_iff.mp hz)
  · rintro (rfl | ⟨k, hklt, hzk⟩)
    · exact Set.mem_union_right _ rfl
    · exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hklt, hzk⟩⟩)

/-! ### Every walk edge is a canonical horizontal or vertical lattice edge

Step 1 of local straightness (`_LWALK_PEEL_NOTES.md`, (c)). -/

theorem edge_range_eq_edgeH_or_edgeV (W : LWalk) {k : ℕ} (hk : k < W.n) :
    (∃ p : ℤ × ℤ, Set.range (W.edge k) = edgeH W.c p) ∨
    (∃ p : ℤ × ℤ, Set.range (W.edge k) = edgeV W.c p) := by
  obtain ⟨s, hs, hdir⟩ := gridStep_vert_or_horiz (W.step k hk)
  have hpt : ∀ j : ℕ, W.pt j = W.c • gpt (W.v j) := by
    intro j
    rw [LWalk.pt, Complex.real_smul]
  rw [LWalk.edge, segPath_range, hpt k, hpt (k + 1)]
  rcases hdir with ⟨hp1, hp2⟩ | ⟨hp2, hp1⟩
  · -- vertical: the first coordinate is constant
    rcases hs with h1 | h1
    · -- increasing: base `W.v k`
      right
      refine ⟨W.v k, ?_⟩
      rw [edgeV]
      have hv : W.v (k + 1) = W.v k + (0, 1) := by
        refine Prod.ext ?_ ?_
        · rw [hp1]; simp
        · rw [hp2, h1]; simp
      rw [hv]
    · -- decreasing: base `W.v (k+1)`
      right
      refine ⟨W.v (k + 1), ?_⟩
      rw [edgeV]
      have hv : W.v k = W.v (k + 1) + (0, 1) := by
        refine Prod.ext ?_ ?_
        · rw [show (W.v (k + 1) + (0, 1) : ℤ × ℤ).1 = (W.v (k + 1)).1 from by simp, hp1]
        · rw [show (W.v (k + 1) + (0, 1) : ℤ × ℤ).2 = (W.v (k + 1)).2 + 1 from by simp]
          have h2 : (W.v (k + 1)).2 = (W.v k).2 - 1 := by rw [hp2, h1]; ring
          rw [h2]; omega
      rw [hv]
      exact segment_symm ℝ _ _
  · -- horizontal: the second coordinate is constant
    rcases hs with h1 | h1
    · left
      refine ⟨W.v k, ?_⟩
      rw [edgeH]
      have hv : W.v (k + 1) = W.v k + (1, 0) := by
        refine Prod.ext ?_ ?_
        · rw [hp1, h1]; simp
        · rw [hp2]; simp
      rw [hv]
    · left
      refine ⟨W.v (k + 1), ?_⟩
      rw [edgeH]
      have hv : W.v k = W.v (k + 1) + (1, 0) := by
        refine Prod.ext ?_ ?_
        · rw [show (W.v (k + 1) + (1, 0) : ℤ × ℤ).1 = (W.v (k + 1)).1 + 1 from by simp]
          have h2 : (W.v (k + 1)).1 = (W.v k).1 - 1 := by rw [hp1, h1]; ring
          rw [h2]; omega
        · rw [show (W.v (k + 1) + (1, 0) : ℤ × ℤ).2 = (W.v (k + 1)).2 from by simp, hp2]
      rw [hv]
      exact segment_symm ℝ _ _


/-! ### Perpendicular unit lattice edges meet only in lattice points

The "perpendicular carriers are impossible for an interior point" half of step 2 of local
straightness (`_LWALK_PEEL_NOTES.md`, (c)). -/

theorem exists_gpt_of_mem_edgeH_inter_edgeV {c : ℝ} {p q : ℤ × ℤ} {z : ℂ}
    (h1 : z ∈ edgeH c p) (h2 : z ∈ edgeV c q) : ∃ a : ℤ × ℤ, z = c • gpt a := by
  rw [edgeH, segment_eq_image] at h1
  rw [edgeV, segment_eq_image] at h2
  obtain ⟨t, ht, ht1⟩ := h1
  obtain ⟨u, hu, hu2⟩ := h2
  have him := congrArg Complex.im ht1
  have hre := congrArg Complex.re hu2
  simp only [] at him hre
  rw [im_interp_smul_gpt] at him
  rw [re_interp_smul_gpt] at hre
  refine ⟨(q.1, p.2), ?_⟩
  apply Complex.ext
  · rw [re_smul_gpt, ← hre]
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    exact smul_add_smul_of_add_eq_one (k := (q.1 : ℝ) * c) (by ring)
  · rw [im_smul_gpt, ← him]
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    exact smul_add_smul_of_add_eq_one (k := (p.2 : ℝ) * c) (by ring)

/-! ### Coordinates of a point of a canonical edge

First step of the parallel half of step 2 of local straightness (`_LWALK_PEEL_NOTES.md`, (c)):
a point of a horizontal unit lattice edge has its second coordinate pinned to `p.2 * c` and its
first coordinate of the form `p.1 * c + t * c` with `t ∈ [0,1]`. -/

theorem edgeH_coords {c : ℝ} {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ edgeH c p) :
    ∃ t ∈ Icc (0:ℝ) 1, z.im = (p.2 : ℝ) * c ∧ z.re = (p.1 : ℝ) * c + t * c := by
  rw [edgeH, segment_eq_image] at hz
  obtain ⟨t, ht, htq⟩ := hz
  have him := congrArg Complex.im htq
  have hre := congrArg Complex.re htq
  simp only [] at him hre
  rw [im_interp_smul_gpt] at him
  rw [re_interp_smul_gpt] at hre
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← him]
    simp only [Prod.snd_add, add_zero]
    exact smul_add_smul_of_add_eq_one (k := (p.2 : ℝ) * c) (by ring)
  · simp only [Prod.fst_add] at hre
    rw [← hre]
    push_cast
    ring

theorem edgeV_coords {c : ℝ} {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ edgeV c p) :
    ∃ t ∈ Icc (0:ℝ) 1, z.re = (p.1 : ℝ) * c ∧ z.im = (p.2 : ℝ) * c + t * c := by
  rw [edgeV, segment_eq_image] at hz
  obtain ⟨t, ht, htq⟩ := hz
  have him := congrArg Complex.im htq
  have hre := congrArg Complex.re htq
  simp only [] at him hre
  rw [im_interp_smul_gpt] at him
  rw [re_interp_smul_gpt] at hre
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← hre]
    simp only [Prod.fst_add, add_zero]
    exact smul_add_smul_of_add_eq_one (k := (p.1 : ℝ) * c) (by ring)
  · simp only [Prod.snd_add] at him
    rw [← him]
    push_cast
    ring

end

end Work.Smooth.JordanSeparation
