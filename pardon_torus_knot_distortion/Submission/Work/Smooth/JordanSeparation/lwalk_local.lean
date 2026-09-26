import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_cells
import Submission.Work.Smooth.JordanSeparation.lwalk_region

/-!
# Local structure of the trace of a lattice walk at an edge midpoint

The ball of radius `c/4` around the midpoint of a unit lattice edge meets the trace of the walk
only in that edge.  This is the local input of the side determination of the peel
(`_LWALK_PEEL_NOTES2.md`, gap 1).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### Elementary arithmetic of integer and half-integer points -/

theorem one_le_abs_intCast {a : ℤ} (h : a ≠ 0) : (1 : ℝ) ≤ |(a : ℝ)| := by
  have h2 : (1 : ℤ) ≤ |a| := Int.one_le_abs h
  rw [← Int.cast_abs]
  exact_mod_cast h2

theorem one_le_abs_sub_intCast {a b : ℤ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  rw [← Int.cast_sub]
  exact one_le_abs_intCast (sub_ne_zero.mpr h)

theorem half_le_abs_sub_half {j b : ℤ} : (1 / 2 : ℝ) ≤ |(b : ℝ) - ((j : ℝ) + 1 / 2)| := by
  have h : (b : ℝ) - ((j : ℝ) + 1 / 2) = ((2 * (b - j) - 1 : ℤ) : ℝ) / 2 := by push_cast; ring
  rw [h]
  have hne : (2 * (b - j) - 1 : ℤ) ≠ 0 := by
    intro hc
    have : (2 * (b - j) : ℤ) = 1 := by omega
    omega
  have h1 : (1 : ℝ) ≤ |((2 * (b - j) - 1 : ℤ) : ℝ)| := one_le_abs_intCast hne
  rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
  linarith

/-- If `k ≠ 0` is an integer and `0 ≤ t ≤ 1`, then `(k - 1/2) + t` is at distance `≥ 1/2` from
`0`. -/
theorem half_le_abs_intCast_sub_half_add {k : ℤ} (hk : k ≠ 0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (1 / 2 : ℝ) ≤ |((k : ℝ) - 1 / 2) + t| := by
  rcases lt_or_gt_of_ne hk with h | h
  · have hk' : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    have hneg : ((k : ℝ) - 1 / 2) + t ≤ 0 := by linarith [ht.2]
    rw [abs_of_nonpos hneg]
    linarith [ht.1, ht.2, hk']
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by
      have : (1 : ℤ) ≤ k := by omega
      exact_mod_cast this
    have hpos : 0 ≤ ((k : ℝ) - 1 / 2) + t := by linarith [ht.1]
    rw [abs_of_nonneg hpos]
    linarith [ht.1, ht.2, hk']

/-! ### Complex distance bookkeeping -/

theorem abs_re_sub_le_dist (z m : ℂ) : |z.re - m.re| ≤ dist z m := by
  have h : (z - m).re = z.re - m.re := by simp
  rw [dist_eq_norm, ← h]
  exact Complex.abs_re_le_norm _

theorem abs_im_sub_le_dist (z m : ℂ) : |z.im - m.im| ≤ dist z m := by
  have h : (z - m).im = z.im - m.im := by simp
  rw [dist_eq_norm, ← h]
  exact Complex.abs_im_le_norm _

/-- The midpoint of the horizontal edge with lower-left corner `p`, as a point of `ℂ`. -/
def midH (c : ℝ) (p : ℤ × ℤ) : ℂ := (((p.1 : ℝ) + 1 / 2) * c : ℝ) + (((p.2 : ℝ) * c : ℝ)) * Complex.I

/-- The midpoint of the vertical edge with lower-left corner `p`, as a point of `ℂ`. -/
def midV (c : ℝ) (p : ℤ × ℤ) : ℂ := (((p.1 : ℝ) * c : ℝ)) + ((((p.2 : ℝ) + 1 / 2) * c : ℝ)) * Complex.I

@[simp] theorem midH_re (c : ℝ) (p : ℤ × ℤ) : (midH c p).re = ((p.1 : ℝ) + 1 / 2) * c := by
  simp [midH]

@[simp] theorem midH_im (c : ℝ) (p : ℤ × ℤ) : (midH c p).im = (p.2 : ℝ) * c := by
  simp [midH]

@[simp] theorem midV_re (c : ℝ) (p : ℤ × ℤ) : (midV c p).re = (p.1 : ℝ) * c := by
  simp [midV]

@[simp] theorem midV_im (c : ℝ) (p : ℤ × ℤ) : (midV c p).im = ((p.2 : ℝ) + 1 / 2) * c := by
  simp [midV]

/-! ### Distance bounds between the midpoints and the canonical edges -/

theorem midH_le_dist_edgeH {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} (h : p ≠ q) {z : ℂ}
    (hz : z ∈ edgeH c q) : c / 2 ≤ dist z (midH c p) := by
  obtain ⟨t, ht, him, hre⟩ := edgeH_coords hz
  rcases eq_or_ne q.2 p.2 with h2 | h2
  · have h1 : q.1 ≠ p.1 := fun h1' => h (Prod.ext h1'.symm h2.symm)
    have hk : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr h1
    have key : (1 / 2 : ℝ) * c ≤ |z.re - (midH c p).re| := by
      have heq : z.re - (midH c p).re = (((q.1 - p.1 : ℤ) : ℝ) - 1 / 2 + t) * c := by
        rw [midH_re, hre]; push_cast; ring
      rw [heq, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right (half_le_abs_intCast_sub_half_add hk ht) (le_of_lt hc)
    calc c / 2 = (1 / 2 : ℝ) * c := by ring
      _ ≤ |z.re - (midH c p).re| := key
      _ ≤ dist z (midH c p) := abs_re_sub_le_dist _ _
  · have key : c ≤ |z.im - (midH c p).im| := by
      have heq : z.im - (midH c p).im = ((q.2 : ℝ) - (p.2 : ℝ)) * c := by
        rw [midH_im, him]; ring
      rw [heq, abs_mul, abs_of_pos hc]
      simpa using mul_le_mul_of_nonneg_right (one_le_abs_sub_intCast h2) (le_of_lt hc)
    calc c / 2 ≤ c := by linarith
      _ ≤ |z.im - (midH c p).im| := key
      _ ≤ dist z (midH c p) := abs_im_sub_le_dist _ _

theorem midV_le_dist_edgeV {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} (h : p ≠ q) {z : ℂ}
    (hz : z ∈ edgeV c q) : c / 2 ≤ dist z (midV c p) := by
  obtain ⟨t, ht, hre, him⟩ := edgeV_coords hz
  rcases eq_or_ne q.1 p.1 with h1 | h1
  · have h2 : q.2 ≠ p.2 := fun h2' => h (Prod.ext h1.symm h2'.symm)
    have hk : q.2 - p.2 ≠ 0 := sub_ne_zero.mpr h2
    have key : (1 / 2 : ℝ) * c ≤ |z.im - (midV c p).im| := by
      have heq : z.im - (midV c p).im = (((q.2 - p.2 : ℤ) : ℝ) - 1 / 2 + t) * c := by
        rw [midV_im, him]; push_cast; ring
      rw [heq, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right (half_le_abs_intCast_sub_half_add hk ht) (le_of_lt hc)
    calc c / 2 = (1 / 2 : ℝ) * c := by ring
      _ ≤ |z.im - (midV c p).im| := key
      _ ≤ dist z (midV c p) := abs_im_sub_le_dist _ _
  · have key : c ≤ |z.re - (midV c p).re| := by
      have heq : z.re - (midV c p).re = ((q.1 : ℝ) - (p.1 : ℝ)) * c := by
        rw [midV_re, hre]; ring
      rw [heq, abs_mul, abs_of_pos hc]
      simpa using mul_le_mul_of_nonneg_right (one_le_abs_sub_intCast h1) (le_of_lt hc)
    calc c / 2 ≤ c := by linarith
      _ ≤ |z.re - (midV c p).re| := key
      _ ≤ dist z (midV c p) := abs_re_sub_le_dist _ _

theorem midH_le_dist_edgeV {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} {z : ℂ} (hz : z ∈ edgeV c q) :
    c / 2 ≤ dist z (midH c p) := by
  obtain ⟨t, ht, hre, him⟩ := edgeV_coords hz
  have hb : (1 / 2 : ℝ) ≤ |(q.1 : ℝ) - ((p.1 : ℝ) + 1 / 2)| := by
    simpa using half_le_abs_sub_half (j := p.1) (b := q.1)
  have key : (1 / 2 : ℝ) * c ≤ |z.re - (midH c p).re| := by
    have heq : z.re - (midH c p).re = ((q.1 : ℝ) - ((p.1 : ℝ) + 1 / 2)) * c := by
      rw [midH_re, hre]; ring
    rw [heq, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hc)
  calc c / 2 = (1 / 2 : ℝ) * c := by ring
    _ ≤ |z.re - (midH c p).re| := key
    _ ≤ dist z (midH c p) := abs_re_sub_le_dist _ _

theorem midV_le_dist_edgeH {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} {z : ℂ} (hz : z ∈ edgeH c q) :
    c / 2 ≤ dist z (midV c p) := by
  obtain ⟨t, ht, him, hre⟩ := edgeH_coords hz
  have hb : (1 / 2 : ℝ) ≤ |(q.2 : ℝ) - ((p.2 : ℝ) + 1 / 2)| := by
    simpa using half_le_abs_sub_half (j := p.2) (b := q.2)
  have key : (1 / 2 : ℝ) * c ≤ |z.im - (midV c p).im| := by
    have heq : z.im - (midV c p).im = ((q.2 : ℝ) - ((p.2 : ℝ) + 1 / 2)) * c := by
      rw [midV_im, him]; ring
    rw [heq, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hc)
  calc c / 2 = (1 / 2 : ℝ) * c := by ring
    _ ≤ |z.im - (midV c p).im| := key
    _ ≤ dist z (midV c p) := abs_im_sub_le_dist _ _

/-- A lattice point is at distance at least `c/2` from the midpoint of `edgeH c p`. -/
theorem midH_le_dist_gpt {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} :
    c / 2 ≤ dist (c • gpt q) (midH c p) := by
  have hb : (1 / 2 : ℝ) ≤ |(q.1 : ℝ) - ((p.1 : ℝ) + 1 / 2)| := by
    simpa using half_le_abs_sub_half (j := p.1) (b := q.1)
  have key : (1 / 2 : ℝ) * c ≤ |(c • gpt q).re - (midH c p).re| := by
    have heq : (c • gpt q).re - (midH c p).re = ((q.1 : ℝ) - ((p.1 : ℝ) + 1 / 2)) * c := by
      rw [midH_re, re_smul_gpt]; ring
    rw [heq, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hc)
  calc c / 2 = (1 / 2 : ℝ) * c := by ring
    _ ≤ |(c • gpt q).re - (midH c p).re| := key
    _ ≤ dist (c • gpt q) (midH c p) := abs_re_sub_le_dist _ _

/-- A lattice point is at distance at least `c/2` from the midpoint of `edgeV c p`. -/
theorem midV_le_dist_gpt {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} :
    c / 2 ≤ dist (c • gpt q) (midV c p) := by
  have hb : (1 / 2 : ℝ) ≤ |(q.2 : ℝ) - ((p.2 : ℝ) + 1 / 2)| := by
    simpa using half_le_abs_sub_half (j := p.2) (b := q.2)
  have key : (1 / 2 : ℝ) * c ≤ |(c • gpt q).im - (midV c p).im| := by
    have heq : (c • gpt q).im - (midV c p).im = ((q.2 : ℝ) - ((p.2 : ℝ) + 1 / 2)) * c := by
      rw [midV_im, im_smul_gpt]; ring
    rw [heq, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hc)
  calc c / 2 = (1 / 2 : ℝ) * c := by ring
    _ ≤ |(c • gpt q).im - (midV c p).im| := key
    _ ≤ dist (c • gpt q) (midV c p) := abs_im_sub_le_dist _ _

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- The midpoint of the `k`-th edge of a walk. -/
def LWalk.midPoint (W : LWalk) (k : ℕ) : ℂ := (W.pt k + W.pt (k + 1)) / 2

theorem LWalk.midPoint_re (W : LWalk) (k : ℕ) :
    (W.midPoint k).re = ((W.v k).1 * W.c + (W.v (k + 1)).1 * W.c) / 2 := by
  have h : ∀ j : ℕ, (W.pt j).re = (W.v j).1 * W.c := by
    intro j
    show (W.c * gpt (W.v j)).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, gpt_re, gpt_im]
    ring
  simp only [LWalk.midPoint, Complex.add_re, Complex.div_ofNat_re, h]

theorem LWalk.midPoint_im (W : LWalk) (k : ℕ) :
    (W.midPoint k).im = ((W.v k).2 * W.c + (W.v (k + 1)).2 * W.c) / 2 := by
  have h : ∀ j : ℕ, (W.pt j).im = (W.v j).2 * W.c := by
    intro j
    show (W.c * gpt (W.v j)).im = _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, gpt_re, gpt_im]
    ring
  simp only [LWalk.midPoint, Complex.add_im, Complex.div_ofNat_im, h]

/-- The midpoint of a horizontal unit lattice edge determines that edge: it lies on `edgeH c q`
only if `q = p`. -/
theorem midH_mem_edgeH_iff {c : ℝ} (hc : 0 < c) {p q : ℤ × ℤ} :
    midH c p ∈ edgeH c q ↔ p = q := by
  constructor
  · intro h
    obtain ⟨t, ht, him, hre⟩ := edgeH_coords h
    have h2 : ((p.2 : ℝ)) * c = (q.2 : ℝ) * c := by rw [← midH_im, him]
    have hpq2 : p.2 = q.2 := by
      exact_mod_cast (mul_right_cancel₀ (ne_of_gt hc) h2)
    have h1 : ((p.1 : ℝ) + 1 / 2) = (q.1 : ℝ) + t := by
      have hthis : ((p.1 : ℝ) + 1 / 2) * c = ((q.1 : ℝ) + t) * c := by
        have h' := hre
        rw [midH_re] at h'
        rw [h']; ring
      exact mul_right_cancel₀ (ne_of_gt hc) hthis
    have hk : ((p.1 - q.1 : ℤ) : ℝ) = t - 1 / 2 := by
      push_cast
      linarith [h1]
    have hb : |t - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hz : (p.1 - q.1 : ℤ) = 0 := by
      by_contra hc'
      have h1' : (1 : ℝ) ≤ |((p.1 - q.1 : ℤ) : ℝ)| := one_le_abs_intCast hc'
      rw [hk] at h1'
      linarith
    exact Prod.ext (by omega) hpq2
  · rintro rfl
    rw [edgeH, segment_eq_image]
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, midH,
        gpt_re, gpt_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
        mul_zero, one_mul, mul_one, zero_add, add_zero, sub_zero, Prod.fst_add, Prod.snd_add] <;>
      push_cast <;> ring

/-- If the `k`-th edge realizes the horizontal canonical edge `edgeH c p`, its midpoint is
`midH c p`. -/
theorem midPoint_eq_midH_of_range {W : LWalk} {k : ℕ} (hk : k < W.n) {p : ℤ × ℤ}
    (h : Set.range (W.edge k) = edgeH W.c p) : W.midPoint k = midH W.c p := by
  have hc : 0 < W.c := W.cpos
  have hmem : ∀ j : ℕ, W.c • gpt (W.v j) ∈ edgeH W.c p → W.v j = p ∨ W.v j = p + (1, 0) := by
    intro j hj
    exact (smul_gpt_mem_edgeH_iff W.c hc p (W.v j)).mp hj
  have hk1 : W.v k = p ∨ W.v k = p + (1, 0) := by
    apply hmem
    rw [← h]
    exact ⟨0, by simp [LWalk.edge, LWalk.pt, Complex.real_smul]⟩
  have hk2 : W.v (k + 1) = p ∨ W.v (k + 1) = p + (1, 0) := by
    apply hmem
    rw [← h]
    exact ⟨1, by simp [LWalk.edge, LWalk.pt, Complex.real_smul]⟩
  have hcomp : (W.v k).2 = p.2 ∧ (W.v (k + 1)).2 = p.2 := by
    constructor
    · rcases hk1 with h1 | h1 <;> rw [h1] <;> simp
    · rcases hk2 with h2 | h2 <;> rw [h2] <;> simp
  have hne : W.v k ≠ W.v (k + 1) := gridStep_ne (W.step k hk)
  have hsum : (W.v k).1 + (W.v (k + 1)).1 = 2 * p.1 + 1 := by
    rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]; simp only [Prod.fst_add, Prod.snd_add, add_zero]; ring
    · rw [h1, h2]; simp only [Prod.fst_add, Prod.snd_add, add_zero]; ring
    · exact absurd (h1.trans h2.symm) hne
  apply Complex.ext
  · rw [LWalk.midPoint_re, midH_re]
    have h2 : ((W.v k).1 : ℝ) * W.c + ((W.v (k + 1)).1 : ℝ) * W.c
        = 2 * (((p.1 : ℝ) + 1 / 2) * W.c) := by
      rw [← add_mul, ← Int.cast_add, hsum]
      push_cast
      ring
    linarith
  · rw [LWalk.midPoint_im, midH_im, hcomp.1, hcomp.2]
    ring

/-- If the `k`-th edge realizes the vertical canonical edge `edgeV c p`, its midpoint is
`midV c p`. -/
theorem midPoint_eq_midV_of_range {W : LWalk} {k : ℕ} (hk : k < W.n) {p : ℤ × ℤ}
    (h : Set.range (W.edge k) = edgeV W.c p) : W.midPoint k = midV W.c p := by
  have hc : 0 < W.c := W.cpos
  have hmem : ∀ j : ℕ, W.c • gpt (W.v j) ∈ edgeV W.c p → W.v j = p ∨ W.v j = p + (0, 1) := by
    intro j hj
    exact (smul_gpt_mem_edgeV_iff W.c hc p (W.v j)).mp hj
  have hk1 : W.v k = p ∨ W.v k = p + (0, 1) := by
    apply hmem
    rw [← h]
    exact ⟨0, by simp [LWalk.edge, LWalk.pt, Complex.real_smul]⟩
  have hk2 : W.v (k + 1) = p ∨ W.v (k + 1) = p + (0, 1) := by
    apply hmem
    rw [← h]
    exact ⟨1, by simp [LWalk.edge, LWalk.pt, Complex.real_smul]⟩
  have hcomp : (W.v k).1 = p.1 ∧ (W.v (k + 1)).1 = p.1 := by
    constructor
    · rcases hk1 with h1 | h1 <;> rw [h1] <;> simp
    · rcases hk2 with h2 | h2 <;> rw [h2] <;> simp
  have hne : W.v k ≠ W.v (k + 1) := gridStep_ne (W.step k hk)
  have hsum : (W.v k).2 + (W.v (k + 1)).2 = 2 * p.2 + 1 := by
    rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]; simp only [Prod.fst_add, Prod.snd_add, add_zero]; ring
    · rw [h1, h2]; simp only [Prod.fst_add, Prod.snd_add, add_zero]; ring
    · exact absurd (h1.trans h2.symm) hne
  apply Complex.ext
  · rw [LWalk.midPoint_re, midV_re, hcomp.1, hcomp.2]
    ring
  · rw [LWalk.midPoint_im, midV_im]
    have h2 : ((W.v k).2 : ℝ) * W.c + ((W.v (k + 1)).2 : ℝ) * W.c
        = 2 * (((p.2 : ℝ) + 1 / 2) * W.c) := by
      rw [← add_mul, ← Int.cast_add, hsum]
      push_cast
      ring
    linarith

/-- **Local structure at an edge midpoint.**  The ball of radius `W.c/4` around the midpoint of
the `k`-th edge meets the trace of the walk only in that edge. -/
theorem exists_ball_inter_edge (W : LWalk) {k : ℕ} (hk : k < W.n) :
    Metric.ball (W.midPoint k) (W.c / 4) ∩ Set.range W.curve
      = Metric.ball (W.midPoint k) (W.c / 4) ∩ Set.range (W.edge k) := by
  have hc : 0 < W.c := W.cpos
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨hzball, hz⟩
    rw [mem_range_curve_iff] at hz
    have hlt : dist z (W.midPoint k) < W.c / 4 := hzball
    rcases hz with hz0 | ⟨k', hk', hz'⟩
    · exfalso
      have hpt : W.pt 0 = W.c • gpt (W.v 0) := by rw [LWalk.pt, Complex.real_smul]
      rw [hz0, hpt] at hlt
      rcases edge_range_eq_edgeH_or_edgeV W hk with ⟨p, hp⟩ | ⟨p, hp⟩
      · rw [midPoint_eq_midH_of_range hk hp] at hlt
        have := midH_le_dist_gpt (c := W.c) hc (p := p) (q := W.v 0)
        linarith
      · rw [midPoint_eq_midV_of_range hk hp] at hlt
        have := midV_le_dist_gpt (c := W.c) hc (p := p) (q := W.v 0)
        linarith
    · by_cases hsame : Set.range (W.edge k') = Set.range (W.edge k)
      · rw [hsame] at hz'
        exact ⟨hzball, hz'⟩
      · exfalso
        have hpq_of : ∀ {p q : ℤ × ℤ}, Set.range (W.edge k') = edgeH W.c q →
            Set.range (W.edge k) = edgeH W.c p → p ≠ q := by
          intro p q hq hp hpq
          exact hsame (by rw [hq, hp, hpq])
        have hpqV_of : ∀ {p q : ℤ × ℤ}, Set.range (W.edge k') = edgeV W.c q →
            Set.range (W.edge k) = edgeV W.c p → p ≠ q := by
          intro p q hq hp hpq
          exact hsame (by rw [hq, hp, hpq])
        rcases edge_range_eq_edgeH_or_edgeV W hk with ⟨p, hp⟩ | ⟨p, hp⟩
        · rw [midPoint_eq_midH_of_range hk hp] at hlt
          rcases edge_range_eq_edgeH_or_edgeV W hk' with ⟨q, hq⟩ | ⟨q, hq⟩
          · rw [hq] at hz'
            have := midH_le_dist_edgeH hc (hpq_of hq hp) hz'
            linarith
          · rw [hq] at hz'
            have := midH_le_dist_edgeV (p := p) hc hz'
            linarith
        · rw [midPoint_eq_midV_of_range hk hp] at hlt
          rcases edge_range_eq_edgeH_or_edgeV W hk' with ⟨q, hq⟩ | ⟨q, hq⟩
          · rw [hq] at hz'
            have := midV_le_dist_edgeH (p := p) hc hz'
            linarith
          · rw [hq] at hz'
            have := midV_le_dist_edgeV hc (hpqV_of hq hp) hz'
            linarith
  · rintro z ⟨hzball, hz⟩
    exact ⟨hzball, edge_range_subset_curve W hk hz⟩

end

end Work.Smooth.JordanSeparation
