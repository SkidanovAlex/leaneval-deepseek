import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.CompletePartialOrder

namespace Commons.MeasureTheory.Integral

open Filter Set MeasureTheory
open scoped Topology

/-!
# Pasting two absolutely continuous functions

If `f` is absolutely continuous on `uIcc a c` and `g` is absolutely continuous on `uIcc c b` with
`f c = g c`, then the function obtained by pasting `f` on `(-∞, c]` with `g` on `(c, ∞)` is
absolutely continuous on `uIcc a b`.

The proof is a direct `ε`-`δ` argument: given a family `E` of pairwise disjoint intervals in
`uIcc a b` of small total length, each interval is split at `c` into its part lying in
`(-∞, c]` (the "`f`-part", `fpiece`) and its part lying in `[c, ∞)` (the "`g`-part", `gpiece`).
The `f`-parts form an admissible family for `f` on `uIcc a c` (they are still pairwise disjoint
and stay within `uIcc a c`), and likewise the `g`-parts for `g` on `uIcc c b`; their total lengths
are bounded by the total length of `E`.  Finally `dist` across the splitting point is controlled
by `f c = g c` and the triangle inequality.
-/

/-- If `min a b ≤ min a' b'` and `max a' b' ≤ max a b` then `uIoc a' b' ⊆ uIoc a b`. -/
lemma uIoc_subset_uIoc_of_minmax {a b a' b' : ℝ} (hmn : min a b ≤ min a' b')
    (hmx : max a' b' ≤ max a b) : uIoc a' b' ⊆ uIoc a b := by
  rw [uIoc, uIoc]
  exact Ioc_subset_Ioc hmn hmx

/-- The part of the unordered interval with endpoints `p.1`, `p.2` which lies in `(-∞, c]`,
encoded as a pair of endpoints. -/
noncomputable def fpiece (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ c then (if p.2 ≤ c then p else (p.1, c))
  else (if p.2 ≤ c then (p.2, c) else (c, c))

/-- The part of the unordered interval with endpoints `p.1`, `p.2` which lies in `[c, ∞)`,
encoded as a pair of endpoints. -/
noncomputable def gpiece (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ c then (if p.2 ≤ c then (c, c) else (c, p.2))
  else (if p.2 ≤ c then (c, p.1) else p)

lemma fpiece_of_le_le {c x y : ℝ} (h₁ : x ≤ c) (h₂ : y ≤ c) : fpiece c (x, y) = (x, y) := by
  simp only [fpiece, if_pos h₁, if_pos h₂]

lemma fpiece_of_le_lt {c x y : ℝ} (h₁ : x ≤ c) (h₂ : c < y) : fpiece c (x, y) = (x, c) := by
  simp only [fpiece, if_pos h₁, if_neg (not_le_of_gt h₂)]

lemma fpiece_of_lt_le {c x y : ℝ} (h₁ : c < x) (h₂ : y ≤ c) : fpiece c (x, y) = (y, c) := by
  simp only [fpiece, if_neg (not_le_of_gt h₁), if_pos h₂]

lemma fpiece_of_lt_lt {c x y : ℝ} (h₁ : c < x) (h₂ : c < y) : fpiece c (x, y) = (c, c) := by
  simp only [fpiece, if_neg (not_le_of_gt h₁), if_neg (not_le_of_gt h₂)]

lemma gpiece_of_le_le {c x y : ℝ} (h₁ : x ≤ c) (h₂ : y ≤ c) : gpiece c (x, y) = (c, c) := by
  simp only [gpiece, if_pos h₁, if_pos h₂]

lemma gpiece_of_le_lt {c x y : ℝ} (h₁ : x ≤ c) (h₂ : c < y) : gpiece c (x, y) = (c, y) := by
  simp only [gpiece, if_pos h₁, if_neg (not_le_of_gt h₂)]

lemma gpiece_of_lt_le {c x y : ℝ} (h₁ : c < x) (h₂ : y ≤ c) : gpiece c (x, y) = (c, x) := by
  simp only [gpiece, if_neg (not_le_of_gt h₁), if_pos h₂]

lemma gpiece_of_lt_lt {c x y : ℝ} (h₁ : c < x) (h₂ : c < y) : gpiece c (x, y) = (x, y) := by
  simp only [gpiece, if_neg (not_le_of_gt h₁), if_neg (not_le_of_gt h₂)]

/-- The `f`-part of an interval is contained in the interval. -/
lemma fpiece_uIoc_subset (c : ℝ) (p : ℝ × ℝ) :
    uIoc (fpiece c p).1 (fpiece c p).2 ⊆ uIoc p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x c with h₁ | h₁
  · rcases le_or_gt y c with h₂ | h₂
    · rw [fpiece_of_le_le h₁ h₂]
    · have h₂' : c < y := h₂
      have hxy : x ≤ y := le_of_lt (lt_of_le_of_lt h₁ h₂')
      rw [fpiece_of_le_lt h₁ h₂', uIoc, uIoc, min_eq_left h₁, max_eq_right h₁, min_eq_left hxy,
        max_eq_right hxy]
      exact Ioc_subset_Ioc le_rfl (le_of_lt h₂')
  · rcases le_or_gt y c with h₂ | h₂
    · have hyx : y ≤ x := le_of_lt (lt_of_le_of_lt h₂ h₁)
      rw [fpiece_of_lt_le h₁ h₂, uIoc, uIoc, min_eq_left h₂, max_eq_right h₂, min_eq_right hyx,
        max_eq_left hyx]
      exact Ioc_subset_Ioc le_rfl (le_of_lt h₁)
    · rw [fpiece_of_lt_lt h₁ h₂, uIoc, min_self, max_self, Ioc_self]
      exact empty_subset _

/-- The `g`-part of an interval is contained in the interval. -/
lemma gpiece_uIoc_subset (c : ℝ) (p : ℝ × ℝ) :
    uIoc (gpiece c p).1 (gpiece c p).2 ⊆ uIoc p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x c with h₁ | h₁
  · rcases le_or_gt y c with h₂ | h₂
    · rw [gpiece_of_le_le h₁ h₂, uIoc, min_self, max_self, Ioc_self]
      exact empty_subset _
    · have h₂' : c < y := h₂
      have hxy : x ≤ y := le_of_lt (lt_of_le_of_lt h₁ h₂')
      rw [gpiece_of_le_lt h₁ h₂', uIoc, uIoc, min_eq_left (le_of_lt h₂'), max_eq_right (le_of_lt h₂'),
        min_eq_left hxy, max_eq_right hxy]
      exact Ioc_subset_Ioc h₁ le_rfl
  · rcases le_or_gt y c with h₂ | h₂
    · have hyx : y ≤ x := le_of_lt (lt_of_le_of_lt h₂ h₁)
      rw [gpiece_of_lt_le h₁ h₂]
      change uIoc c x ⊆ uIoc x y
      rw [uIoc, uIoc, min_eq_left (le_of_lt h₁), max_eq_right (le_of_lt h₁), min_eq_right hyx,
        max_eq_left hyx]
      exact Ioc_subset_Ioc h₂ le_rfl
    · rw [gpiece_of_lt_lt h₁ h₂]

/-- The `f`-part of an interval inside `Icc a b` stays inside `Icc a c`. -/
lemma fpiece_mem_Icc {a b c : ℝ} (hac : a ≤ c) {p : ℝ × ℝ} (h₁ : p.1 ∈ Icc a b)
    (h₂ : p.2 ∈ Icc a b) : (fpiece c p).1 ∈ Icc a c ∧ (fpiece c p).2 ∈ Icc a c := by
  obtain ⟨x, y⟩ := p
  rw [mem_Icc] at h₁ h₂
  rcases le_or_gt x c with hx | hx
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_le_le hx hy]
      exact ⟨⟨h₁.1, hx⟩, ⟨h₂.1, hy⟩⟩
    · rw [fpiece_of_le_lt hx hy]
      exact ⟨⟨h₁.1, hx⟩, hac, le_rfl⟩
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_lt_le hx hy]
      exact ⟨⟨h₂.1, hy⟩, hac, le_rfl⟩
    · rw [fpiece_of_lt_lt hx hy]
      exact ⟨⟨hac, le_rfl⟩, hac, le_rfl⟩

/-- The `g`-part of an interval inside `Icc a b` stays inside `Icc c b`. -/
lemma gpiece_mem_Icc {a b c : ℝ} (hcb : c ≤ b) {p : ℝ × ℝ} (h₁ : p.1 ∈ Icc a b)
    (h₂ : p.2 ∈ Icc a b) : (gpiece c p).1 ∈ Icc c b ∧ (gpiece c p).2 ∈ Icc c b := by
  obtain ⟨x, y⟩ := p
  rw [mem_Icc] at h₁ h₂
  rcases le_or_gt x c with hx | hx
  · rcases le_or_gt y c with hy | hy
    · rw [gpiece_of_le_le hx hy]
      exact ⟨⟨le_rfl, hcb⟩, le_rfl, hcb⟩
    · rw [gpiece_of_le_lt hx hy]
      exact ⟨⟨le_rfl, hcb⟩, ⟨le_of_lt hy, h₂.2⟩⟩
  · rcases le_or_gt y c with hy | hy
    · rw [gpiece_of_lt_le hx hy]
      exact ⟨⟨le_rfl, hcb⟩, ⟨le_of_lt hx, h₁.2⟩⟩
    · rw [gpiece_of_lt_lt hx hy]
      exact ⟨⟨le_of_lt hx, h₁.2⟩, ⟨le_of_lt hy, h₂.2⟩⟩

/-- The length of the `f`-part of an interval is at most the length of the interval. -/
lemma fpiece_dist_le (c : ℝ) (p : ℝ × ℝ) :
    dist (fpiece c p).1 (fpiece c p).2 ≤ dist p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x c with hx | hx
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_le_le hx hy]
    · have hy' : c < y := hy
      rw [fpiece_of_le_lt hx hy']
      change dist x c ≤ dist x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_lt_le hx hy]
      change dist y c ≤ dist x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [fpiece_of_lt_lt hx hy]
      simp

/-- The length of the `g`-part of an interval is at most the length of the interval. -/
lemma gpiece_dist_le (c : ℝ) (p : ℝ × ℝ) :
    dist (gpiece c p).1 (gpiece c p).2 ≤ dist p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x c with hx | hx
  · rcases le_or_gt y c with hy | hy
    · rw [gpiece_of_le_le hx hy]
      simp
    · have hy' : c < y := hy
      have hxy : x ≤ y := le_of_lt (lt_of_le_of_lt hx hy')
      rw [gpiece_of_le_lt hx hy']
      change dist c y ≤ dist x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rcases le_or_gt y c with hy | hy
    · have hyx : y ≤ x := le_of_lt (lt_of_le_of_lt hy hx)
      rw [gpiece_of_lt_le hx hy]
      change dist c x ≤ dist x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [gpiece_of_lt_lt hx hy]

/-- The distance between the values of the pasted function on the two endpoints of an interval is
bounded by the sum of the contributions of the `f`-part and the `g`-part. -/
theorem dist_glue_le {F : Type*} [NormedAddCommGroup F] {f g : ℝ → F} {c : ℝ} (hfc : f c = g c)
    (p : ℝ × ℝ) :
    dist (if p.1 ≤ c then f p.1 else g p.1) (if p.2 ≤ c then f p.2 else g p.2)
      ≤ dist (f (fpiece c p).1) (f (fpiece c p).2)
        + dist (g (gpiece c p).1) (g (gpiece c p).2) := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x c with hx | hx
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_le_le hx hy, gpiece_of_le_le hx hy, if_pos hx, if_pos hy]
      simp
    · have hy' : c < y := hy
      rw [fpiece_of_le_lt hx hy', gpiece_of_le_lt hx hy', if_pos hx, if_neg (not_le_of_gt hy')]
      have e : dist (f c) (g y) = dist (g c) (g y) := by rw [hfc]
      rw [← e]
      exact dist_triangle _ _ _
  · rcases le_or_gt y c with hy | hy
    · rw [fpiece_of_lt_le hx hy, gpiece_of_lt_le hx hy, if_neg (not_le_of_gt hx), if_pos hy]
      have e₁ : dist (g x) (g c) = dist (g c) (g x) := dist_comm _ _
      have e₂ : dist (g c) (f y) = dist (f y) (f c) := by rw [dist_comm, ← hfc]
      calc dist (g x) (f y) ≤ dist (g x) (g c) + dist (g c) (f y) := dist_triangle _ _ _
        _ = dist (f y) (f c) + dist (g c) (g x) := by rw [e₁, e₂]; ring
    · rw [fpiece_of_lt_lt hx hy, gpiece_of_lt_lt hx hy, if_neg (not_le_of_gt hx),
        if_neg (not_le_of_gt hy)]
      simp

theorem absolutelyContinuousOnInterval_concat {F : Type*} [NormedAddCommGroup F]
    {f g : ℝ → F} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hfc : f c = g c)
    (hf : AbsolutelyContinuousOnInterval f a c) (hg : AbsolutelyContinuousOnInterval g c b) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => if x ≤ c then f x else g x) a b := by
  have hab : a ≤ b := le_trans hac hcb
  rw [absolutelyContinuousOnInterval_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hg (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun E hE hlen => ?_⟩
  rw [AbsolutelyContinuousOnInterval.disjWithin] at hE
  obtain ⟨hEend, hEdisj⟩ := hE
  have hEend' : ∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ Icc a b ∧ (E.2 i).2 ∈ Icc a b := by
    intro i hi
    obtain ⟨h₁, h₂⟩ := hEend i hi
    exact ⟨by simpa [uIcc_of_le hab] using h₁, by simpa [uIcc_of_le hab] using h₂⟩
  let fp : ℕ → ℝ × ℝ := fun i => fpiece c (E.2 i)
  let gp : ℕ → ℝ × ℝ := fun i => gpiece c (E.2 i)
  have hEf : (E.1, fp) ∈ AbsolutelyContinuousOnInterval.disjWithin a c := by
    rw [AbsolutelyContinuousOnInterval.disjWithin]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨h₁, h₂⟩ := fpiece_mem_Icc hac (hEend' i hi).1 (hEend' i hi).2
      exact ⟨by simpa [uIcc_of_le hac] using h₁, by simpa [uIcc_of_le hac] using h₂⟩
    · exact hEdisj.mono fun i => fpiece_uIoc_subset c (E.2 i)
  have hEg : (E.1, gp) ∈ AbsolutelyContinuousOnInterval.disjWithin c b := by
    rw [AbsolutelyContinuousOnInterval.disjWithin]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨h₁, h₂⟩ := gpiece_mem_Icc hcb (hEend' i hi).1 (hEend' i hi).2
      exact ⟨by simpa [uIcc_of_le hcb] using h₁, by simpa [uIcc_of_le hcb] using h₂⟩
    · exact hEdisj.mono fun i => gpiece_uIoc_subset c (E.2 i)
  have hlenf : ∑ i ∈ Finset.range E.1, dist (fp i).1 (fp i).2 < δ₁ := by
    have h₁ : ∑ i ∈ Finset.range E.1, dist (fp i).1 (fp i).2
        ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
      Finset.sum_le_sum fun i _ => fpiece_dist_le c (E.2 i)
    linarith [min_le_left δ₁ δ₂]
  have hleng : ∑ i ∈ Finset.range E.1, dist (gp i).1 (gp i).2 < δ₂ := by
    have h₁ : ∑ i ∈ Finset.range E.1, dist (gp i).1 (gp i).2
        ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
      Finset.sum_le_sum fun i _ => gpiece_dist_le c (E.2 i)
    linarith [min_le_right δ₁ δ₂]
  have hSf : ∑ i ∈ Finset.range E.1, dist (f (fp i).1) (f (fp i).2) < ε / 2 :=
    hδ₁ (E.1, fp) hEf hlenf
  have hSg : ∑ i ∈ Finset.range E.1, dist (g (gp i).1) (g (gp i).2) < ε / 2 :=
    hδ₂ (E.1, gp) hEg hleng
  calc ∑ i ∈ Finset.range E.1,
        dist ((fun x : ℝ => if x ≤ c then f x else g x) (E.2 i).1)
          ((fun x : ℝ => if x ≤ c then f x else g x) (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1,
          (dist (f (fp i).1) (f (fp i).2) + dist (g (gp i).1) (g (gp i).2)) :=
        Finset.sum_le_sum fun i _ => dist_glue_le hfc (E.2 i)
    _ = (∑ i ∈ Finset.range E.1, dist (f (fp i).1) (f (fp i).2))
          + ∑ i ∈ Finset.range E.1, dist (g (gp i).1) (g (gp i).2) :=
        Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := add_lt_add hSf hSg
    _ = ε := by ring

end Commons.MeasureTheory.Integral