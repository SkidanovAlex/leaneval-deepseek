import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# Intersections of distinct unit lattice segments are lattice points

Two distinct unit grid segments (the closed segments joining two `IsUnitAdj` lattice points,
`adjSeg u v = segment ℝ (lpt u) (lpt v)`) can meet only in lattice points.  Equivalently, every
point of `adjSeg u v ∩ adjSeg u' v'` is of the form `lpt w` as soon as the two segments differ.

The proof writes each segment as `hSeg`- or `vSeg`-shaped (`hSeg p = segment ℝ (lpt p) (lpt p + 1)`,
`vSeg p = segment ℝ (lpt p) (lpt p + I)`), then combines the coordinate descriptions: two distinct
horizontal (resp. vertical) unit intervals with integer endpoints intersect in an integer point, and a
horizontal meets a vertical segment in a point with both coordinates integral.
-/

open Work.HornSC.CellBoundaryJordan

namespace Work.PlanarSC.JC

/-! ## Segment/`hSeg`/`vSeg` identifications -/

/-- The closed horizontal unit grid segment at `u` is the segment from `lpt u` to `lpt u + 1`. -/
lemma hSeg_eq_segment (u : ℤ × ℤ) : hSeg u = segment ℝ (lpt u) (lpt u + 1) := by
  rw [segment_eq_image]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, mem_hSeg]
  constructor
  · rintro ⟨him, hlo, hhi⟩
    refine ⟨z.re - (u.1:ℝ), ⟨⟨by linarith, by linarith⟩, ?_⟩⟩
    apply Complex.ext <;> simp [lpt]
    · ring
    · linarith [him]
  · rintro ⟨x, ⟨h0, h1⟩, hx⟩
    have hre : z.re = (u.1:ℝ) + x := by rw [← hx]; simp [lpt]; ring
    have him : z.im = (u.2:ℝ) := by rw [← hx]; simp [lpt]; ring
    refine ⟨him, by linarith, by linarith⟩

/-- The closed vertical unit grid segment at `u` is the segment from `lpt u` to `lpt u + I`. -/
lemma vSeg_eq_segment (u : ℤ × ℤ) : vSeg u = segment ℝ (lpt u) (lpt u + Complex.I) := by
  rw [segment_eq_image]
  ext z
  simp only [Set.mem_image, Set.mem_Icc, mem_vSeg]
  constructor
  · rintro ⟨him, hlo, hhi⟩
    refine ⟨z.im - (u.2:ℝ), ⟨⟨by linarith, by linarith⟩, ?_⟩⟩
    apply Complex.ext <;> simp [lpt]
    · linarith [him]
    · ring
  · rintro ⟨x, ⟨h0, h1⟩, hx⟩
    have hre : z.re = (u.1:ℝ) := by rw [← hx]; simp [lpt]; ring
    have him : z.im = (u.2:ℝ) + x := by rw [← hx]; simp [lpt]; ring
    refine ⟨hre, by linarith, by linarith⟩

lemma lpt_add_e1 (u : ℤ × ℤ) : lpt (u.1 + 1, u.2) = lpt u + 1 := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_sub_e1 (u : ℤ × ℤ) : lpt (u.1 - 1, u.2) = lpt u - 1 := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_add_e2 (u : ℤ × ℤ) : lpt (u.1, u.2 + 1) = lpt u + Complex.I := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_sub_e2 (u : ℤ × ℤ) : lpt (u.1, u.2 - 1) = lpt u - Complex.I := by
  apply Complex.ext <;> simp [lpt]

/-! ## `adjSeg` in normal form -/

lemma adjSeg_of_eq_east {u v : ℤ × ℤ} (h : v = (u.1 + 1, u.2)) : adjSeg u v = hSeg u := by
  rw [h, adjSeg, lpt_add_e1, ← hSeg_eq_segment]

lemma adjSeg_of_eq_west {u v : ℤ × ℤ} (h : v = (u.1 - 1, u.2)) :
    adjSeg u v = hSeg (u.1 - 1, u.2) := by
  rw [h, adjSeg, lpt_sub_e1, segment_symm, ← lpt_sub_e1,
      show (lpt u : ℂ) = lpt (u.1 - 1, u.2) + 1 from by rw [lpt_sub_e1]; ring,
      ← hSeg_eq_segment]

lemma adjSeg_of_eq_north {u v : ℤ × ℤ} (h : v = (u.1, u.2 + 1)) : adjSeg u v = vSeg u := by
  rw [h, adjSeg, lpt_add_e2, ← vSeg_eq_segment]

lemma adjSeg_of_eq_south {u v : ℤ × ℤ} (h : v = (u.1, u.2 - 1)) :
    adjSeg u v = vSeg (u.1, u.2 - 1) := by
  rw [h, adjSeg, lpt_sub_e2, segment_symm, ← lpt_sub_e2,
      show (lpt u : ℂ) = lpt (u.1, u.2 - 1) + Complex.I from by rw [lpt_sub_e2]; ring,
      ← vSeg_eq_segment]

/-- Any unit-adjacent pair spans a horizontal or a vertical unit grid segment. -/
lemma adjSeg_hSeg_or_vSeg {u v : ℤ × ℤ} (h : IsUnitAdj u v) :
    (∃ p, adjSeg u v = hSeg p) ∨ (∃ p, adjSeg u v = vSeg p) := by
  rcases h with h | h | h | h
  · exact Or.inl ⟨u, adjSeg_of_eq_east h⟩
  · exact Or.inl ⟨(u.1 - 1, u.2), adjSeg_of_eq_west h⟩
  · exact Or.inr ⟨u, adjSeg_of_eq_north h⟩
  · exact Or.inr ⟨(u.1, u.2 - 1), adjSeg_of_eq_south h⟩

/-! ## Intersection lemmas -/

/-- Two distinct unit intervals `[a,a+1]`, `[b,b+1]` with integer endpoints meet in an integer. -/
lemma exists_int_of_inter_unit {a b : ℤ} {x : ℝ}
    (ha : (a:ℝ) ≤ x) (ha' : x ≤ (a:ℝ) + 1) (hb : (b:ℝ) ≤ x) (hb' : x ≤ (b:ℝ) + 1)
    (hne : a ≠ b) : ∃ c : ℤ, x = (c:ℝ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨b, le_antisymm (le_trans ha' (by exact_mod_cast (show a + 1 ≤ b by omega))) hb⟩
  · exact ⟨a, le_antisymm (le_trans hb' (by exact_mod_cast (show b + 1 ≤ a by omega))) ha⟩

/-- Two distinct horizontal unit segments meet only in lattice points. -/
lemma hSeg_inter_hSeg_subset_lpt {p q : ℤ × ℤ} (hne : hSeg p ≠ hSeg q)
    {z : ℂ} (hp : z ∈ hSeg p) (hq : z ∈ hSeg q) : ∃ w : ℤ × ℤ, z = lpt w := by
  simp only [mem_hSeg] at hp hq
  obtain ⟨hpim, hp1, hp2⟩ := hp
  obtain ⟨hqim, hq1, hq2⟩ := hq
  have h12 : p.2 = q.2 := by
    have : ((p.2:ℤ):ℝ) = ((q.2:ℤ):ℝ) := by rw [← hpim, hqim]
    exact_mod_cast this
  have hpq : p.1 ≠ q.1 := fun h => hne (by rw [Prod.ext h h12])
  obtain ⟨c, hc⟩ := exists_int_of_inter_unit hp1 hp2 hq1 hq2 hpq
  exact ⟨(c, p.2), by apply Complex.ext <;> simp [lpt, hc, hpim]⟩

/-- A horizontal and a vertical unit segment meet only in lattice points. -/
lemma hSeg_inter_vSeg_subset_lpt {p q : ℤ × ℤ} {z : ℂ}
    (hp : z ∈ hSeg p) (hq : z ∈ vSeg q) : ∃ w : ℤ × ℤ, z = lpt w := by
  simp only [mem_hSeg] at hp
  simp only [mem_vSeg] at hq
  obtain ⟨hpim, _⟩ := hp
  obtain ⟨hqre, _⟩ := hq
  exact ⟨(q.1, p.2), by apply Complex.ext <;> simp [lpt, hqre, hpim]⟩

/-- Two distinct vertical unit segments meet only in lattice points. -/
lemma vSeg_inter_vSeg_subset_lpt {p q : ℤ × ℤ} (hne : vSeg p ≠ vSeg q)
    {z : ℂ} (hp : z ∈ vSeg p) (hq : z ∈ vSeg q) : ∃ w : ℤ × ℤ, z = lpt w := by
  simp only [mem_vSeg] at hp hq
  obtain ⟨hpre, hp1, hp2⟩ := hp
  obtain ⟨hqre, hq1, hq2⟩ := hq
  have h12 : p.1 = q.1 := by
    have : ((p.1:ℤ):ℝ) = ((q.1:ℤ):ℝ) := by rw [← hpre, hqre]
    exact_mod_cast this
  have hpq : p.2 ≠ q.2 := fun h => hne (by rw [Prod.ext h12 h])
  obtain ⟨c, hc⟩ := exists_int_of_inter_unit hp1 hp2 hq1 hq2 hpq
  exact ⟨(p.1, c), by apply Complex.ext <;> simp [lpt, hpre, hc]⟩

/-! ## The target -/

theorem adjSeg_inter_subset_lpt {u v u' v' : ℤ × ℤ}
    (hu : Work.HornSC.CellBoundaryJordan.IsUnitAdj u v)
    (hu' : Work.HornSC.CellBoundaryJordan.IsUnitAdj u' v')
    (hne : Work.HornSC.CellBoundaryJordan.adjSeg u v ≠
      Work.HornSC.CellBoundaryJordan.adjSeg u' v')
    {z : ℂ} (hz : z ∈ Work.HornSC.CellBoundaryJordan.adjSeg u v)
    (hz' : z ∈ Work.HornSC.CellBoundaryJordan.adjSeg u' v') :
    ∃ w : ℤ × ℤ, z = Work.HornSC.CellBoundaryJordan.lpt w := by
  rcases adjSeg_hSeg_or_vSeg hu with ⟨p, hp⟩ | ⟨p, hp⟩ <;>
    rcases adjSeg_hSeg_or_vSeg hu' with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [hp] at hz; rw [hq] at hz'; rw [hp, hq] at hne
    exact hSeg_inter_hSeg_subset_lpt hne hz hz'
  · rw [hp] at hz; rw [hq] at hz'
    exact hSeg_inter_vSeg_subset_lpt hz hz'
  · rw [hp] at hz; rw [hq] at hz'
    exact hSeg_inter_vSeg_subset_lpt hz' hz
  · rw [hp] at hz; rw [hq] at hz'; rw [hp, hq] at hne
    exact vSeg_inter_vSeg_subset_lpt hne hz hz'

end Work.PlanarSC.JC
