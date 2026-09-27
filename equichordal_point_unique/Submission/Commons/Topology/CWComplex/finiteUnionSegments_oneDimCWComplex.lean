import Mathlib.Topology.MetricSpace.HausdorffDistance
import Submission.Commons.Topology.Plane.exists_cwComplex_of_finset_segments

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Set Function Metric
open scoped Topology Classical

namespace Commons.Topology.CWComplex


lemma lineMap_sub_lineMap (a b : ℂ) (s t : ℝ) :
    AffineMap.lineMap a b s - AffineMap.lineMap a b t = (s - t : ℝ) • (b - a) := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma norm_lineMap_sub (a b : ℂ) (s t : ℝ) :
    dist (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) = |s - t| * ‖b - a‖ := by
  rw [dist_eq_norm, lineMap_sub_lineMap, norm_smul, Real.norm_eq_abs]

lemma lineMap_inj (a b : ℂ) (hab : a ≠ b) :
    Function.Injective (fun t : ℝ => AffineMap.lineMap a b t) :=
  AffineMap.lineMap_injective ℝ hab

lemma mem_segment_iff_lineMap {a b : ℂ} (z : ℂ) :
    z ∈ segment ℝ a b ↔ ∃ t ∈ Icc (0:ℝ) 1, AffineMap.lineMap a b t = z := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

lemma lineMap_eq_left_add_smul (a b : ℂ) (t : ℝ) :
    AffineMap.lineMap a b t = a + t • (b - a) := by
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul]
  push_cast
  ring

noncomputable def pc (a b z : ℂ) : ℝ := ((z - a) / (b - a)).re

lemma pc_lineMap (a b : ℂ) (hab : a ≠ b) (t : ℝ) :
    pc a b (AffineMap.lineMap a b t) = t := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have h : AffineMap.lineMap a b t - a = (t : ℂ) * (b - a) := by
    rw [lineMap_eq_left_add_smul, Complex.real_smul]
    ring
  rw [pc, h, mul_div_assoc, div_self hd, mul_one, Complex.ofReal_re]

lemma lineMap_pc_of_mem {a b z : ℂ} (hab : a ≠ b) (hz : z ∈ segment ℝ a b) :
    AffineMap.lineMap a b (pc a b z) = z := by
  obtain ⟨t, _, htz⟩ := (mem_segment_iff_lineMap z).mp hz
  rw [← htz, pc_lineMap a b hab t]

lemma pc_mem_Icc_of_mem {a b z : ℂ} (hab : a ≠ b) (hz : z ∈ segment ℝ a b) :
    pc a b z ∈ Icc (0:ℝ) 1 := by
  obtain ⟨t, ht, htz⟩ := (mem_segment_iff_lineMap z).mp hz
  rw [← htz, pc_lineMap a b hab t]
  exact ht

lemma isCompact_segment (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

lemma exists_pos_lt_dist_of_notMem_segment {a b x : ℂ} (hx : x ∉ segment ℝ a b) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ segment ℝ a b, r ≤ dist x y := by
  have hcl : IsClosed (segment ℝ a b) := (isCompact_segment a b).isClosed
  have hne : (segment ℝ a b).Nonempty := ⟨a, left_mem_segment ℝ a b⟩
  refine ⟨infDist x (segment ℝ a b), ?_, ?_⟩
  · rw [← IsClosed.notMem_iff_infDist_pos hcl hne]; exact hx
  · intro y hy
    exact infDist_le_dist_of_mem hy

noncomputable def detC (u v : ℂ) : ℝ := u.im * v.re - u.re * v.im

@[simp] lemma detC_self (u : ℂ) : detC u u = 0 := by rw [detC]; ring
@[simp] lemma detC_zero_left (v : ℂ) : detC 0 v = 0 := by rw [detC]; simp
@[simp] lemma detC_zero_right (u : ℂ) : detC u 0 = 0 := by rw [detC]; simp

lemma detC_add_left (u₁ u₂ v : ℂ) : detC (u₁ + u₂) v = detC u₁ v + detC u₂ v := by
  rw [detC, detC, detC, Complex.add_re, Complex.add_im]; ring
lemma detC_add_right (u v₁ v₂ : ℂ) : detC u (v₁ + v₂) = detC u v₁ + detC u v₂ := by
  rw [detC, detC, detC, Complex.add_re, Complex.add_im]; ring
lemma detC_sub_left (u₁ u₂ v : ℂ) : detC (u₁ - u₂) v = detC u₁ v - detC u₂ v := by
  rw [detC, detC, detC, Complex.sub_re, Complex.sub_im]; ring
lemma detC_sub_right (u v₁ v₂ : ℂ) : detC u (v₁ - v₂) = detC u v₁ - detC u v₂ := by
  rw [detC, detC, detC, Complex.sub_re, Complex.sub_im]; ring
lemma detC_ofReal_mul_left (r : ℝ) (u v : ℂ) : detC ((r : ℂ) * u) v = r * detC u v := by
  rw [detC, detC, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
lemma detC_ofReal_mul_right (r : ℝ) (u v : ℂ) : detC u ((r : ℂ) * v) = r * detC u v := by
  rw [detC, detC, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
lemma detC_eq_im (u v : ℂ) : detC u v = (u * starRingEnd ℂ v).im := by
  rw [detC, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
lemma detC_anti (u v : ℂ) : detC u v = -detC v u := by rw [detC, detC]; ring

lemma eq_lineMap_of_mem_segments {a b c d : ℂ} (hpar : detC (b - a) (d - c) ≠ 0) {x : ℂ}
    (hx : x ∈ segment ℝ a b ∩ segment ℝ c d) :
    x = AffineMap.lineMap a b (detC (c - a) (d - c) / detC (b - a) (d - c)) := by
  obtain ⟨t, -, htx⟩ := (mem_segment_iff_lineMap x).mp hx.1
  obtain ⟨u, -, hux⟩ := (mem_segment_iff_lineMap x).mp hx.2
  have h1 : x - a = (t : ℂ) * (b - a) := by
    rw [← htx, lineMap_eq_left_add_smul, Complex.real_smul]; ring
  have h2 : x - c = (u : ℂ) * (d - c) := by
    rw [← hux, lineMap_eq_left_add_smul, Complex.real_smul]; ring
  have h5 : detC (c - a) (d - c) = t * detC (b - a) (d - c) := by
    have h3 : c - a = (t : ℂ) * (b - a) - (u : ℂ) * (d - c) := by rw [← h1, ← h2]; ring
    rw [h3, detC_sub_left, detC_ofReal_mul_left, detC_ofReal_mul_left, detC_self, mul_zero,
      sub_zero]
  have h4 : t = detC (c - a) (d - c) / detC (b - a) (d - c) := by
    rw [eq_div_iff hpar]; exact h5.symm
  rw [← htx, h4]

lemma exists_smul_of_detC_eq_zero {d d' : ℂ} (hd : d ≠ 0) (h : detC d' d = 0) :
    ∃ c : ℝ, d' = c • d := by
  have hd0 : Complex.normSq d ≠ 0 := by
    intro h; exact hd (Complex.normSq_eq_zero.mp h)
  have hc : (Complex.normSq d : ℂ) ≠ 0 := by simpa using hd0
  have him : (d' * starRingEnd ℂ d).im = 0 := by rw [← detC_eq_im]; exact h
  have hreal : d' * starRingEnd ℂ d = ((d' * starRingEnd ℂ d).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hsmul : starRingEnd ℂ d * d = (Complex.normSq d : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hkey : d' * (Complex.normSq d : ℂ) = ((d' * starRingEnd ℂ d).re : ℂ) * d := by
    calc d' * (Complex.normSq d : ℂ) = d' * (starRingEnd ℂ d * d) := by rw [hsmul]
      _ = (d' * starRingEnd ℂ d) * d := by ring
      _ = ((d' * starRingEnd ℂ d).re : ℂ) * d := by
        conv_lhs => rw [hreal]
  refine ⟨(d' * starRingEnd ℂ d).re / Complex.normSq d, ?_⟩
  rw [Complex.real_smul, Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hc]
  exact hkey

lemma sub_eq_smul_sub_of_mem_segment {a b x y : ℂ}
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    ∃ u ∈ Icc (0:ℝ) 1, ∃ v ∈ Icc (0:ℝ) 1, y - x = (v - u) • (b - a) := by
  obtain ⟨u, hu, hux⟩ := (mem_segment_iff_lineMap x).mp hx
  obtain ⟨v, hv, hvy⟩ := (mem_segment_iff_lineMap y).mp hy
  exact ⟨u, hu, v, hv, by rw [← hvy, ← hux, lineMap_sub_lineMap]⟩


noncomputable def crossPt (p : (ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  AffineMap.lineMap p.1.1 p.1.2
    (detC (p.2.1 - p.1.1) (p.2.2 - p.2.1) / detC (p.1.2 - p.1.1) (p.2.2 - p.2.1))

noncomputable def vCand (S : Finset (ℂ × ℂ)) : Finset ℂ :=
  S.image (fun s => s.1) ∪ S.image (fun s => s.2) ∪ (S ×ˢ S).image crossPt

noncomputable def vSet (S : Finset (ℂ × ℂ)) : Finset ℂ :=
  (vCand S).filter (fun x => x ∈ ⋃ s ∈ S, segment ℝ s.1 s.2)

lemma mem_vCand {S : Finset (ℂ × ℂ)} {x : ℂ} :
    x ∈ vCand S ↔ (∃ s ∈ S, s.1 = x) ∨ (∃ s ∈ S, s.2 = x) ∨
      (∃ s ∈ S, ∃ s' ∈ S, crossPt (s, s') = x) := by
  have hprod : (∃ a ∈ S ×ˢ S, crossPt a = x) ↔
      (∃ s ∈ S, ∃ s' ∈ S, crossPt (s, s') = x) := by
    constructor
    · rintro ⟨a, ha, hx⟩
      rw [Finset.mem_product] at ha
      exact ⟨a.1, ha.1, a.2, ha.2, hx⟩
    · rintro ⟨s, hs, s', hs', hx⟩
      exact ⟨(s, s'), Finset.mem_product.mpr ⟨hs, hs'⟩, hx⟩
  simp only [vCand, Finset.mem_union, Finset.mem_image]
  rw [hprod]
  simp only [or_assoc]

lemma mem_vSet {S : Finset (ℂ × ℂ)} {x : ℂ} :
    x ∈ vSet S ↔ x ∈ vCand S ∧ x ∈ (⋃ s ∈ S, segment ℝ s.1 s.2) := by
  rw [vSet, Finset.mem_filter]

lemma fst_mem_vSet {S : Finset (ℂ × ℂ)} {s : ℂ × ℂ} (hs : s ∈ S) : s.1 ∈ vSet S := by
  rw [mem_vSet]
  refine ⟨?_, ?_⟩
  · rw [mem_vCand]; exact Or.inl ⟨s, hs, rfl⟩
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, left_mem_segment ℝ s.1 s.2⟩⟩

lemma snd_mem_vSet {S : Finset (ℂ × ℂ)} {s : ℂ × ℂ} (hs : s ∈ S) : s.2 ∈ vSet S := by
  rw [mem_vSet]
  refine ⟨?_, ?_⟩
  · rw [mem_vCand]; exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, right_mem_segment ℝ s.1 s.2⟩⟩

lemma mem_vSet_of_crossPt {S : Finset (ℂ × ℂ)} {s s' : ℂ × ℂ} (hs : s ∈ S) (hs' : s' ∈ S)
    {x : ℂ} (hx : x ∈ segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2)
    (hpar : detC (s.2 - s.1) (s'.2 - s'.1) ≠ 0) : x ∈ vSet S := by
  have hxc : crossPt (s, s') = x := by
    rw [crossPt]
    exact (eq_lineMap_of_mem_segments hpar hx).symm
  rw [mem_vSet]
  refine ⟨?_, ?_⟩
  · rw [mem_vCand]; exact Or.inr (Or.inr ⟨s, hs, s', hs', hxc⟩)
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, hx.1⟩⟩

lemma detC_eq_zero_of_mem_segments {S : Finset (ℂ × ℂ)} {s s' : ℂ × ℂ} (hs : s ∈ S) (hs' : s' ∈ S)
    {x : ℂ} (hx : x ∈ segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2) (hxV : x ∉ vSet S) :
    detC (s.2 - s.1) (s'.2 - s'.1) = 0 := by
  by_contra hpar
  exact hxV (mem_vSet_of_crossPt hs hs' hx hpar)




/-- A finite nonempty family of positive reals has a positive common lower bound. -/
lemma exists_pos_le_finset {ι : Type*} :
    ∀ (S : Finset ι), S.Nonempty → ∀ f : ι → ℝ, (∀ i ∈ S, 0 < f i) →
      ∃ r : ℝ, 0 < r ∧ ∀ i ∈ S, r ≤ f i := by
  intro S
  induction S using Finset.induction with
  | empty => intro h; exact absurd h (Finset.not_nonempty_empty)
  | insert a S ha ih =>
      intro h f hf
      by_cases hS : S.Nonempty
      · obtain ⟨r, hr, hrle⟩ := ih hS f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        refine ⟨min r (f a), lt_min hr (hf a (Finset.mem_insert_self a S)), ?_⟩
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact min_le_right _ _
        · exact le_trans (min_le_left _ _) (hrle i hi)
      · refine ⟨f a, hf a (Finset.mem_insert_self a S), ?_⟩
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact le_rfl
        · exact absurd ⟨i, hi⟩ hS

/-- Near a point of `⋃ S` which is not a vertex, the union of the segments agrees with any
segment through that point. -/
lemma exists_ball_subset_segment {S : Finset (ℂ × ℂ)} {x : ℂ} {s : ℂ × ℂ} (hs : s ∈ S)
    (hx : x ∈ segment ℝ s.1 s.2) (hxV : x ∉ vSet S) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ (⋃ s ∈ S, segment ℝ s.1 s.2), dist y x < r → y ∈ segment ℝ s.1 s.2 := by
  have hs12 : s.1 ≠ s.2 := by
    intro h
    have hxs1 : x = s.1 := by
      have hseg : segment ℝ s.1 s.2 = {s.1} := by rw [h, segment_same]
      rw [hseg] at hx
      exact mem_singleton_iff.mp hx
    exact hxV (hxs1 ▸ fst_mem_vSet hs)
  obtain ⟨t, htmem, htx⟩ := (mem_segment_iff_lineMap x).mp hx
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le htmem.1 with h | h
    · exfalso
      have : x = s.1 := by rw [← htx, ← h, AffineMap.lineMap_apply_zero]
      exact hxV (this ▸ fst_mem_vSet hs)
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le htmem.2 with h | h
    · exfalso
      have : x = s.2 := by rw [← htx, h, AffineMap.lineMap_apply_one]
      exact hxV (this ▸ snd_mem_vSet hs)
    · exact h
  have hd : s.2 - s.1 ≠ 0 := sub_ne_zero.mpr hs12.symm
  have hnd : 0 < ‖s.2 - s.1‖ := norm_pos_iff.mpr hd
  have hm : 0 < min t (1 - t) := lt_min ht0 (by linarith)
  have hr0 : 0 < min t (1 - t) * ‖s.2 - s.1‖ := mul_pos hm hnd
  let rho : ℂ × ℂ → ℝ := fun s' =>
    if x ∈ segment ℝ s'.1 s'.2 then min t (1 - t) * ‖s.2 - s.1‖
    else infDist x (segment ℝ s'.1 s'.2)
  have hrho : ∀ s' ∈ S, 0 < rho s' := by
    intro s' hs'
    by_cases h : x ∈ segment ℝ s'.1 s'.2
    · simp only [rho, h, if_true]; exact hr0
    · have hne : (segment ℝ s'.1 s'.2).Nonempty := ⟨s'.1, left_mem_segment ℝ s'.1 s'.2⟩
      have hcl : IsClosed (segment ℝ s'.1 s'.2) := (isCompact_segment s'.1 s'.2).isClosed
      simp only [rho, h, if_false]
      exact (IsClosed.notMem_iff_infDist_pos hcl hne).mp h
  obtain ⟨r, hrpos, hrle⟩ := exists_pos_le_finset S ⟨s, hs⟩ rho hrho
  refine ⟨r, hrpos, ?_⟩
  intro y hy hyr
  obtain ⟨s', hss'⟩ := mem_iUnion.mp hy
  obtain ⟨hs', hys'⟩ := mem_iUnion.mp hss'
  have hx' : x ∈ segment ℝ s'.1 s'.2 := by
    by_contra hx''
    have hrho_eq : rho s' = infDist x (segment ℝ s'.1 s'.2) := by
      simp only [rho, hx'', if_false]
    have h1 : r ≤ infDist x (segment ℝ s'.1 s'.2) := by rw [← hrho_eq]; exact hrle s' hs'
    have h2 : infDist x (segment ℝ s'.1 s'.2) ≤ dist x y := infDist_le_dist_of_mem hys'
    rw [dist_comm] at hyr
    linarith
  have hrho_eq : rho s' = min t (1 - t) * ‖s.2 - s.1‖ := by
    simp only [rho, hx', if_true]
  have hr_le : r ≤ min t (1 - t) * ‖s.2 - s.1‖ := by rw [← hrho_eq]; exact hrle s' hs'
  have hcol : detC (s'.2 - s'.1) (s.2 - s.1) = 0 :=
    detC_eq_zero_of_mem_segments hs' hs ⟨hx', hx⟩ hxV
  obtain ⟨c, hc⟩ := exists_smul_of_detC_eq_zero hd hcol
  obtain ⟨u, -, v, -, huv⟩ := sub_eq_smul_sub_of_mem_segment hx' hys'
  let w : ℝ := (v - u) * c
  have hw : w = (v - u) * c := rfl
  have hy_eq : y = AffineMap.lineMap s.1 s.2 (t + w) := by
    have h1 : y = x + w • (s.2 - s.1) := by
      rw [hw, show y = (y - x) + x by abel, huv, hc, smul_smul]
      abel
    rw [h1, ← htx, lineMap_eq_left_add_smul, lineMap_eq_left_add_smul, add_smul]
    abel
  have hdist : dist y x = |w| * ‖s.2 - s.1‖ := by
    rw [hy_eq, ← htx, norm_lineMap_sub]
    norm_num
  have hwlt : |w| < min t (1 - t) := by
    have h1 : |w| * ‖s.2 - s.1‖ < r := by rw [← hdist]; exact hyr
    exact lt_of_mul_lt_mul_right (lt_of_lt_of_le h1 hr_le) hnd.le
  have ht' : t + w ∈ Icc (0:ℝ) 1 := by
    have h1 : |w| < min t (1 - t) := hwlt
    have h2 : t + w < 1 := by
      have := (abs_lt.mp h1).2
      have hmin : min t (1 - t) ≤ 1 - t := min_le_right _ _
      linarith
    have h3 : 0 < t + w := by
      have := (abs_lt.mp h1).1
      have hmin : min t (1 - t) ≤ t := min_le_left _ _
      linarith
    exact ⟨h3.le, h2.le⟩
  exact (mem_segment_iff_lineMap y).mpr ⟨t + w, ht', hy_eq.symm⟩

/-- A point of the union of the segments which is not a vertex lies in the open segment joining
two adjacent vertices. -/
lemma exists_adjacent_vertices {S : Finset (ℂ × ℂ)} {x : ℂ}
    (hx : x ∈ ⋃ s ∈ S, segment ℝ s.1 s.2) (hxV : x ∉ vSet S) :
    ∃ u ∈ vSet S, ∃ v ∈ vSet S, u ≠ v ∧ x ∈ openSegment ℝ u v ∧
      openSegment ℝ u v ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧
      Disjoint (openSegment ℝ u v) (vSet S : Set ℂ) := by
  obtain ⟨s, hss⟩ := mem_iUnion.mp hx
  obtain ⟨hs, hxs⟩ := mem_iUnion.mp hss
  have hs12 : s.1 ≠ s.2 := by
    intro h
    have hxs1 : x = s.1 := by
      have hseg : segment ℝ s.1 s.2 = {s.1} := by rw [h, segment_same]
      rw [hseg] at hxs
      exact mem_singleton_iff.mp hxs
    exact hxV (hxs1 ▸ fst_mem_vSet hs)
  obtain ⟨t, htmem, htx⟩ := (mem_segment_iff_lineMap x).mp hxs
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le htmem.1 with h | h
    · exfalso
      have : x = s.1 := by rw [← htx, ← h, AffineMap.lineMap_apply_zero]
      exact hxV (this ▸ fst_mem_vSet hs)
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le htmem.2 with h | h
    · exfalso
      have : x = s.2 := by rw [← htx, h, AffineMap.lineMap_apply_one]
      exact hxV (this ▸ snd_mem_vSet hs)
    · exact h
  let T : Finset ℝ := ((vSet S).filter (fun z => z ∈ segment ℝ s.1 s.2)).image (pc s.1 s.2)
  have hT_sub : ∀ t' ∈ T, t' ∈ Icc (0:ℝ) 1 := by
    intro t' ht'
    obtain ⟨z, hz, hzpc⟩ := Finset.mem_image.mp ht'
    rw [Finset.mem_filter] at hz
    rw [← hzpc]
    exact pc_mem_Icc_of_mem hs12 hz.2
  have hT0 : (0:ℝ) ∈ T := by
    refine Finset.mem_image.mpr ⟨s.1, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨fst_mem_vSet hs, left_mem_segment ℝ s.1 s.2⟩
    · rw [pc]; simp
  have hT1 : (1:ℝ) ∈ T := by
    refine Finset.mem_image.mpr ⟨s.2, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨snd_mem_vSet hs, right_mem_segment ℝ s.1 s.2⟩
    · rw [pc, div_self (sub_ne_zero.mpr hs12.symm)]
      simp
  have htT : t ∉ T := by
    intro ht'
    obtain ⟨z, hz, hzpc⟩ := Finset.mem_image.mp ht'
    rw [Finset.mem_filter] at hz
    have hzx : z = x := by rw [← lineMap_pc_of_mem hs12 hz.2, hzpc, htx]
    exact hxV (hzx ▸ hz.1)
  obtain ⟨a, haT, hat, halow⟩ : ∃ a ∈ T, a < t ∧ ∀ t' ∈ T, t' < t → t' ≤ a := by
    have hne : (T.filter (fun t' => t' < t)).Nonempty :=
      ⟨0, by rw [Finset.mem_filter]; exact ⟨hT0, ht0⟩⟩
    refine ⟨(T.filter (fun t' => t' < t)).max' hne, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    · intro t' ht' ht'lt
      exact Finset.le_max' _ t' (Finset.mem_filter.mpr ⟨ht', ht'lt⟩)
  obtain ⟨b, hbT, htb, habig⟩ : ∃ b ∈ T, t < b ∧ ∀ t' ∈ T, t < t' → b ≤ t' := by
    have hne : (T.filter (fun t' => t < t')).Nonempty :=
      ⟨1, by rw [Finset.mem_filter]; exact ⟨hT1, ht1⟩⟩
    refine ⟨(T.filter (fun t' => t < t')).min' hne, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    · intro t' ht' ht'gt
      exact Finset.min'_le _ t' (Finset.mem_filter.mpr ⟨ht', ht'gt⟩)
  have hab : a < b := lt_trans hat htb
  have ha0 : 0 ≤ a := (hT_sub a haT).1
  have hb1 : b ≤ 1 := (hT_sub b hbT).2
  obtain ⟨u, huV, hus, hua⟩ : ∃ u ∈ vSet S, u ∈ segment ℝ s.1 s.2 ∧
      AffineMap.lineMap s.1 s.2 a = u := by
    obtain ⟨z, hz, hzpc⟩ := Finset.mem_image.mp haT
    rw [Finset.mem_filter] at hz
    exact ⟨z, hz.1, hz.2, by rw [← hzpc]; exact lineMap_pc_of_mem hs12 hz.2⟩
  obtain ⟨v, hvV, hvs, hvb⟩ : ∃ v ∈ vSet S, v ∈ segment ℝ s.1 s.2 ∧
      AffineMap.lineMap s.1 s.2 b = v := by
    obtain ⟨z, hz, hzpc⟩ := Finset.mem_image.mp hbT
    rw [Finset.mem_filter] at hz
    exact ⟨z, hz.1, hz.2, by rw [← hzpc]; exact lineMap_pc_of_mem hs12 hz.2⟩
  have huv : u ≠ v := by
    intro h
    have : AffineMap.lineMap s.1 s.2 a = AffineMap.lineMap s.1 s.2 b := by rw [hua, hvb, h]
    exact absurd (lineMap_inj s.1 s.2 hs12 this) (ne_of_lt hab)
  have hxos : x ∈ openSegment ℝ u v := by
    rw [← hua, ← hvb, ← image_openSegment ℝ (AffineMap.lineMap s.1 s.2) a b,
      openSegment_eq_Ioo hab]
    exact ⟨t, ⟨hat, htb⟩, htx⟩
  have hosY : openSegment ℝ u v ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2) := by
    rw [← hua, ← hvb, ← image_openSegment ℝ (AffineMap.lineMap s.1 s.2) a b,
      openSegment_eq_Ioo hab]
    rintro y ⟨t', ht', rfl⟩
    exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs,
      (mem_segment_iff_lineMap _).mpr ⟨t', ⟨le_trans ha0 ht'.1.le, le_trans ht'.2.le hb1⟩, rfl⟩⟩⟩
  have hosV : Disjoint (openSegment ℝ u v) (vSet S : Set ℂ) := by
    rw [Set.disjoint_left]
    intro z hz hzV
    rw [← hua, ← hvb, ← image_openSegment ℝ (AffineMap.lineMap s.1 s.2) a b,
      openSegment_eq_Ioo hab] at hz
    obtain ⟨t', ht', ht'eq⟩ := hz
    have hzseg : z ∈ segment ℝ s.1 s.2 := by
      rw [← ht'eq]
      exact (mem_segment_iff_lineMap _).mpr ⟨t', ⟨le_trans ha0 ht'.1.le, le_trans ht'.2.le hb1⟩, rfl⟩
    have ht'T : t' ∈ T := by
      refine Finset.mem_image.mpr ⟨z, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨hzV, hzseg⟩
      · rw [← ht'eq, pc_lineMap s.1 s.2 hs12 t']
    rcases lt_trichotomy t' t with h | h | h
    · exact absurd (halow t' ht'T h) (not_le.mpr ht'.1)
    · exact htT (h ▸ ht'T)
    · exact absurd (habig t' ht'T h) (not_le.mpr ht'.2)
  exact ⟨u, huV, v, hvV, huv, hxos, hosY, hosV⟩

lemma openSegment_eq_Ioo_minmax {a b : ℝ} (h : a ≠ b) :
    openSegment ℝ a b = Ioo (min a b) (max a b) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, openSegment_eq_Ioo h]
  · rw [min_eq_right h.le, max_eq_left h.le, openSegment_symm, openSegment_eq_Ioo h]

/-- Two "gaps" of the same subset `T` of `ℝ` which meet are equal. -/
lemma eq_Ioo_of_inter {α β γ δ : ℝ} {T : Set ℝ} (hα : α ∈ T) (hβ : β ∈ T) (hγ : γ ∈ T)
    (hδ : δ ∈ T)
    (hI : Disjoint (Ioo α β) T) (hJ : Disjoint (Ioo γ δ) T)
    (hne : (Ioo α β ∩ Ioo γ δ).Nonempty) : α = γ ∧ β = δ := by
  obtain ⟨t, htI, htJ⟩ := hne
  have h1 : α = γ := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact absurd hγ (Set.disjoint_left.mp hI ⟨h, lt_trans htJ.1 htI.2⟩)
    · exact absurd hα (Set.disjoint_left.mp hJ ⟨h, lt_trans htI.1 htJ.2⟩)
  have h2 : β = δ := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact absurd hβ (Set.disjoint_left.mp hJ ⟨lt_trans htJ.1 htI.2, h⟩)
    · exact absurd hδ (Set.disjoint_left.mp hI ⟨lt_trans htI.1 htJ.2, h⟩)
  exact ⟨h1, h2⟩

/-- If the open interval `(u,v)` of the construction lies in a segment of the family, so does it
in the whole. -/
lemma openSegment_subset_segment_of_mem {S : Finset (ℂ × ℂ)} {u v z : ℂ} {s : ℂ × ℂ}
    (hs : s ∈ S) (hz : z ∈ openSegment ℝ u v) (hzs : z ∈ segment ℝ s.1 s.2)
    (hse : openSegment ℝ u v ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2))
    (hd : Disjoint (openSegment ℝ u v) (vSet S : Set ℂ)) :
    openSegment ℝ u v ⊆ segment ℝ s.1 s.2 := by
  have hpre : IsPreconnected (openSegment ℝ u v) := by
    rw [openSegment_eq_image_lineMap]
    exact isPreconnected_Ioo.image _ (by fun_prop)
  haveI : PreconnectedSpace ↥(openSegment ℝ u v) := isPreconnected_iff_preconnectedSpace.mp hpre
  let t : Set ↥(openSegment ℝ u v) := Subtype.val ⁻¹' (segment ℝ s.1 s.2)
  have htop : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro w hw
    obtain ⟨r, hr, hrle⟩ := exists_ball_subset_segment hs hw
      (fun hV => (Set.disjoint_left.mp hd w.2) hV)
    refine ⟨r, hr, fun w' hw' => ?_⟩
    refine hrle (w' : ℂ) (hse w'.2) ?_
    exact (Subtype.dist_eq w' w) ▸ Metric.mem_ball.mp hw'
  have htbot : IsClosed t := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro w hw
    have hcl : IsClosed (segment ℝ s.1 s.2) := (isCompact_segment s.1 s.2).isClosed
    have hopen : IsOpen ((segment ℝ s.1 s.2)ᶜ) := hcl.isOpen_compl
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨r, hr, hrsub⟩ := hopen (w : ℂ) hw
    refine ⟨r, hr, fun w' hw' => ?_⟩
    rw [Set.mem_compl_iff]
    intro hmem
    refine hrsub ?_ hmem
    rw [Metric.mem_ball]
    exact (Subtype.dist_eq w' w).symm ▸ Metric.mem_ball.mp hw'
  have hne : (univ ∩ t).Nonempty := ⟨⟨z, hz⟩, mem_univ _, hzs⟩
  have hsub := IsPreconnected.subset_isClopen isPreconnected_univ
    (⟨htbot, htop⟩ : IsClopen t) hne
  intro y hy
  exact hsub (mem_univ ⟨y, hy⟩)

/-- Two "edges" of the construction which meet are equal. -/
lemma openSegment_eq_of_good_inter {S : Finset (ℂ × ℂ)} {u v u' v' : ℂ}
    (hu : u ∈ vSet S) (hv : v ∈ vSet S) (hu' : u' ∈ vSet S) (hv' : v' ∈ vSet S)
    (huv : u ≠ v) (hu'v' : u' ≠ v')
    (hse : openSegment ℝ u v ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2))
    (hse' : openSegment ℝ u' v' ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2))
    (hd : Disjoint (openSegment ℝ u v) (vSet S : Set ℂ))
    (hd' : Disjoint (openSegment ℝ u' v') (vSet S : Set ℂ))
    (hint : (openSegment ℝ u v ∩ openSegment ℝ u' v').Nonempty) :
    openSegment ℝ u v = openSegment ℝ u' v' := by
  obtain ⟨z, hz1, hz2⟩ := hint
  obtain ⟨s, hss⟩ := mem_iUnion.mp (hse hz1)
  obtain ⟨hs, hzs⟩ := mem_iUnion.mp hss
  have hsub : openSegment ℝ u v ⊆ segment ℝ s.1 s.2 :=
    openSegment_subset_segment_of_mem hs hz1 hzs hse hd
  have hsub' : openSegment ℝ u' v' ⊆ segment ℝ s.1 s.2 :=
    openSegment_subset_segment_of_mem hs hz2 hzs hse' hd'
  have hcl : IsClosed (segment ℝ s.1 s.2) := (isCompact_segment s.1 s.2).isClosed
  have hus : u ∈ segment ℝ s.1 s.2 :=
    closure_minimal hsub hcl ((closure_openSegment (𝕜 := ℝ) u v).symm ▸ left_mem_segment ℝ u v)
  have hvs : v ∈ segment ℝ s.1 s.2 :=
    closure_minimal hsub hcl ((closure_openSegment (𝕜 := ℝ) u v).symm ▸ right_mem_segment ℝ u v)
  have hu's : u' ∈ segment ℝ s.1 s.2 :=
    closure_minimal hsub' hcl ((closure_openSegment (𝕜 := ℝ) u' v').symm ▸ left_mem_segment ℝ u' v')
  have hv's : v' ∈ segment ℝ s.1 s.2 :=
    closure_minimal hsub' hcl ((closure_openSegment (𝕜 := ℝ) u' v').symm ▸ right_mem_segment ℝ u' v')
  have hs12 : s.1 ≠ s.2 := by
    intro h
    have hone : segment ℝ s.1 s.2 = {s.1} := by rw [h, segment_same]
    rw [hone, mem_singleton_iff] at hus hvs
    exact huv (by rw [hus, hvs])
  have hpiece : ∀ a b : ℂ, a ∈ segment ℝ s.1 s.2 → b ∈ segment ℝ s.1 s.2 →
      openSegment ℝ a b = (AffineMap.lineMap s.1 s.2) ''
        openSegment ℝ (pc s.1 s.2 a) (pc s.1 s.2 b) := by
    intro a b ha hb
    rw [image_openSegment ℝ (AffineMap.lineMap s.1 s.2) (pc s.1 s.2 a) (pc s.1 s.2 b),
      lineMap_pc_of_mem hs12 ha, lineMap_pc_of_mem hs12 hb]
  have htz : AffineMap.lineMap s.1 s.2 (pc s.1 s.2 z) = z := lineMap_pc_of_mem hs12 hzs
  have hzI : pc s.1 s.2 z ∈ openSegment ℝ (pc s.1 s.2 u) (pc s.1 s.2 v) := by
    rw [hpiece u v hus hvs] at hz1
    obtain ⟨t, ht, ht'⟩ := hz1
    have heq : t = pc s.1 s.2 z := lineMap_inj s.1 s.2 hs12 (ht'.trans htz.symm)
    rwa [heq] at ht
  have hzI' : pc s.1 s.2 z ∈ openSegment ℝ (pc s.1 s.2 u') (pc s.1 s.2 v') := by
    rw [hpiece u' v' hu's hv's] at hz2
    obtain ⟨t, ht, ht'⟩ := hz2
    have heq : t = pc s.1 s.2 z := lineMap_inj s.1 s.2 hs12 (ht'.trans htz.symm)
    rwa [heq] at ht
  let T : Set ℝ := {t : ℝ | AffineMap.lineMap s.1 s.2 t ∈ (vSet S : Set ℂ)}
  have hnoV : ∀ t ∈ openSegment ℝ (pc s.1 s.2 u) (pc s.1 s.2 v),
      AffineMap.lineMap s.1 s.2 t ∉ (vSet S : Set ℂ) := by
    intro t ht hV
    have hmem : AffineMap.lineMap s.1 s.2 t ∈ openSegment ℝ u v := by
      rw [hpiece u v hus hvs]
      exact Set.mem_image_of_mem _ ht
    exact (Set.disjoint_left.mp hd hmem) hV
  have hnoV' : ∀ t ∈ openSegment ℝ (pc s.1 s.2 u') (pc s.1 s.2 v'),
      AffineMap.lineMap s.1 s.2 t ∉ (vSet S : Set ℂ) := by
    intro t ht hV
    have hmem : AffineMap.lineMap s.1 s.2 t ∈ openSegment ℝ u' v' := by
      rw [hpiece u' v' hu's hv's]
      exact Set.mem_image_of_mem _ ht
    exact (Set.disjoint_left.mp hd' hmem) hV
  have htuT : pc s.1 s.2 u ∈ T := by
    change AffineMap.lineMap s.1 s.2 (pc s.1 s.2 u) ∈ (vSet S : Set ℂ)
    rw [lineMap_pc_of_mem hs12 hus]; exact hu
  have htvT : pc s.1 s.2 v ∈ T := by
    change AffineMap.lineMap s.1 s.2 (pc s.1 s.2 v) ∈ (vSet S : Set ℂ)
    rw [lineMap_pc_of_mem hs12 hvs]; exact hv
  have htu'T : pc s.1 s.2 u' ∈ T := by
    change AffineMap.lineMap s.1 s.2 (pc s.1 s.2 u') ∈ (vSet S : Set ℂ)
    rw [lineMap_pc_of_mem hs12 hu's]; exact hu'
  have htv'T : pc s.1 s.2 v' ∈ T := by
    change AffineMap.lineMap s.1 s.2 (pc s.1 s.2 v') ∈ (vSet S : Set ℂ)
    rw [lineMap_pc_of_mem hs12 hv's]; exact hv'
  have htuv : pc s.1 s.2 u ≠ pc s.1 s.2 v := by
    intro h
    exact huv (by rw [← lineMap_pc_of_mem hs12 hus, ← lineMap_pc_of_mem hs12 hvs, h])
  have htu'v' : pc s.1 s.2 u' ≠ pc s.1 s.2 v' := by
    intro h
    exact hu'v' (by rw [← lineMap_pc_of_mem hs12 hu's, ← lineMap_pc_of_mem hs12 hv's, h])
  have hminT : min (pc s.1 s.2 u) (pc s.1 s.2 v) ∈ T := by
    rcases le_total (pc s.1 s.2 u) (pc s.1 s.2 v) with h | h
    · rw [min_eq_left h]; exact htuT
    · rw [min_eq_right h]; exact htvT
  have hmaxT : max (pc s.1 s.2 u) (pc s.1 s.2 v) ∈ T := by
    rcases le_total (pc s.1 s.2 u) (pc s.1 s.2 v) with h | h
    · rw [max_eq_right h]; exact htvT
    · rw [max_eq_left h]; exact htuT
  have hminT' : min (pc s.1 s.2 u') (pc s.1 s.2 v') ∈ T := by
    rcases le_total (pc s.1 s.2 u') (pc s.1 s.2 v') with h | h
    · rw [min_eq_left h]; exact htu'T
    · rw [min_eq_right h]; exact htv'T
  have hmaxT' : max (pc s.1 s.2 u') (pc s.1 s.2 v') ∈ T := by
    rcases le_total (pc s.1 s.2 u') (pc s.1 s.2 v') with h | h
    · rw [max_eq_right h]; exact htv'T
    · rw [max_eq_left h]; exact htu'T
  have hdI : Disjoint (Ioo (min (pc s.1 s.2 u) (pc s.1 s.2 v))
      (max (pc s.1 s.2 u) (pc s.1 s.2 v))) T := by
    rw [Set.disjoint_left]
    intro t ht hT
    simp only [T] at hT
    have ht' : t ∈ openSegment ℝ (pc s.1 s.2 u) (pc s.1 s.2 v) := by
      rw [openSegment_eq_Ioo_minmax htuv]; exact ht
    exact hnoV t ht' hT
  have hdI' : Disjoint (Ioo (min (pc s.1 s.2 u') (pc s.1 s.2 v'))
      (max (pc s.1 s.2 u') (pc s.1 s.2 v'))) T := by
    rw [Set.disjoint_left]
    intro t ht hT
    simp only [T] at hT
    have ht' : t ∈ openSegment ℝ (pc s.1 s.2 u') (pc s.1 s.2 v') := by
      rw [openSegment_eq_Ioo_minmax htu'v']; exact ht
    exact hnoV' t ht' hT
  have hne' : (Ioo (min (pc s.1 s.2 u) (pc s.1 s.2 v)) (max (pc s.1 s.2 u) (pc s.1 s.2 v)) ∩
      Ioo (min (pc s.1 s.2 u') (pc s.1 s.2 v')) (max (pc s.1 s.2 u') (pc s.1 s.2 v'))).Nonempty := by
    refine ⟨pc s.1 s.2 z, ?_, ?_⟩
    · rw [← openSegment_eq_Ioo_minmax htuv]; exact hzI
    · rw [← openSegment_eq_Ioo_minmax htu'v']; exact hzI'
  obtain ⟨hm1, hm2⟩ := eq_Ioo_of_inter hminT hmaxT hminT' hmaxT' hdI hdI' hne'
  rw [hpiece u v hus hvs, hpiece u' v' hu's hv's, openSegment_eq_Ioo_minmax htuv,
    openSegment_eq_Ioo_minmax htu'v', hm1, hm2]

/-! ## The subdivision -/

/-- A total order (lexicographic in `(re, im)`) used to choose a canonical representative of each
unordered pair of distinct points of `ℂ`. -/
def Canon (a b : ℂ) : Prop := a.re < b.re ∨ (a.re = b.re ∧ a.im < b.im)

lemma canon_irrefl (a : ℂ) : ¬ Canon a a := by
  rintro (h | ⟨h, h'⟩) <;> linarith

lemma canon_asymm {a b : ℂ} (h1 : Canon a b) (h2 : Canon b a) : False := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · linarith

lemma canon_or (a b : ℂ) (h : a ≠ b) : Canon a b ∨ Canon b a := by
  rcases lt_trichotomy a.re b.re with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy a.im b.im with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact absurd (Complex.ext h1 h2) h
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

lemma canon_pair_eq {a b c d : ℂ} (hab : a ≠ b) (h1 : Canon a b) (h2 : Canon c d)
    (h : ({a, b} : Set ℂ) = {c, d}) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have h' : a ∈ ({c, d} : Set ℂ) := by rw [← h]; exact Or.inl rfl
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
  have hb : b = c ∨ b = d := by
    have h' : b ∈ ({c, d} : Set ℂ) := by rw [← h]; exact Or.inr rfl
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
  rcases ha with hac | had
  · rcases hb with hbc | hbd
    · exact absurd (hac.trans hbc.symm) hab
    · exact ⟨hac, hbd⟩
  · rcases hb with hbc | hbd
    · exact absurd (canon_asymm h1 (hbc.symm ▸ had.symm ▸ h2)) id
    · exact absurd (had.trans hbd.symm) hab

/-- For distinct `a, b`, the open segment determines the unordered pair of endpoints. -/
lemma openSegment_eq_iff_endpoints {a b c d : ℂ} (hab : a ≠ b) (hcd : c ≠ d) :
    openSegment ℝ a b = openSegment ℝ c d ↔ ({a, b} : Set ℂ) = {c, d} := by
  constructor
  · intro h
    have hseg : segment ℝ a b = segment ℝ c d := by
      rw [← closure_openSegment (𝕜 := ℝ) a b, ← closure_openSegment (𝕜 := ℝ) c d, h]
    have ha : a ∈ ({c, d} : Set ℂ) := by
      by_contra hc
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
      have hmem : a ∈ openSegment ℝ c d :=
        mem_openSegment_of_ne_left_right (Ne.symm hc.1) (Ne.symm hc.2)
          (hseg ▸ left_mem_segment ℝ a b)
      rw [← h] at hmem
      exact Commons.Topology.Plane.notMem_openSegment_left hab hmem
    have hb : b ∈ ({c, d} : Set ℂ) := by
      by_contra hc
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
      have hmem : b ∈ openSegment ℝ c d :=
        mem_openSegment_of_ne_left_right (Ne.symm hc.1) (Ne.symm hc.2)
          (hseg ▸ right_mem_segment ℝ a b)
      rw [← h] at hmem
      exact Commons.Topology.Plane.notMem_openSegment_right hab hmem
    have ha' : a = c ∨ a = d := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    have hb' : b = c ∨ b = d := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb
    rcases ha' with hac | had
    · rcases hb' with hbc | hbd
      · exact absurd (hac.trans hbc.symm) hab
      · rw [hac, hbd]
    · rcases hb' with hbc | hbd
      · rw [had, hbc, Set.pair_comm]
      · exact absurd (had.trans hbd.symm) hab
  · intro h
    have ha : a = c ∨ a = d := by
      have h' : a ∈ ({c, d} : Set ℂ) := by rw [← h]; exact Or.inl rfl
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
    have hb : b = c ∨ b = d := by
      have h' : b ∈ ({c, d} : Set ℂ) := by rw [← h]; exact Or.inr rfl
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
    rcases ha with hac | had
    · rcases hb with hbc | hbd
      · exact absurd (hac.trans hbc.symm) hab
      · rw [hac, hbd]
    · rcases hb with hbc | hbd
      · rw [had, hbc, openSegment_symm]
      · exact absurd (had.trans hbd.symm) hab

noncomputable def eSet (S : Finset (ℂ × ℂ)) (V : Finset ℂ) : Finset (ℂ × ℂ) :=
  (V ×ˢ V).filter (fun p =>
    p.1 ≠ p.2 ∧
    openSegment ℝ p.1 p.2 ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧
    Disjoint (openSegment ℝ p.1 p.2) (V : Set ℂ) ∧
    Canon p.1 p.2)

lemma mem_eSet {S : Finset (ℂ × ℂ)} {V : Finset ℂ} {p : ℂ × ℂ} :
    p ∈ eSet S V ↔ p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 ≠ p.2 ∧
      openSegment ℝ p.1 p.2 ⊆ (⋃ s ∈ S, segment ℝ s.1 s.2) ∧
      Disjoint (openSegment ℝ p.1 p.2) (V : Set ℂ) ∧ Canon p.1 p.2 := by
  simp only [eSet, Finset.mem_filter, Finset.mem_product]
  tauto

lemma eSet_eq_of_seg_eq {S : Finset (ℂ × ℂ)} {V : Finset ℂ} {p p' : ℂ × ℂ}
    (hp : p ∈ eSet S V) (hp' : p' ∈ eSet S V)
    (h : openSegment ℝ p.1 p.2 = openSegment ℝ p'.1 p'.2) : p = p' := by
  rw [mem_eSet] at hp hp'
  have h1 : ({p.1, p.2} : Set ℂ) = {p'.1, p'.2} :=
    (openSegment_eq_iff_endpoints hp.2.2.1 hp'.2.2.1).mp h
  have h2 := canon_pair_eq hp.2.2.1 hp.2.2.2.2.2 hp'.2.2.2.2.2 h1
  exact Prod.ext h2.1 h2.2

lemma openSegment_eq_of_mem_eSet {S : Finset (ℂ × ℂ)} {p p' : ℂ × ℂ}
    (hp : p ∈ eSet S (vSet S)) (hp' : p' ∈ eSet S (vSet S))
    (h : (openSegment ℝ p.1 p.2 ∩ openSegment ℝ p'.1 p'.2).Nonempty) :
    openSegment ℝ p.1 p.2 = openSegment ℝ p'.1 p'.2 := by
  rw [mem_eSet] at hp hp'
  exact openSegment_eq_of_good_inter hp.1 hp.2.1 hp'.1 hp'.2.1 hp.2.2.1 hp'.2.2.1
    hp.2.2.2.1 hp'.2.2.2.1 hp.2.2.2.2.1 hp'.2.2.2.2.1 h

/-- Every finite union of closed line segments in `ℂ` can be subdivided into closed line segments
meeting only in common endpoints. -/
theorem exists_subdivision_of_finset_segments_aux (S : Finset (ℂ × ℂ)) :
    ∃ (V : Finset ℂ) (E : Finset (ℂ × ℂ)),
      (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) ∧
      (∀ e ∈ E, e.1 ≠ e.2) ∧
      (∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
        segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
          ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ)) ∧
      ((V : Set ℂ) ∪ ⋃ e ∈ E, segment ℝ e.1 e.2 = ⋃ s ∈ S, segment ℝ s.1 s.2) := by
  refine ⟨vSet S, eSet S (vSet S), ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [mem_eSet] at he
    exact ⟨he.1, he.2.1⟩
  · intro e he
    rw [mem_eSet] at he
    exact he.2.2.1
  · intro e he e' he' hne
    have he_mem := he
    have he'_mem := he'
    rw [mem_eSet] at he he'
    intro z hz
    have hz1 : z ∈ ({e.1, e.2} : Set ℂ) ∨ z ∈ openSegment ℝ e.1 e.2 := by
      have h := insert_endpoints_openSegment (𝕜 := ℝ) e.1 e.2
      have h' : z ∈ segment ℝ e.1 e.2 := hz.1
      rw [← h] at h'
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] using h'
    have hz2 : z ∈ ({e'.1, e'.2} : Set ℂ) ∨ z ∈ openSegment ℝ e'.1 e'.2 := by
      have h := insert_endpoints_openSegment (𝕜 := ℝ) e'.1 e'.2
      have h' : z ∈ segment ℝ e'.1 e'.2 := hz.2
      rw [← h] at h'
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] using h'
    rcases hz1 with h1 | h1
    · rcases hz2 with h2 | h2
      · exact ⟨h1, h2⟩
      · exact absurd (h1.elim (fun hh => hh ▸ he.1) (fun hh => hh ▸ he.2.1))
          (Set.disjoint_left.mp he'.2.2.2.2.1 h2)
    · rcases hz2 with h2 | h2
      · exact absurd (h2.elim (fun hh => hh ▸ he'.1) (fun hh => hh ▸ he'.2.1))
          (Set.disjoint_left.mp he.2.2.2.2.1 h1)
      · exact absurd (eSet_eq_of_seg_eq he_mem he'_mem
          (openSegment_eq_of_mem_eSet he_mem he'_mem ⟨z, h1, h2⟩)) hne
  · apply subset_antisymm
    · intro z hz
      rcases hz with hz | hz
      · rw [Finset.mem_coe, mem_vSet] at hz
        exact hz.2
      · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
        obtain ⟨he, hz⟩ := mem_iUnion.mp hz
        rw [mem_eSet] at he
        have hseg : z = e.1 ∨ z = e.2 ∨ z ∈ openSegment ℝ e.1 e.2 := by
          have h := insert_endpoints_openSegment (𝕜 := ℝ) e.1 e.2
          rw [← h] at hz
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
        rcases hseg with hz | hz | hz
        · rw [hz]; exact (mem_vSet.mp he.1).2
        · rw [hz]; exact (mem_vSet.mp he.2.1).2
        · exact he.2.2.2.1 hz
    · intro z hz
      by_cases hzV : z ∈ vSet S
      · exact Or.inl hzV
      · obtain ⟨u, hu, v, hv, huv, hzu, hsu, hdu⟩ := exists_adjacent_vertices hz hzV
        have hcan : Canon u v ∨ Canon v u := canon_or u v huv
        rcases hcan with hcan | hcan
        · refine Or.inr (mem_iUnion.mpr ⟨(u, v), mem_iUnion.mpr ⟨?_, ?_⟩⟩)
          · rw [mem_eSet]
            exact ⟨hu, hv, huv, hsu, hdu, hcan⟩
          · exact openSegment_subset_segment ℝ u v hzu
        · refine Or.inr (mem_iUnion.mpr ⟨(v, u), mem_iUnion.mpr ⟨?_, ?_⟩⟩)
          · rw [mem_eSet]
            refine ⟨hv, hu, huv.symm, ?_, ?_, hcan⟩
            · rwa [openSegment_symm]
            · rwa [openSegment_symm]
          · exact openSegment_subset_segment ℝ v u (by rwa [openSegment_symm])




lemma exists_cwComplex_subtype_univ_aux {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}
    (hC : Topology.CWComplex C) :
    ∃ h : Topology.CWComplex (X := ↥C) Set.univ,
      ∀ n : ℕ, IsEmpty (@Topology.CWComplex.cell X _ C hC n) →
        IsEmpty (@Topology.CWComplex.cell ↥C _ Set.univ h n) := by
  classical
  letI : Topology.CWComplex C := hC
  let toF : (n : ℕ) → Topology.RelCWComplex.cell C n → (Fin n → ℝ) → ↥C :=
    fun n i t => if h : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1
      then ⟨Topology.RelCWComplex.map n i t,
        Topology.RelCWComplex.closedCell_subset_complex n i (mem_image_of_mem _ h)⟩
      else ⟨Topology.RelCWComplex.map n i 0,
        Topology.RelCWComplex.closedCell_subset_complex n i
          (mem_image_of_mem _ (Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1)))⟩
  let mp : (n : ℕ) → Topology.RelCWComplex.cell C n → PartialEquiv (Fin n → ℝ) ↥C :=
    fun n i =>
      { toFun := toF n i
        invFun := fun y => (Topology.RelCWComplex.map n i).symm y
        source := Metric.ball (0 : Fin n → ℝ) 1
        target := Subtype.val ⁻¹' (Topology.RelCWComplex.map n i).target
        map_source' := by
          intro t ht
          have hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := ball_subset_closedBall ht
          simp only [toF, dif_pos hb, mem_preimage]
          exact (Topology.RelCWComplex.map n i).map_source
            ((Topology.RelCWComplex.source_eq n i).symm ▸ ht)
        map_target' := by
          intro y hy
          rw [mem_preimage] at hy
          have hs := (Topology.RelCWComplex.map n i).map_target hy
          rw [Topology.RelCWComplex.source_eq n i] at hs
          exact hs
        left_inv' := by
          intro t ht
          have hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := ball_subset_closedBall ht
          simp only [toF, dif_pos hb]
          exact (Topology.RelCWComplex.map n i).left_inv
            ((Topology.RelCWComplex.source_eq n i).symm ▸ ht)
        right_inv' := by
          intro y hy
          rw [mem_preimage] at hy
          have hs := (Topology.RelCWComplex.map n i).map_target hy
          rw [Topology.RelCWComplex.source_eq n i] at hs
          have hb : (Topology.RelCWComplex.map n i).symm y ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
            ball_subset_closedBall hs
          simp only [toF, dif_pos hb]
          exact Subtype.ext ((Topology.RelCWComplex.map n i).right_inv hy) }
  have mp_apply : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n) (t : Fin n → ℝ),
      (mp n i) t = toF n i t := fun n i t => rfl
  have htoF_eq : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n) (t : Fin n → ℝ)
      (hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1),
      toF n i t = ⟨Topology.RelCWComplex.map n i t,
        Topology.RelCWComplex.closedCell_subset_complex n i (mem_image_of_mem _ hb)⟩ := by
    intro n i t hb
    simp only [toF, dif_pos hb]
  have hball : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      mp n i '' Metric.ball (0 : Fin n → ℝ) 1 =
        Subtype.val ⁻¹' (Topology.RelCWComplex.openCell n i) := by
    intro n i
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mp_apply, htoF_eq n i t (ball_subset_closedBall ht)]
      exact mem_image_of_mem _ ht
    · intro hy
      rw [mem_preimage] at hy
      obtain ⟨t, ht, ht'⟩ := hy
      exact ⟨t, ht, by rw [mp_apply, htoF_eq n i t (ball_subset_closedBall ht)]; exact Subtype.ext ht'⟩
  have hclosed : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      mp n i '' Metric.closedBall (0 : Fin n → ℝ) 1 =
        Subtype.val ⁻¹' (Topology.RelCWComplex.closedCell n i) := by
    intro n i
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mp_apply, htoF_eq n i t ht]
      exact mem_image_of_mem _ ht
    · intro hy
      rw [mem_preimage] at hy
      obtain ⟨t, ht, ht'⟩ := hy
      exact ⟨t, ht, by rw [mp_apply, htoF_eq n i t ht]; exact Subtype.ext ht'⟩
  have hsphere : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      mp n i '' Metric.sphere (0 : Fin n → ℝ) 1 =
        Subtype.val ⁻¹' (Topology.RelCWComplex.cellFrontier n i) := by
    intro n i
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
        simp only [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at ht
        linarith
      rw [mp_apply, htoF_eq n i t hb]
      exact ⟨t, ht, rfl⟩
    · intro hy
      rw [mem_preimage] at hy
      obtain ⟨t, ht, ht'⟩ := hy
      have hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
        simp only [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at ht
        linarith
      exact ⟨t, ht, by rw [mp_apply, htoF_eq n i t hb]; exact Subtype.ext ht'⟩
  let hY : Topology.CWComplex (X := ↥C) Set.univ :=
    { cell := fun n => Topology.RelCWComplex.cell C n
      map := mp
      source_eq := fun n i => rfl
      continuousOn := by
        intro n i
        rw [Topology.IsInducing.continuousOn_iff Topology.IsInducing.subtypeVal]
        exact (Topology.RelCWComplex.continuousOn n i).congr (fun t ht => by
          simp only [Function.comp_apply, mp, toF, dif_pos ht])
      continuousOn_symm := by
        intro n i
        have h : ContinuousOn (fun y : ↥C => (y : X)) (mp n i).target :=
          continuous_subtype_val.continuousOn
        exact (Topology.RelCWComplex.continuousOn_symm n i).comp h (fun y hy => hy)
      pairwiseDisjoint' := by
        intro a _ b _ hab
        show Disjoint ((mp a.1 a.2) '' Metric.ball (0 : Fin a.1 → ℝ) 1)
          ((mp b.1 b.2) '' Metric.ball (0 : Fin b.1 → ℝ) 1)
        rw [hball a.1 a.2, hball b.1 b.2]
        refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
        rw [mem_preimage] at hy1 hy2
        exact (Set.disjoint_left.mp
          (Topology.RelCWComplex.disjoint_openCell_of_ne (C := C) hab) hy1) hy2
      mapsTo' := by
        intro n i
        obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo (C := C) n i
        refine ⟨I, fun t ht => ?_⟩
        have hb : t ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
          simp only [Metric.mem_closedBall]
          rw [Metric.mem_sphere] at ht
          linarith
        have h1 := hI ht
        rw [mem_iUnion] at h1
        obtain ⟨m, h1⟩ := h1
        rw [mem_iUnion] at h1
        obtain ⟨hmn, h1⟩ := h1
        rw [mem_iUnion] at h1
        obtain ⟨j, h1⟩ := h1
        rw [mem_iUnion] at h1
        obtain ⟨hj, h1⟩ := h1
        obtain ⟨t', ht', ht''⟩ := h1
        refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn,
          mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, ?_⟩⟩⟩⟩
        refine ⟨t', ht', ?_⟩
        have hb' : t' ∈ Metric.closedBall (0 : Fin m → ℝ) 1 := ht'
        rw [mp_apply, mp_apply, htoF_eq n i t hb, htoF_eq m j t' hb']
        exact Subtype.ext ht''
      closed' := by
        intro A _ hcl
        have hA' : Subtype.val '' A ⊆ C := fun x ⟨a, _, ha⟩ => ha ▸ a.2
        have hcl' : ∀ (n : ℕ) (j : Topology.RelCWComplex.cell C n),
            IsClosed ((Subtype.val '' A) ∩ Topology.RelCWComplex.closedCell n j) := by
          intro n j
          have h1 := hcl n j
          have heq : (Subtype.val '' A) ∩ Topology.RelCWComplex.closedCell n j =
              Subtype.val '' (A ∩ (mp n j '' Metric.closedBall (0 : Fin n → ℝ) 1)) := by
            rw [hclosed n j]
            ext x
            constructor
            · rintro ⟨⟨a, ha, rfl⟩, hx⟩
              exact ⟨a, ⟨ha, hx⟩, rfl⟩
            · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
              exact ⟨⟨a, ha, rfl⟩, hx⟩
          rw [heq]
          rw [isClosed_induced_iff] at h1
          obtain ⟨t, ht, ht'⟩ := h1
          have h2 : Subtype.val '' (A ∩ (mp n j '' Metric.closedBall (0 : Fin n → ℝ) 1)) =
              C ∩ t := by
            rw [← ht', Subtype.image_preimage_coe]
          rw [h2]
          exact (Topology.RelCWComplex.isClosed (C := C)).inter ht
        have h2 : IsClosed (Subtype.val '' A) :=
          (Topology.CWComplex.closed C (Subtype.val '' A) hA').mpr hcl'
        have h3 : A = Subtype.val ⁻¹' (Subtype.val '' A) :=
          (Set.preimage_image_eq A Subtype.val_injective).symm
        rw [h3]
        exact h2.preimage continuous_subtype_val
      union' := by
        apply eq_univ_of_forall
        intro y
        have hy' : (y : X) ∈ ⋃ (n : ℕ) (j : Topology.RelCWComplex.cell C n),
            Topology.RelCWComplex.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 :=
          (Topology.CWComplex.union (C := C)).ge y.2
        obtain ⟨n, hy'⟩ := mem_iUnion.mp hy'
        obtain ⟨j, hy'⟩ := mem_iUnion.mp hy'
        exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨j, by rw [hclosed n j]; exact hy'⟩⟩ }
  refine ⟨hY, ?_⟩
  intro n hn
  exact hn


theorem finiteUnionSegments_oneDimCWComplex (S : Finset (ℂ × ℂ)) :
    ∃ (hY : @Topology.CWComplex ↥(⋃ s ∈ S, segment ℝ s.1 s.2) _ Set.univ),
      (∀ n : ℕ, 2 ≤ n →
        IsEmpty (@Topology.CWComplex.cell ↥(⋃ s ∈ S, segment ℝ s.1 s.2) _ Set.univ hY n)) := by
  classical
  obtain ⟨V, E, hV, hne, hdisj, hcov⟩ := exists_subdivision_of_finset_segments_aux S
  obtain ⟨hC, hcell⟩ := Commons.Topology.Plane.exists_cwComplex_of_finset_segments V E hV hne hdisj
  obtain ⟨h, hcells⟩ := exists_cwComplex_subtype_univ_aux
    (C := ((V : Set ℂ) ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) : Set ℂ)) hC
  have key : ∃ (hY : @Topology.CWComplex
        ↥((V : Set ℂ) ∪ (⋃ e ∈ E, segment ℝ e.1 e.2)) _ Set.univ),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell
        ↥((V : Set ℂ) ∪ (⋃ e ∈ E, segment ℝ e.1 e.2)) _ Set.univ hY n)) :=
    ⟨h, fun n hn => hcells n (hcell n hn)⟩
  exact hcov ▸ key

end Commons.Topology.CWComplex