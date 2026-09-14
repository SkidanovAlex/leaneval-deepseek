import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.CompletePartialOrder

namespace Commons.MeasureTheory.Integral

open Filter Set
open scoped Topology

/-- An affine self-map `t ↦ c * t + d` of `ℝ` (with `c ≠ 0`) sends `uIcc ((a-d)/c) ((b-d)/c)` into
`uIcc a b`. -/
lemma mem_uIcc_comp_affine {a b c d x : ℝ} (hc : c ≠ 0)
    (hx : x ∈ uIcc ((a - d) / c) ((b - d) / c)) : c * x + d ∈ uIcc a b := by
  have h1 : c * ((a - d) / c) + d = a := by rw [mul_div_cancel₀ _ hc]; ring
  have h2 : c * ((b - d) / c) + d = b := by rw [mul_div_cancel₀ _ hc]; ring
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hanti : Antitone (fun t : ℝ => c * t + d) := by
      intro p q hpq
      have : c * q ≤ c * p := mul_le_mul_of_nonpos_left hpq hcneg.le
      linarith
    have hmaps := hanti.mapsTo_uIcc (a := (a - d) / c) (b := (b - d) / c)
    rw [h1, h2] at hmaps
    exact hmaps hx
  · have hmono : Monotone (fun t : ℝ => c * t + d) := by
      intro p q hpq
      have : c * p ≤ c * q := mul_le_mul_of_nonneg_left hpq hcpos.le
      linarith
    have hmaps := hmono.mapsTo_uIcc (a := (a - d) / c) (b := (b - d) / c)
    rw [h1, h2] at hmaps
    exact hmaps hx

lemma disjoint_Ico_of_disjoint_Ioc {m M m' M' : ℝ}
    (h : Disjoint (Ioc m M) (Ioc m' M')) : Disjoint (Ico m M) (Ico m' M') := by
  rw [Set.disjoint_left] at h ⊢
  intro s hs hs'
  rw [Set.mem_Ico] at hs hs'
  rcases le_total M M' with hMM | hMM
  · exact h ⟨lt_of_le_of_lt hs.1 hs.2, le_refl M⟩
      ⟨lt_of_le_of_lt hs'.1 hs.2, hMM⟩
  · exact h ⟨lt_of_le_of_lt hs.1 hs'.2, hMM⟩
      ⟨lt_of_le_of_lt hs'.1 hs'.2, le_refl M'⟩

lemma uIoc_affine_eq_image_of_pos {x y c d : ℝ} (hc : 0 < c) :
    uIoc (c * x + d) (c * y + d) = (fun t => c * t + d) '' uIoc x y := by
  have hmono : Monotone (fun t : ℝ => c * t + d) := fun p q hpq => by nlinarith
  have hmin : min (c * x + d) (c * y + d) = c * min x y + d := by
    have := hmono.map_min (a := x) (b := y); simpa using this.symm
  have hmax : max (c * x + d) (c * y + d) = c * max x y + d := by
    have := hmono.map_max (a := x) (b := y); simpa using this.symm
  rw [uIoc, uIoc, hmin, hmax]
  ext t
  simp only [Set.mem_Ioc, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(t - d) / c,
      ⟨by rw [lt_div_iff₀ hc]; nlinarith, by rw [div_le_iff₀ hc]; nlinarith⟩,
      by rw [mul_div_cancel₀ _ hc.ne']; ring⟩
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    exact ⟨by nlinarith [mul_lt_mul_of_pos_left h1 hc],
      by nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]⟩

lemma uIoc_affine_eq_image_of_neg {x y c d : ℝ} (hc : c < 0) :
    uIoc (c * x + d) (c * y + d) = (fun t => c * t + d) '' (Ico (min x y) (max x y)) := by
  have hanti : Antitone (fun t : ℝ => c * t + d) := fun p q hpq => by nlinarith
  have hmin : min (c * x + d) (c * y + d) = c * max x y + d := by
    have := hanti.map_max (a := x) (b := y); simpa using this.symm
  have hmax : max (c * x + d) (c * y + d) = c * min x y + d := by
    have := hanti.map_min (a := x) (b := y); simpa using this.symm
  rw [uIoc, hmin, hmax]
  ext t
  simp only [Set.mem_Ioc, Set.mem_Ico, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(t - d) / c,
      ⟨by rw [le_div_iff_of_neg hc]; nlinarith, by rw [div_lt_iff_of_neg hc]; nlinarith⟩,
      by rw [mul_div_cancel₀ _ hc.ne]; ring⟩
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    exact ⟨by nlinarith [mul_lt_mul_of_neg_left h2 hc],
      by nlinarith [mul_le_mul_of_nonpos_left h1 hc.le]⟩

lemma injective_affine {c d : ℝ} (hc : c ≠ 0) : Function.Injective (fun t : ℝ => c * t + d) := by
  intro p q hpq
  exact mul_left_cancel₀ hc (by linarith)

lemma disjoint_uIoc_affine_of_pos {x y x' y' c d : ℝ} (hc : 0 < c)
    (h : Disjoint (uIoc x y) (uIoc x' y')) :
    Disjoint (uIoc (c * x + d) (c * y + d)) (uIoc (c * x' + d) (c * y' + d)) := by
  rw [uIoc_affine_eq_image_of_pos hc, uIoc_affine_eq_image_of_pos hc]
  exact Set.disjoint_image_of_injective (injective_affine hc.ne') h

lemma disjoint_uIoc_affine_of_neg {x y x' y' c d : ℝ} (hc : c < 0)
    (h : Disjoint (uIoc x y) (uIoc x' y')) :
    Disjoint (uIoc (c * x + d) (c * y + d)) (uIoc (c * x' + d) (c * y' + d)) := by
  have hdisj' : Disjoint (Ioc (min x y) (max x y)) (Ioc (min x' y') (max x' y')) := h
  rw [uIoc_affine_eq_image_of_neg hc, uIoc_affine_eq_image_of_neg hc]
  exact Set.disjoint_image_of_injective (injective_affine hc.ne)
    (disjoint_Ico_of_disjoint_Ioc hdisj')

lemma pairwiseDisjoint_uIoc_affine {ι : Type*} {s : Set ι} {I : ι → ℝ × ℝ} {c d : ℝ}
    (hc : c ≠ 0)
    (h : s.PairwiseDisjoint (fun i => uIoc (I i).1 (I i).2)) :
    s.PairwiseDisjoint (fun i => uIoc (c * (I i).1 + d) (c * (I i).2 + d)) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact disjoint_uIoc_affine_of_neg hcneg (h hi hj hij)
  · exact disjoint_uIoc_affine_of_pos hcpos (h hi hj hij)

theorem absolutelyContinuousOnInterval_comp_affine {F : Type*} [NormedAddCommGroup F]
    {f : ℝ → F} {a b c d : ℝ} (hc : c ≠ 0)
    (h : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => f (c * t + d)) ((a - d) / c) ((b - d) / c) := by
  rw [absolutelyContinuousOnInterval_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := h ε hε
  refine ⟨δ / |c|, div_pos hδ (abs_pos.mpr hc), ?_⟩
  intro E hE hlen
  rw [AbsolutelyContinuousOnInterval.disjWithin] at hE
  have hdist : ∀ i, dist (c * (E.2 i).1 + d) (c * (E.2 i).2 + d)
      = |c| * dist (E.2 i).1 (E.2 i).2 := by
    intro i
    rw [dist_add_right]
    change dist (c • (E.2 i).1) (c • (E.2 i).2) = _
    rw [dist_smul₀, Real.norm_eq_abs]
  have hsum : ∑ i ∈ Finset.range E.1, dist (c * (E.2 i).1 + d) (c * (E.2 i).2 + d)
      = |c| * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hdist i)
  have hlen' : ∑ i ∈ Finset.range E.1, dist (c * (E.2 i).1 + d) (c * (E.2 i).2 + d) < δ := by
    have := (lt_div_iff₀ (abs_pos.mpr hc)).mp hlen
    rw [hsum]
    linarith
  have hE'mem : (E.1, fun i => (c * (E.2 i).1 + d, c * (E.2 i).2 + d)) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    rw [AbsolutelyContinuousOnInterval.disjWithin]
    constructor
    · intro i hi
      exact ⟨mem_uIcc_comp_affine hc (hE.1 i hi).1, mem_uIcc_comp_affine hc (hE.1 i hi).2⟩
    · show Set.PairwiseDisjoint (↑(Finset.range E.1))
        (fun i => uIoc (c * (E.2 i).1 + d) (c * (E.2 i).2 + d))
      exact pairwiseDisjoint_uIoc_affine hc hE.2
  have := hδprop (E.1, fun i => (c * (E.2 i).1 + d, c * (E.2 i).2 + d)) hE'mem hlen'
  simpa using this

end Commons.MeasureTheory.Integral