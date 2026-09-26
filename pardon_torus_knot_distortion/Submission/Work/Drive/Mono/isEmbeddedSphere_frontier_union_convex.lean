import Mathlib
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.EpsW.isEmbeddedSphere_levelSet_of_convex

/-!
# The frontier of the union of two intersecting convex bodies of `ℝ³`

If `A` and `B` are open, convex, bounded subsets of `ℝ³` with `A ∩ B ≠ ∅`, then
`frontier (A ∪ B)` is an embedded `2`-sphere.

The witness is the radial parametrisation from a point `x ∈ A ∩ B`: along every ray issuing
from `x`, the set `A ∪ B` is an interval `[0, r)` (both `A` and `B` are convex and contain `x`),
so the ray meets the frontier in exactly one point, and the direction map is a homeomorphism
of `frontier (A ∪ B)` onto the unit sphere.  The radial function is computed with the
Minkowski gauge of the translates `A - x` and `B - x`: for a unit vector `v` and `t ≥ 0`,

* `x + t • v ∈ A ↔ t < (gauge (A - x) v)⁻¹`,
* `x + t • v ∈ closure A ↔ t ≤ (gauge (A - x) v)⁻¹`,

by `gauge_smul_of_nonneg` together with `gauge_lt_one_iff_mem_interior` and
`gauge_le_one_iff_mem_closure`.  The exit parameter of the ray is therefore
`max ((gauge (A - x) v)⁻¹) ((gauge (B - x) v)⁻¹)`, which is continuous on the unit sphere
because the gauge is continuous and does not vanish there.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal Topology Pointwise

noncomputable section

/-- For a convex open set `s ∋ 0` and `t ≥ 0`, the point `t • v` lies in `s` exactly when
`t` is smaller than the reciprocal of the gauge of `v`: the gauge of the point on the ray is
`t * gauge s v`. -/
theorem smul_mem_iff_lt_inv_gauge {s : Set R3} (hc : Convex ℝ s) (hs : s ∈ 𝓝 0)
    (hopen : IsOpen s) {v : R3} {t : ℝ} (ht : 0 ≤ t) (hg : 0 < gauge s v) :
    t • v ∈ s ↔ t < (gauge s v)⁻¹ := by
  have key := gauge_lt_one_iff_mem_interior (s := s) hc hs (x := t • v)
  rw [hopen.interior_eq] at key
  rw [gauge_smul_of_nonneg ht, smul_eq_mul] at key
  rw [← key, ← one_div]
  exact (lt_div_iff₀ hg).symm

/-- For a convex open set `s ∋ 0` and `t ≥ 0`, the point `t • v` lies in the closure of `s`
exactly when `t` is at most the reciprocal of the gauge of `v`. -/
theorem smul_mem_closure_iff_le_inv_gauge {s : Set R3} (hc : Convex ℝ s) (hs : s ∈ 𝓝 0)
    {v : R3} {t : ℝ} (ht : 0 ≤ t) (hg : 0 < gauge s v) :
    t • v ∈ closure s ↔ t ≤ (gauge s v)⁻¹ := by
  have key := gauge_le_one_iff_mem_closure (s := s) hc hs (x := t • v)
  rw [gauge_smul_of_nonneg ht, smul_eq_mul] at key
  rw [← key, ← one_div]
  exact (le_div_iff₀ hg).symm

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem isEmbeddedSphere_frontier_union_convex {A B : Set R3}
    (hAo : IsOpen A) (hBo : IsOpen B) (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B)
    (hne : (A ∩ B).Nonempty) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier (A ∪ B)) := by
  obtain ⟨x, hxA, hxB⟩ := hne
  -- the translates of `A` and `B` centred at the origin
  set sA : Set R3 := (-x) +ᵥ A with hsA
  set sB : Set R3 := (-x) +ᵥ B with hsB
  have hmemA : ∀ y : R3, y ∈ sA ↔ x + y ∈ A := by
    intro y
    rw [hsA, Set.mem_vadd_set]
    constructor
    · rintro ⟨a, ha, hax⟩
      rw [← hax, vadd_eq_add]
      simpa [add_assoc] using ha
    · intro hy
      exact ⟨x + y, hy, by simp [vadd_eq_add]⟩
  have hmemB : ∀ y : R3, y ∈ sB ↔ x + y ∈ B := by
    intro y
    rw [hsB, Set.mem_vadd_set]
    constructor
    · rintro ⟨a, ha, hax⟩
      rw [← hax, vadd_eq_add]
      simpa [add_assoc] using ha
    · intro hy
      exact ⟨x + y, hy, by simp [vadd_eq_add]⟩
  have hconvA : Convex ℝ sA := by rw [hsA]; exact hAc.vadd (-x)
  have hconvB : Convex ℝ sB := by rw [hsB]; exact hBc.vadd (-x)
  have hopenA : IsOpen sA := by rw [hsA]; exact hAo.vadd (-x)
  have hopenB : IsOpen sB := by rw [hsB]; exact hBo.vadd (-x)
  have h0A : (0 : R3) ∈ sA := by rw [hmemA 0]; simpa using hxA
  have h0B : (0 : R3) ∈ sB := by rw [hmemB 0]; simpa using hxB
  have hnhdsA : sA ∈ 𝓝 0 := hopenA.mem_nhds h0A
  have hnhdsB : sB ∈ 𝓝 0 := hopenB.mem_nhds h0B
  have hvNA : Bornology.IsVonNBounded ℝ sA :=
    NormedSpace.isVonNBounded_of_isBounded ℝ (by rw [hsA]; exact hAb.vadd (-x))
  have hvNB : Bornology.IsVonNBounded ℝ sB :=
    NormedSpace.isVonNBounded_of_isBounded ℝ (by rw [hsB]; exact hBb.vadd (-x))
  have hclA : ∀ (t : ℝ) (y : R3), t • y ∈ closure sA ↔ x + t • y ∈ closure A := by
    intro t y
    rw [hsA, closure_vadd, Set.mem_vadd_set]
    constructor
    · rintro ⟨a, ha, hax⟩
      rw [← hax, vadd_eq_add]
      simpa [add_assoc] using ha
    · intro hy
      exact ⟨x + t • y, hy, by simp [vadd_eq_add]⟩
  have hclB : ∀ (t : ℝ) (y : R3), t • y ∈ closure sB ↔ x + t • y ∈ closure B := by
    intro t y
    rw [hsB, closure_vadd, Set.mem_vadd_set]
    constructor
    · rintro ⟨a, ha, hax⟩
      rw [← hax, vadd_eq_add]
      simpa [add_assoc] using ha
    · intro hy
      exact ⟨x + t • y, hy, by simp [vadd_eq_add]⟩
  have hposA : ∀ y : R3, ‖y‖ = 1 → 0 < gauge sA y := by
    intro y hy
    have hyne : y ≠ 0 := by
      intro h
      rw [h] at hy
      simp at hy
    exact (gauge_pos (absorbent_nhds_zero hnhdsA) hvNA).2 hyne
  have hposB : ∀ y : R3, ‖y‖ = 1 → 0 < gauge sB y := by
    intro y hy
    have hyne : y ≠ 0 := by
      intro h
      rw [h] at hy
      simp at hy
    exact (gauge_pos (absorbent_nhds_zero hnhdsB) hvNB).2 hyne
  have hsmulA : ∀ (t : ℝ) (y : R3), 0 ≤ t → 0 < gauge sA y →
      (x + t • y ∈ A ↔ t < (gauge sA y)⁻¹) := by
    intro t y ht hg
    rw [← hmemA (t • y)]
    exact smul_mem_iff_lt_inv_gauge hconvA hnhdsA hopenA ht hg
  have hsmulB : ∀ (t : ℝ) (y : R3), 0 ≤ t → 0 < gauge sB y →
      (x + t • y ∈ B ↔ t < (gauge sB y)⁻¹) := by
    intro t y ht hg
    rw [← hmemB (t • y)]
    exact smul_mem_iff_lt_inv_gauge hconvB hnhdsB hopenB ht hg
  have hsmulAcl : ∀ (t : ℝ) (y : R3), 0 ≤ t → 0 < gauge sA y →
      (x + t • y ∈ closure A ↔ t ≤ (gauge sA y)⁻¹) := by
    intro t y ht hg
    rw [← hclA t y]
    exact smul_mem_closure_iff_le_inv_gauge hconvA hnhdsA ht hg
  have hsmulBcl : ∀ (t : ℝ) (y : R3), 0 ≤ t → 0 < gauge sB y →
      (x + t • y ∈ closure B ↔ t ≤ (gauge sB y)⁻¹) := by
    intro t y ht hg
    rw [← hclB t y]
    exact smul_mem_closure_iff_le_inv_gauge hconvB hnhdsB ht hg
  have hw_norm : ∀ w : Metric.sphere (0 : R3) 1, ‖(w : R3)‖ = 1 := by
    intro w
    have h := w.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h
  -- continuity of the two radial functions on the unit sphere
  have hcontA : Continuous fun w : Metric.sphere (0 : R3) 1 => (gauge sA (w : R3))⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro w
    exact (((continuous_gauge hconvA hnhdsA).comp continuous_subtype_val).continuousAt).inv₀
      (ne_of_gt (hposA (w : R3) (hw_norm w)))
  have hcontB : Continuous fun w : Metric.sphere (0 : R3) 1 => (gauge sB (w : R3))⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro w
    exact (((continuous_gauge hconvB hnhdsB).comp continuous_subtype_val).continuousAt).inv₀
      (ne_of_gt (hposB (w : R3) (hw_norm w)))
  have hcont : Continuous fun w : Metric.sphere (0 : R3) 1 =>
      x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3) :=
    continuous_const.add ((hcontA.max hcontB).smul continuous_subtype_val)
  let e : C(Metric.sphere (0 : R3) 1, R3) :=
    { toFun := fun w =>
        x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3)
      continuous_toFun := hcont }
  have he_apply : ∀ w : Metric.sphere (0 : R3) 1,
      e w = x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3) :=
    fun w => rfl
  refine ⟨e, ?_, ?_⟩
  · -- injectivity: the point of the sphere is recovered as the unit direction of `e w - x`
    intro u v huv
    have hkey : ∀ w : Metric.sphere (0 : R3) 1, (w : R3) = ‖e w - x‖⁻¹ • (e w - x) := by
      intro w
      have hrpos : 0 < max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) :=
        lt_max_of_lt_left (inv_pos.mpr (hposA (w : R3) (hw_norm w)))
      have hvec : e w - x
          = max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3) := by
        rw [he_apply, add_sub_cancel_left]
      have hnorm : ‖e w - x‖ = max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) := by
        rw [hvec, norm_smul, Real.norm_of_nonneg hrpos.le, hw_norm w, mul_one]
      rw [hnorm, hvec, smul_smul, inv_mul_cancel₀ (ne_of_gt hrpos), one_smul]
    exact Subtype.ext (by rw [hkey u, hkey v, huv])
  · -- the range is exactly the frontier
    ext p
    constructor
    · rintro ⟨w, rfl⟩
      rw [he_apply]
      have hw := hw_norm w
      have hgA := hposA (w : R3) hw
      have hgB := hposB (w : R3) hw
      have htw : 0 ≤ max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) :=
        le_trans (inv_pos.mpr hgA).le (le_max_left _ _)
      have htwB : 0 ≤ max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) :=
        le_trans (inv_pos.mpr hgB).le (le_max_right _ _)
      have hnotA : x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3) ∉ A :=
        fun h => absurd ((hsmulA _ _ htw hgA).1 h) (not_lt.mpr (le_max_left _ _))
      have hnotB : x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3) ∉ B :=
        fun h => absurd ((hsmulB _ _ htwB hgB).1 h) (not_lt.mpr (le_max_right _ _))
      have hcl : x + max ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) • (w : R3)
          ∈ closure (A ∪ B) := by
        rw [closure_union]
        rcases le_total ((gauge sA (w : R3))⁻¹) ((gauge sB (w : R3))⁻¹) with hle | hle
        · right
          exact (hsmulBcl _ _ htwB hgB).2 (le_of_eq (max_eq_right hle))
        · left
          exact (hsmulAcl _ _ htw hgA).2 (le_of_eq (max_eq_left hle))
      rw [frontier, (hAo.union hBo).interior_eq]
      exact ⟨hcl, fun h => h.elim hnotA hnotB⟩
    · -- every point of the frontier is an exit point of some ray
      intro hp
      rw [frontier, (hAo.union hBo).interior_eq] at hp
      obtain ⟨hpcl, hpnot⟩ := hp
      rw [closure_union] at hpcl
      have hpx : p ≠ x := by
        intro h
        exact hpnot (by rw [h]; exact Or.inl hxA)
      set v : R3 := ‖p - x‖⁻¹ • (p - x) with hv
      have htnorm : ‖p - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpx)
      have hvnorm : ‖v‖ = 1 := by
        rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ htnorm]
      have hpv : p = x + ‖p - x‖ • v := by
        rw [hv, smul_smul, mul_inv_cancel₀ htnorm, one_smul]
        abel
      have hgvA : 0 < gauge sA v := hposA v hvnorm
      have hgvB : 0 < gauge sB v := hposB v hvnorm
      have ht0 : 0 ≤ ‖p - x‖ := norm_nonneg _
      have hnotA : x + ‖p - x‖ • v ∉ A := by
        rw [← hpv]; intro h; exact hpnot (Or.inl h)
      have hnotB : x + ‖p - x‖ • v ∉ B := by
        rw [← hpv]; intro h; exact hpnot (Or.inr h)
      have hgeA : (gauge sA v)⁻¹ ≤ ‖p - x‖ :=
        le_of_not_gt fun hlt => hnotA ((hsmulA _ _ ht0 hgvA).2 hlt)
      have hgeB : (gauge sB v)⁻¹ ≤ ‖p - x‖ :=
        le_of_not_gt fun hlt => hnotB ((hsmulB _ _ ht0 hgvB).2 hlt)
      have hle : ‖p - x‖ ≤ max ((gauge sA v)⁻¹) ((gauge sB v)⁻¹) := by
        rcases hpcl with h | h
        · have h' : x + ‖p - x‖ • v ∈ closure A := by rw [← hpv]; exact h
          exact le_trans ((hsmulAcl _ _ ht0 hgvA).1 h') (le_max_left _ _)
        · have h' : x + ‖p - x‖ • v ∈ closure B := by rw [← hpv]; exact h
          exact le_trans ((hsmulBcl _ _ ht0 hgvB).1 h') (le_max_right _ _)
      have heq : max ((gauge sA v)⁻¹) ((gauge sB v)⁻¹) = ‖p - x‖ :=
        le_antisymm (max_le hgeA hgeB) hle
      refine ⟨⟨v, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right]; exact hvnorm
      · rw [he_apply, heq, ← hpv]

end

end Work.Drive.Mono
