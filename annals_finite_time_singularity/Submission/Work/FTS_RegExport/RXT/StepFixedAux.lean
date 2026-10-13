import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary real-analysis lemmas for the corrected integrated cone step (`step_integrated_nonneg`)

Helpers used by `Submission/Work/FTS_RegExport/RXT/step_integrated_fix.lean`:

* uniform continuity, uniform in the index, of a finite family on a compact set, and of the
  sum `p ↦ ∑ k, |f k p|` (`rxtStep_exists_uniform_family`, `rxtStep_exists_uniform_sum`),
  with `rxtStep_exists_delta_fin` supplying the finite minimum of the moduli;
* the two-point mean value theorem in slope form valid also at `x = y`
  (`rxtStep_exists_slope_point`);
* elementary order lemmas (`rxtStep_abs_min_max_le`, `rxtStep_le_succ_mul`,
  `rxtStep_abs_le_succ_mul`, `rxtStep_abs_sub_le_abs_of_mem_Icc`,
  `rxtStep_abs_le_max_of_mem_Icc`, `rxtStep_dist_three_le`, `rxtStep_abs_add4_le`);
* `rxtStep_correction_le`: replacing a frozen value of `F` by its value at a point inside an
  interval integral.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary helpers -/

/-- If `a ≤ x ≤ b` then `|x| ≤ max |a| |b|`. -/
lemma rxtStep_abs_le_max_of_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    |x| ≤ max |a| |b| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le a) hx.1)
  · exact le_trans hx.2 (le_trans (le_abs_self b) (le_max_right _ _))

/-- If `x, y ∈ [a,b]` then `|x - y| ≤ |b - a|`. -/
lemma rxtStep_abs_sub_le_abs_of_mem_Icc {x y a b : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : |x - y| ≤ |b - a| := by
  have hab : a ≤ b := le_trans hy.1 hy.2
  have h : |b - a| = b - a := abs_of_nonneg (by linarith)
  rw [h, abs_sub_le_iff]
  exact ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩

/-- `h ≤ (A+1) * h` for `A, h ≥ 0`. -/
lemma rxtStep_le_succ_mul {A h : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h) : h ≤ (A + 1) * h := by
  have h1 : (0:ℝ) ≤ A * h := mul_nonneg hA hh
  have h2 : (A + 1) * h = A * h + h := by ring
  linarith [h1, h2.le]

/-- `|x| ≤ A * h ≤ (A+1) * h` for `A, h ≥ 0`. -/
lemma rxtStep_abs_le_succ_mul {x A h : ℝ} (hx : |x| ≤ A * h) (hA : 0 ≤ A) (hh : 0 ≤ h) :
    |x| ≤ (A + 1) * h := by
  have h2 : (A + 1) * h = A * h + h := by ring
  linarith [hx, hh, h2.le]

/-- `x ∈ [min a b, max a b]` with `|a| ≤ C` and `|b| ≤ C` gives `|x| ≤ C`. -/
lemma rxtStep_abs_min_max_le {x a b C : ℝ} (hx : x ∈ Set.Icc (min a b) (max a b))
    (ha : |a| ≤ C) (hb : |b| ≤ C) : |x| ≤ C := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hmin : min a b ≤ x := hx.1
    have h1 : -C ≤ min a b :=
      le_min (by linarith [neg_abs_le a, ha]) (by linarith [neg_abs_le b, hb])
    linarith
  · have hmax : x ≤ max a b := hx.2
    have h2 : max a b ≤ C :=
      max_le (by linarith [le_abs_self a, ha]) (by linarith [le_abs_self b, hb])
    linarith

/-- The sup-distance of two triples, dominated componentwise. -/
lemma rxtStep_dist_three_le {a b c a' b' c' θ : ℝ} (hab : |a - a'| ≤ θ) (hbc : |b - b'| ≤ θ)
    (hcc : |c - c'| ≤ θ) : dist (a, (b, c)) (a', (b', c')) ≤ θ := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le hab (max_le hbc hcc)

/-- The two-point mean value theorem in slope form, valid also at `x = y`. -/
lemma rxtStep_exists_slope_point {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (x y : ℝ) :
    ∃ c ∈ Set.Icc (min x y) (max x y), g y - g x = (y - x) * g' c := by
  have hcont : ∀ u v : ℝ, ContinuousOn g (Set.Icc u v) := fun u v =>
    (continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt).continuousOn
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' h (hcont x y) (fun z _ => hg z)
    refine ⟨c, ?_, ?_⟩
    · rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨hc.1.le, hc.2.le⟩
    · rw [hceq]; field_simp
  · subst h
    exact ⟨x, by simp, by simp⟩
  · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' h (hcont y x) (fun z _ => hg z)
    refine ⟨c, ?_, ?_⟩
    · rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨hc.1.le, hc.2.le⟩
    · rw [hceq]; field_simp; ring

/-- A finite family of positive numbers has a positive lower bound. -/
lemma rxtStep_exists_delta_fin {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 < d k) :
    ∃ δ > 0, ∀ k, δ ≤ d k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun k => Fin.elim0 k⟩
  · have hn' : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_,
      fun k => Finset.inf'_le d (Finset.mem_univ k)⟩
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun k _ => hd k)

/-- Uniform continuity, uniform in the index, of a finite family continuous on a compact set. -/
lemma rxtStep_exists_uniform_family {n : ℕ} {f : Fin n → ℝ → ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hf : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => f k p.1 p.2.1 p.2.2) K) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      ∀ k, |f k p.1 p.2.1 p.2.2 - f k q.1 q.2.1 q.2.2| < η := by
  have hδk : ∀ k, ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      |f k p.1 p.2.1 p.2.2 - f k q.1 q.2.1 q.2.2| < η := by
    intro k
    obtain ⟨δ, hδ, hδ'⟩ :=
      (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous (hf k))) η hη
    exact ⟨δ, hδ, fun p hp q hq hpq => by
      have h := hδ' p hp q hq hpq
      rwa [Real.dist_eq] at h⟩
  choose d hd0 hd using hδk
  obtain ⟨δ, hδ0, hδle⟩ := rxtStep_exists_delta_fin d hd0
  exact ⟨δ, hδ0, fun p hp q hq hpq k => hd k p hp q hq (lt_of_lt_of_le hpq (hδle k))⟩

/-- Uniform continuity of `p ↦ ∑ k, |f k p|` on a compact set. -/
lemma rxtStep_exists_uniform_sum {n : ℕ} {f : Fin n → ℝ → ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hf : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => f k p.1 p.2.1 p.2.2) K) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      |(∑ k, |f k p.1 p.2.1 p.2.2|) - (∑ k, |f k q.1 q.2.1 q.2.2|)| < η := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => ∑ k, |f k p.1 p.2.1 p.2.2|) K :=
    continuousOn_finset_sum Finset.univ (fun k _ => (hf k).abs)
  obtain ⟨δ, hδ, hδ'⟩ :=
    (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcont)) η hη
  exact ⟨δ, hδ, fun p hp q hq hpq => by
    have h := hδ' p hp q hq hpq
    rwa [Real.dist_eq] at h⟩

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
lemma rxtStep_abs_add4_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- Replacing the frozen value of `F` by its value at a point: if `a` is continuous on
`[l,u]`, `F` is continuous on `[l,u]`, `|a| ≤ A` and `|c - F| ≤ η` there, then
`|(∫ a) * c - ∫ a * F| ≤ A * η * (u - l)`. -/
lemma rxtStep_correction_le {a F : ℝ → ℝ} {l u c A η : ℝ} (hlu : l ≤ u)
    (hac : ContinuousOn a (Set.uIcc l u)) (hFc : ContinuousOn F (Set.uIcc l u))
    (ha : ∀ x ∈ Set.Icc l u, |a x| ≤ A) (hΔ : ∀ x ∈ Set.Icc l u, |c - F x| ≤ η)
    (hA0 : 0 ≤ A) (hη0 : 0 ≤ η) :
    |(∫ x in l..u, a x) * c - ∫ x in l..u, a x * F x| ≤ A * η * (u - l) := by
  have hmulI : IntervalIntegrable (fun x => a x * F x) volume l u :=
    (hac.mul hFc).intervalIntegrable
  have hcI : IntervalIntegrable (fun x => a x * c) volume l u :=
    (hac.mul continuousOn_const).intervalIntegrable
  have h1 : (∫ x in l..u, a x) * c = ∫ x in l..u, a x * c :=
    (intervalIntegral.integral_mul_const c a).symm
  have h2 : (∫ x in l..u, a x * c) - (∫ x in l..u, a x * F x)
      = ∫ x in l..u, a x * (c - F x) := by
    rw [← intervalIntegral.integral_sub hcI hmulI]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [h1, h2]
  calc |∫ x in l..u, a x * (c - F x)| ≤ ∫ x in l..u, |a x * (c - F x)| :=
        intervalIntegral.abs_integral_le_integral_abs hlu
    _ ≤ ∫ x in l..u, A * η := by
        refine intervalIntegral.integral_mono_on hlu ((hac.mul (continuousOn_const.sub hFc)).intervalIntegrable).abs
          intervalIntegrable_const ?_
        intro x hx
        rw [abs_mul]
        exact mul_le_mul (ha x hx) (hΔ x hx) (abs_nonneg _) hA0
    _ = A * η * (u - l) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

end Work.FTS_RegExport.RXT
