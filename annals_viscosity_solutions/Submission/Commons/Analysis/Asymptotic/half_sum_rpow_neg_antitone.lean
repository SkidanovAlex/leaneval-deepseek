import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Set

namespace Commons.Analysis.Asymptotic

/-- For `0 < p`, `0 < A` and `B < A`, the symmetric average
`u ↦ (1/2) * ((A + u) ^ (-p) + (A - u) ^ (-p))` is monotone on `[0, B]`.
This is the analytic core of the fact that
`g ↦ (1/2) * ((A + B cos g) ^ (-p) + (A - B cos g) ^ (-p))` is antitone. -/
lemma monotoneOn_half_sum_rpow_neg {p A B : ℝ} (hp : 0 < p) (hA : 0 < A) (hBA : B < A) :
    MonotoneOn (fun u : ℝ => (1 / 2) * ((A + u) ^ (-p) + (A - u) ^ (-p))) (Set.Icc 0 B) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 B)
  · apply ContinuousOn.const_mul
    apply ContinuousOn.add
    · exact ((continuous_const.add continuous_id).continuousOn).rpow_const
        (fun u hu => Or.inl (ne_of_gt (show 0 < A + u by linarith [hu.1])))
    · exact ((continuous_const.sub continuous_id).continuousOn).rpow_const
        (fun u hu => Or.inl (ne_of_gt (show 0 < A - u by linarith [hu.2])))
  · intro x hx
    have hx0 : 0 ≤ x := (interior_subset hx).1
    have hxB : x ≤ B := (interior_subset hx).2
    have hxpos : 0 < A + x := by linarith
    have hxneg : 0 < A - x := by linarith
    have h1 : HasDerivAt (fun u : ℝ => (A + u) ^ (-p)) ((-p) * (A + x) ^ (-p - 1)) x := by
      have := ((hasDerivAt_const x A).add (hasDerivAt_id x)).rpow_const (p := -p)
        (Or.inl (ne_of_gt hxpos))
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => (A - u) ^ (-p)) (p * (A - x) ^ (-p - 1)) x := by
      have := ((hasDerivAt_const x A).sub (hasDerivAt_id x)).rpow_const (p := -p)
        (Or.inl (ne_of_gt hxneg))
      simpa using this
    have hsum := h1.add h2
    have hcm := hsum.const_mul (1 / 2 : ℝ)
    simpa using hcm.hasDerivWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := (interior_subset hx).1
    have hxB : x ≤ B := (interior_subset hx).2
    have hxpos : 0 < A + x := by linarith
    have hxneg : 0 < A - x := by linarith
    have hneg : -p - 1 < 0 := by linarith
    have hle : (A + x) ^ (-p - 1) ≤ (A - x) ^ (-p - 1) := by
      rw [Real.rpow_le_rpow_iff_of_neg hxpos hxneg hneg]
      linarith
    have heq : -(p * (A + x) ^ (-p - 1)) + p * (A - x) ^ (-p - 1)
        = p * ((A - x) ^ (-p - 1) - (A + x) ^ (-p - 1)) := by ring
    rw [heq]
    have h2 : 0 ≤ (A - x) ^ (-p - 1) - (A + x) ^ (-p - 1) := by linarith
    positivity

theorem half_sum_rpow_neg_antitone {p A B : ℝ} (hp : 0 < p) (hA : 0 < A) (hB : 0 ≤ B)
    (hBA : B < A) :
    AntitoneOn (fun g : ℝ =>
        (1 / 2) * ((A + B * Real.cos g) ^ (-p) + (A - B * Real.cos g) ^ (-p)))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hmono : MonotoneOn (fun u : ℝ => (1 / 2) * ((A + u) ^ (-p) + (A - u) ^ (-p)))
      (Set.Icc 0 B) := monotoneOn_half_sum_rpow_neg hp hA hBA
  have hcos' : AntitoneOn Real.cos (Set.Icc 0 (Real.pi / 2)) :=
    Real.antitoneOn_cos.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have hcos : AntitoneOn (fun g : ℝ => B * Real.cos g) (Set.Icc 0 (Real.pi / 2)) := by
    intro g1 hg1 g2 hg2 h12
    exact mul_le_mul_of_nonneg_left (hcos' hg1 hg2 h12) hB
  have hmaps : Set.MapsTo (fun g : ℝ => B * Real.cos g) (Set.Icc 0 (Real.pi / 2))
      (Set.Icc 0 B) := by
    intro g hg
    refine ⟨mul_nonneg hB (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hg.1, Real.pi_pos], by linarith [hg.2, Real.pi_pos]⟩), ?_⟩
    calc B * Real.cos g ≤ B * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one g) hB
      _ = B := mul_one B
  exact hmono.comp_AntitoneOn hcos hmaps

end Commons.Analysis.Asymptotic