import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Asymptotics Metric

theorem inner_self_bound_near_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V Z : ℝ → E} (hV0 : V 0 = 0) (hd : HasDerivAt V (Z 0) 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Set.Ioo 0 δ, Inner.inner ℝ (V t) (V t) ≤ C * t ^ 2 := by
  -- Differentiability at 0 gives the little-o estimate V t = t • Z 0 + o(t).
  have hlittle : (fun h : ℝ => V h - V 0 - h • (Z 0)) =o[nhds 0] fun h : ℝ => h := by
    simpa using (hasDerivAt_iff_isLittleO_nhds_zero.mp hd)
  rw [Asymptotics.isLittleO_iff] at hlittle
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hlittle one_pos)
  refine ⟨(‖Z 0‖ + 1) ^ 2 + 1, by positivity, ε, hεpos, ?_⟩
  intro t ht
  have htε : |t| < ε := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact htε
  have hb : ‖V t - V 0 - t • Z 0‖ ≤ 1 * ‖t‖ := hε hball
  rw [hV0, sub_zero, one_mul, Real.norm_eq_abs] at hb
  -- ‖V t‖ ≤ (‖Z 0‖ + 1) * |t| on the small interval
  have hA : ‖V t‖ ≤ (‖Z 0‖ + 1) * |t| := by
    have h1 : ‖V t‖ = ‖(V t - t • Z 0) + t • Z 0‖ := by congr 1; abel
    have h2 : ‖(V t - t • Z 0) + t • Z 0‖ ≤ ‖V t - t • Z 0‖ + |t| * ‖Z 0‖ := by
      simpa [norm_smul, Real.norm_eq_abs] using norm_add_le (V t - t • Z 0) (t • Z 0)
    rw [h1]
    nlinarith [h2, hb, abs_nonneg t, norm_nonneg (Z 0)]
  have hB : ‖V t‖ ^ 2 ≤ ((‖Z 0‖ + 1) * |t|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hC : ((‖Z 0‖ + 1) * |t|) ^ 2 = (‖Z 0‖ + 1) ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  rw [hC] at hB
  have hinner : Inner.inner ℝ (V t) (V t) = ‖V t‖ ^ 2 := real_inner_self_eq_norm_sq (V t)
  rw [hinner]
  nlinarith [hB, sq_nonneg t, sq_nonneg (‖Z 0‖ + 1)]

end Work.Diff.C
