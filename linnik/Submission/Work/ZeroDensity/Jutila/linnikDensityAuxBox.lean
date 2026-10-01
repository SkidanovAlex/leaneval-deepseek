import Mathlib
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

namespace Work.ZeroDensity.Jutila

open scoped Classical

/-- The honest kernel inequality behind the box count: at `s₀ = 1 + l + iT`, the real part of
`1/(s₀ - u)` is at least `1/(5l)` on the box `1 - l ≤ Re u ≤ 1`, `|Im u - T| ≤ l/2` (the sharp
constant is `4/17 > 1/5`). -/
private lemma kernel_lower {l T : ℝ} {u : ℂ} (hl : 0 < l) (hu1 : 1 - l ≤ u.re)
    (hu2 : u.re ≤ 1) (him : |u.im - T| ≤ l / 2) :
    1 / (5 * l) ≤ (1 + l - u.re) / ((1 + l - u.re) ^ 2 + (T - u.im) ^ 2) := by
  set x := 1 + l - u.re with hx
  set y := T - u.im with hy
  have hx1 : l ≤ x := by rw [hx]; linarith
  have hx2 : x ≤ 2 * l := by rw [hx]; linarith
  have hxpos : 0 < x := lt_of_lt_of_le hl hx1
  have hdenpos : 0 < x ^ 2 + y ^ 2 := by
    have := sq_pos_of_pos hxpos
    nlinarith [sq_nonneg y]
  have hy2 : y ^ 2 ≤ l ^ 2 / 4 := by
    have hab : |y| ≤ l / 2 := by rw [hy, abs_sub_comm]; exact him
    have h1 : -(l / 2) ≤ y := (abs_le.mp hab).1
    have h2 : y ≤ l / 2 := (abs_le.mp hab).2
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ l / 2 + y) (by linarith : (0:ℝ) ≤ l / 2 - y)]
  have hxsq : x ^ 2 ≤ 2 * l * x := by
    nlinarith [mul_nonneg (le_of_lt hxpos) (by linarith : (0:ℝ) ≤ 2 * l - x)]
  have hlsq : l ^ 2 ≤ l * x := by
    nlinarith [mul_nonneg (le_of_lt hl) (by linarith : (0:ℝ) ≤ x - l)]
  have hlxp : (0:ℝ) ≤ l * x := mul_nonneg (le_of_lt hl) (le_of_lt hxpos)
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 5 * l) hdenpos]
  nlinarith [hy2, hxsq, hlsq, hlxp]

/-- The geometric half: a zero `ρ` of the strip `0 < Re ρ < 1` whose imaginary part is within
`(1-σ)/2 ≤ 1/2` of `T ≥ 1` lies in the closed ball of radius `T + 2` about the origin. -/
private lemma mem_closedBall_of_box {ρ : ℂ} {σ T : ℝ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hσ0 : 0 ≤ σ) (him : |ρ.im - T| ≤ (1 - σ) / 2) (hT : 1 ≤ T) :
    ρ ∈ Metric.closedBall (0 : ℂ) (T + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have him' : |ρ.im - T| ≤ 1 / 2 := by linarith
  have hy : |ρ.im| ≤ T + 1 / 2 := by
    rw [abs_le]
    have h1 : ρ.im - T ≤ 1 / 2 := (abs_le.mp him').2
    have h2 : -(1 / 2) ≤ ρ.im - T := (abs_le.mp him').1
    constructor <;> linarith
  have hsq : ‖ρ‖ ^ 2 ≤ (T + 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : ρ.im ≤ T + 1 / 2 := (abs_le.mp hy).2
    have h2 : -(T + 1 / 2) ≤ ρ.im := (abs_le.mp hy).1
    have h3 : ρ.im ^ 2 ≤ (T + 1 / 2) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ T + 1 / 2 - ρ.im)
        (by linarith : (0:ℝ) ≤ T + 1 / 2 + ρ.im)]
    have h4 : ρ.re ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (le_of_lt hre0) (by linarith : (0:ℝ) ≤ 1 - ρ.re)]
    nlinarith [h3, h4]
  have h2 : ‖ρ‖ ≤ T + 2 := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg ρ), Real.sqrt_sq (by linarith : (0:ℝ) ≤ T + 2)] at h
  exact h2

/-- Elementary cancellation used for the scaled pointwise bound. -/
private lemma mul_mul_one_div_cancel (a b : ℝ) (ha : a ≠ 0) : a * (b * (1 / a)) = b := by
  rw [mul_comm a (b * (1 / a)), mul_assoc, mul_comm (1 / a) a, mul_one_div_cancel ha, mul_one]

/-- **The box count against the kernel sum.**  If `F` is entire with all its zeros in the open
critical strip `0 < Re z < 1`, then the multiplicity-weighted number of zeros in the box
`σ ≤ Re ρ ≤ 1`, `|Im ρ - T| ≤ (1-σ)/2` is at most `5(1-σ)` times the divisor sum of `F` over the
closed ball of radius `T + 2` weighted by the (positive) Jutila kernel
`Re (1/(1 + (1-σ) + iT - u))`.

Every zero `ρ` of the box lies in that ball (`mem_closedBall_of_box`), and there the kernel is at
least `1/(5(1-σ))` (`kernel_lower`), so each box zero contributes at least `1/(5(1-σ))` times its
multiplicity to the kernel sum; the divisor of the entire function `F` dominates the multiplicity
function (`apply_eq_zero_of_analyticOrderNatAt_ne_zero`,
`Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast`,
`MeromorphicOn.AnalyticOnNhd.divisor_nonneg`), and the comparison of the two `finsum`s is
`finsum_le_finsum'`. -/
theorem linnikDensityAuxBox (F : ℂ → ℂ) (han : AnalyticOnNhd ℂ F Set.univ)
    (hstrip : ∀ u : ℂ, F u = 0 → 0 < u.re ∧ u.re < 1)
    {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    (∑ᶠ ρ : ℂ, (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2
        then (analyticOrderNatAt F ρ : ℝ) else 0))
      ≤ 5 * (1 - σ) * ∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor F (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) *
            ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2)) := by
  classical
  have hUcompact : IsCompact (Metric.closedBall (0 : ℂ) (T + 2)) := isCompact_closedBall (0 : ℂ) (T + 2)
  have hmont : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) (T + 2)) := fun z _ => han z (Set.mem_univ z)
  have hdiv_nonneg : ∀ u : ℂ, (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hmont u
  have hd_fin : Function.HasFiniteSupport
      (fun u : ℂ => MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u) :=
    (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2))).finiteSupport hUcompact
  have hDfin : Function.HasFiniteSupport (fun u : ℂ => ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ)) :=
    hd_fin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h]; simp))
  have hRfin : Function.HasFiniteSupport (fun u : ℂ => ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ) * ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2))) :=
    hDfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, zero_mul]))
  have hpt : ∀ ρ : ℂ, (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) ≤ 5 * (1 - σ) * (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) ρ : ℤ) : ℝ) * ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (T - ρ.im) ^ 2))) := by
    intro ρ
    by_cases hc : analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2
    · have hLval : (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) = (analyticOrderNatAt F ρ : ℝ) := if_pos hc
      rw [hLval]
      obtain ⟨hm, hr1, hr2, him⟩ := hc
      have hF0 : F ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
      obtain ⟨hz0, hz1⟩ := hstrip ρ hF0
      have hmem : ρ ∈ (Metric.closedBall (0 : ℂ) (T + 2)) := mem_closedBall_of_box hz0 hz1 hσ0 him hT
      have hDval : ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) ρ : ℤ) : ℝ) = (analyticOrderNatAt F ρ : ℝ) := by
        rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hmont hmem]
        simp
      rw [hDval]
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ 1 - σ by linarith) with hzero | hpos
      · exfalso
        have hσ : σ = 1 := by linarith
        linarith [hz1]
      · have hk : 1 / (5 * (1 - σ)) ≤ ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (T - ρ.im) ^ 2)) :=
          kernel_lower hpos (by linarith : 1 - (1 - σ) ≤ ρ.re) hr2 him
        have hmnn : (0:ℝ) ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
        have hne : 5 * (1 - σ) ≠ 0 := by linarith
        calc (analyticOrderNatAt F ρ : ℝ)
            = 5 * (1 - σ) * ((analyticOrderNatAt F ρ : ℝ) * (1 / (5 * (1 - σ)))) :=
              (mul_mul_one_div_cancel (5 * (1 - σ)) (analyticOrderNatAt F ρ : ℝ) hne).symm
          _ ≤ 5 * (1 - σ) * ((analyticOrderNatAt F ρ : ℝ) * ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (T - ρ.im) ^ 2))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hmnn) (by linarith)
    · have hLval : (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) = 0 := if_neg hc
      rw [hLval]
      refine mul_nonneg (by linarith : (0:ℝ) ≤ 5 * (1 - σ)) ?_
      by_cases hDz : MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) ρ = 0
      · rw [show ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) ρ : ℤ) : ℝ) = 0 by rw [hDz]; simp]
        simp
      · have hmem : ρ ∈ (Metric.closedBall (0 : ℂ) (T + 2)) := by
          by_contra h
          exact hDz (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
            (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2))) h)
        have hord : analyticOrderNatAt F ρ ≠ 0 := by
          intro h0
          refine hDz ?_
          rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hmont hmem, h0]
          simp
        obtain ⟨hz0, hz1⟩ := hstrip ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
        have hnum : 0 < 1 + (1 - σ) - ρ.re := by linarith
        have hden : 0 < (1 + (1 - σ) - ρ.re) ^ 2 + (T - ρ.im) ^ 2 := by
          have hh : (0:ℝ) < (1 + (1 - σ) - ρ.re) ^ 2 := pow_pos hnum 2
          nlinarith [sq_nonneg (T - ρ.im)]
        exact mul_nonneg (by exact_mod_cast hdiv_nonneg ρ) (le_of_lt (div_pos hnum hden))
  have hSfin : Function.HasFiniteSupport (fun u : ℂ => 5 * (1 - σ) * (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ) * ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2)))) :=
    hRfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, mul_zero]))
  have hLfin : Function.HasFiniteSupport (fun ρ : ℂ => (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0)) :=
    hRfin.subset (fun ρ hρ => by
      rw [Function.mem_support] at hρ ⊢
      have hLnn : 0 ≤ (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) := by
        by_cases hc : analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2
        · rw [if_pos hc]; exact Nat.cast_nonneg _
        · rw [if_neg hc]
      intro hR0
      have hle := hpt ρ
      rw [hR0, mul_zero] at hle
      exact hρ (le_antisymm hle hLnn))
  have key : 5 * (1 - σ) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ) * ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2))) = (∑ᶠ u : ℂ, 5 * (1 - σ) * (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ) * ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2)))) :=
    mul_finsum (fun u : ℂ => ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (T + 2)) u : ℤ) : ℝ) * ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2))) (5 * (1 - σ))
  rw [key]
  exact finsum_le_finsum' hLfin hSfin hpt

end Work.ZeroDensity.Jutila
