import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta1_exists_good_radius
import Submission.Commons.NumberTheory.Zeta.zeta1_growth_disk4
import Submission.Commons.NumberTheory.Zeta.riemannZeta1_ball_divisor_le_log
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.divisor_riemannZeta1_eq_completedRiemannZeta_ball
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le

set_option maxHeartbeats 1000000

noncomputable section

open Complex Filter Metric Set Function
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

/-- The norm of a `finsum` is at most the `finsum` of the norms. -/
private lemma norm_finsum_le_finsum_norm' {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (f : α → E) (hf : Function.HasFiniteSupport f) :
    ‖∑ᶠ i, f i‖ ≤ ∑ᶠ i, ‖f i‖ := by
  classical
  have hf' : (Function.support f).Finite := hf
  have hg : Function.HasFiniteSupport (fun i => ‖f i‖) := by
    rw [Function.HasFiniteSupport]
    refine hf'.subset ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hfx
    exact hx (by rw [hfx, norm_zero])
  rw [finsum_eq_finsetSum_of_support_subset f (s := hf'.toFinset)
      (by intro x hx; exact (Set.Finite.mem_toFinset hf').mpr hx)]
  rw [finsum_eq_finsetSum_of_support_subset (fun i => ‖f i‖) (s := hf'.toFinset)
      (by
        intro x hx
        rw [Function.mem_support] at hx
        exact (Set.Finite.mem_toFinset hf').mpr (by
          rw [Function.mem_support]
          intro hfx
          exact hx (by rw [hfx, norm_zero])))]
  exact norm_sum_le _ _

/-- If `‖f i‖ ≤ g i` pointwise with `g` of finite support, then `‖∑ᶠ f‖ ≤ ∑ᶠ g`. -/
private lemma norm_finsum_le_of_norm_le' {α : Type*} {f : α → ℂ} {g : α → ℝ}
    (hg : Function.HasFiniteSupport g) (hfg : ∀ u, ‖f u‖ ≤ g u) :
    ‖∑ᶠ u, f u‖ ≤ ∑ᶠ u, g u := by
  classical
  have hsupp : Function.HasFiniteSupport f := by
    rw [Function.HasFiniteSupport]
    refine hg.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hgu
    apply hu
    have hz : ‖f u‖ ≤ 0 := by have h := hfg u; rw [hgu] at h; exact h
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  have h1 : ‖∑ᶠ u, f u‖ ≤ ∑ᶠ u, ‖f u‖ := norm_finsum_le_finsum_norm' f hsupp
  have h2 : ∑ᶠ u, ‖f u‖ ≤ ∑ᶠ u, g u := by
    have hsupp' : Function.HasFiniteSupport (fun u => ‖f u‖) := by
      rw [Function.HasFiniteSupport]
      have : Function.support (fun u => ‖f u‖) = Function.support f := by
        ext x
        rw [Function.mem_support, Function.mem_support]
        constructor
        · intro h hfx; exact h (by rw [hfx, norm_zero])
        · intro h hnx; exact h (norm_eq_zero.mp hnx)
      rw [this]; exact hsupp
    exact finsum_le_finsum' hsupp' hg (fun u => hfg u)
  linarith only [h1, h2]

theorem zeta_logDeriv_local_approx_ne :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ σ : ℝ, (3 / 8 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
      riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 →
      ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) -
        (∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor completedRiemannZeta
              (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℂ) *
            (if ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - u‖ ≤ (1 / 8 : ℝ) then
              ((((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - u)⁻¹ else 0)))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 := by
  classical
  obtain ⟨Cg, hCgpos, hCgb⟩ := zeta1_growth_disk4
  obtain ⟨K, hKpos, hKb⟩ := riemannZeta1_ball_divisor_le_log
  refine ⟨224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.log (4 * Cg + 1) := Real.log_nonneg (by linarith)
    linarith
  intro t ht σ hσlo hσhi hfs
  obtain ⟨R, hR72, hR4, hcircR, hcircR2⟩ := zeta1_exists_good_radius t ht
  have hRpos : 0 < R := by linarith only [hR72]
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hsdef
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2)) u
    with hd
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall c (3 : ℝ)) u
    with hD
  set S : ℂ := ∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * (1 / (s - u))) with hS
  set T : ℂ := ∑ᶠ u : ℂ, (((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0))
    with hT
  set x : ℝ := Real.log (|t| + 3) + 1 with hx
  -- basic facts
  have hd_fin : Function.HasFiniteSupport d := by
    have hsupp := (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))).finiteSupport
      (isCompact_closedBall c (R / 2))
    simpa [Function.HasFiniteSupport, hd] using hsupp
  have hCgnn : (0 : ℝ) ≤ Cg * (|t| + 7) ^ 15 :=
    mul_nonneg (le_of_lt hCgpos) (pow_nonneg (by linarith only [abs_nonneg t]) 15)
  have hX0 : (0 : ℝ) ≤ 4 * Cg * (|t| + 7) ^ 15 := by nlinarith only [hCgnn]
  set A : ℝ := 4 * Cg * (|t| + 7) ^ 15 + 1 with hA
  have hA1 : (1 : ℝ) ≤ A := by rw [hA]; linarith only [hX0]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hs_norm : ‖s - c‖ = 2 - σ := by
    have hsc : s - c = ((σ - 2 : ℝ) : ℂ) := by
      simp only [hsdef, hc]; push_cast; ring
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    ring
  have hs13 : ‖s - c‖ ≤ 13 / 8 := by
    rw [hs_norm]; linarith only [hσlo]
  have hs_le : ‖s - c‖ ≤ (13 / 28 : ℝ) * R := by
    rw [hs_norm]
    have h2 : (13 / 8 : ℝ) ≤ 13 / 28 * R := by nlinarith only [hR72]
    linarith only [h2, hσlo]
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]
    have : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
    linarith only [this]
  have hx3x : x ≤ x ^ 3 := by
    have h := pow_le_pow_right₀ hx1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using h
  have hx31 : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1
  have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have ht7 : Real.log (|t| + 7) ≤ x := by
    have hpos : (0 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t]
    have hle : (|t| + 7 : ℝ) ≤ 2 * (|t| + 3) := by linarith only [ht]
    calc Real.log (|t| + 7) ≤ Real.log (2 * (|t| + 3)) :=
          Real.log_le_log (by linarith only [abs_nonneg t]) hle
      _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hpos)
      _ ≤ 1 + Real.log (|t| + 3) := by linarith only [hlog2]
      _ = x := by rw [hx]; ring
  have ht6 : Real.log (|t| + 6) ≤ x := by
    have hpos : (0 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t]
    have hle : (|t| + 6 : ℝ) ≤ 2 * (|t| + 3) := by linarith only [abs_nonneg t]
    calc Real.log (|t| + 6) ≤ Real.log (2 * (|t| + 3)) :=
          Real.log_le_log (by linarith only [abs_nonneg t]) hle
      _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hpos)
      _ ≤ 1 + Real.log (|t| + 3) := by linarith only [hlog2]
      _ = x := by rw [hx]; ring
  have hlogA : Real.log A ≤ Real.log (4 * Cg + 1) + 15 * Real.log (|t| + 7) := by
    have h7 : (1 : ℝ) ≤ (|t| + 7) ^ 15 := one_le_pow₀ (by linarith only [abs_nonneg t])
    have hle : A ≤ (4 * Cg + 1) * (|t| + 7) ^ 15 := by
      rw [hA]; nlinarith only [h7]
    calc Real.log A ≤ Real.log ((4 * Cg + 1) * (|t| + 7) ^ 15) :=
          Real.log_le_log hApos hle
      _ = Real.log (4 * Cg + 1) + Real.log ((|t| + 7) ^ 15) :=
          Real.log_mul (by linarith only [hCgpos]) (by positivity)
      _ = Real.log (4 * Cg + 1) + 15 * Real.log (|t| + 7) := by
          rw [Real.log_pow]; ring
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hclb : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    simpa only [hc] using zeta1_re_two_lower t
  have hfc : riemannZeta₁ c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hclb
    norm_num at hclb
  have hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖riemannZeta₁ w‖ ≤ A * ‖riemannZeta₁ c‖ := by
    intro w hw
    have hle4 : ‖w - c‖ ≤ 4 := by rw [hw]; exact hR4
    have hgw : ‖riemannZeta₁ w‖ ≤ Cg * (|t| + 7) ^ 15 := hCgb t ht w (by simpa only [hc] using hle4)
    calc ‖riemannZeta₁ w‖ ≤ Cg * (|t| + 7) ^ 15 := hgw
      _ = 4 * Cg * (|t| + 7) ^ 15 * (1 / 4) := by ring
      _ ≤ 4 * Cg * (|t| + 7) ^ 15 * ‖riemannZeta₁ c‖ :=
          mul_le_mul_of_nonneg_left hclb hX0
      _ ≤ (4 * Cg * (|t| + 7) ^ 15 + 1) * ‖riemannZeta₁ c‖ :=
          mul_le_mul_of_nonneg_right (by linarith only [hApos]) (norm_nonneg _)
      _ = A * ‖riemannZeta₁ c‖ := by rw [hA]
  have hmain : ‖logDeriv riemannZeta₁ s - S‖ ≤ 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) :=
    Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁) (c := c) (R := R)
      (A := A) (α := (13 / 28 : ℝ))
      hRpos hA1 (by norm_num) (by norm_num)
      (fun z _ => differentiable_riemannZeta₁.analyticAt z) hfc
      (fun w hw => hcircR w (by simpa only [hc] using hw))
      (fun w hw => hcircR2 w (by simpa only [hc] using hw))
      hAb hs_le hfs
  -- Step 1: rewrite T in terms of d
  have hTeq : T = ∑ᶠ u : ℂ,
      (((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (1 / (s - u)) else 0)) := by
    rw [hT]
    apply finsum_congr
    intro u
    by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · have hu : u ∈ Metric.closedBall c (R / 2) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖u - c‖ ≤ ‖u - s‖ + ‖s - c‖ := by
          calc ‖u - c‖ = ‖(u - s) + (s - c)‖ := by congr 1; ring
            _ ≤ ‖u - s‖ + ‖s - c‖ := norm_add_le _ _
        have h2 : ‖u - s‖ = ‖s - u‖ := norm_sub_rev _ _
        linarith only [h1, h2, h, hs13, hR72]
      have hDd : D u = d u :=
        (divisor_riemannZeta1_eq_completedRiemannZeta_ball (t := t) (R := R) ht hRpos hR4 hu).symm
      rw [if_pos h, if_pos h, hDd, one_div]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  -- Step 2: S - T as a finsum
  have hAfin : Function.HasFiniteSupport (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s - u))) := by
    refine hd_fin.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hdu
    exact hu (by rw [hdu]; simp)
  have hBfin : Function.HasFiniteSupport
      (fun u : ℂ => ((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (1 / (s - u)) else 0)) := by
    refine hd_fin.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hdu
    exact hu (by rw [hdu]; simp)
  have hST : S - T = ∑ᶠ u : ℂ,
      (((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then 0 else (s - u)⁻¹)) := by
    rw [hS, hTeq]
    rw [← finsum_sub_distrib hAfin hBfin]
    apply finsum_congr
    intro u
    by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero, sub_zero, one_div]
  -- Step 3: bound
  have hST_bound : ‖S - T‖ ≤ 8 * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    rw [hST]
    have hg : Function.HasFiniteSupport (fun u : ℂ => 8 * ((d u : ℤ) : ℝ)) := by
      refine hd_fin.subset ?_
      rw [Function.support_subset_iff]
      intro u hu hdu
      exact hu (by rw [hdu]; simp)
    have hbound := norm_finsum_le_of_norm_le' (f := fun u : ℂ =>
        ((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then 0 else (s - u)⁻¹))
      (g := fun u : ℂ => 8 * ((d u : ℤ) : ℝ)) hg (by
        intro u
        have hdnn : (0 : ℤ) ≤ d u :=
          (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁)
            (U := Metric.closedBall c (R / 2))
            (fun z _ => differentiable_riemannZeta₁.analyticAt z)) u
        have hdu : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := Int.cast_nonneg hdnn
        by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
        · rw [if_pos h, mul_zero, norm_zero]
          exact mul_nonneg (by norm_num) hdu
        · rw [if_neg h]
          have hnorm : ‖((d u : ℤ) : ℂ) * (s - u)⁻¹‖ = ((d u : ℤ) : ℝ) * ‖s - u‖⁻¹ := by
            rw [norm_mul, norm_inv, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg hdnn)]
          rw [hnorm]
          have hgt : (1 / 8 : ℝ) < ‖s - u‖ := lt_of_not_ge h
          have hle : ‖s - u‖⁻¹ ≤ 8 := by
            rw [← one_div]
            simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 8) (le_of_lt hgt)
          calc ((d u : ℤ) : ℝ) * ‖s - u‖⁻¹ ≤ ((d u : ℤ) : ℝ) * 8 :=
                mul_le_mul_of_nonneg_left hle hdu
            _ = 8 * ((d u : ℤ) : ℝ) := by ring)
    have hmul : (∑ᶠ u : ℂ, 8 * ((d u : ℤ) : ℝ)) = 8 * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) :=
      (mul_finsum (fun u : ℂ => ((d u : ℤ) : ℝ)) 8).symm
    rw [hmul] at hbound
    exact hbound
  have hdivle : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) ≤ K * (Real.log (|t| + 6) + 1) :=
    hKb t ht R hRpos hR4
  -- Step 4: the log arithmetic
  have hbound1 : 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) ≤ 224 * Real.log A := by
    have hdsq : (1 - 2 * (13 / 28 : ℝ)) ^ 2 = 1 / 196 := by norm_num
    rw [hdsq, div_le_iff₀ (mul_pos hRpos (by norm_num : (0 : ℝ) < 1 / 196))]
    have hkey : (4 : ℝ) ≤ 224 * R * (1 / 196) := by nlinarith only [hR72]
    have hh := mul_le_mul_of_nonneg_right hkey hlogA0
    nlinarith only [hh]
  have hb1 : 224 * Real.log A ≤ 224 * (Real.log (4 * Cg + 1) + 15 * x) := by
    have hmid : Real.log A ≤ Real.log (4 * Cg + 1) + 15 * x := by linarith only [hlogA, ht7]
    exact mul_le_mul_of_nonneg_left hmid (by norm_num)
  have hb2 : 8 * (K * (Real.log (|t| + 6) + 1)) ≤ 16 * K * x ^ 3 := by
    have h1 : Real.log (|t| + 6) + 1 ≤ 2 * x := by linarith only [ht6, hx1]
    have hK0 : (0 : ℝ) ≤ 8 * K := mul_nonneg (by norm_num) (le_of_lt hKpos)
    have h2 : 8 * K * (Real.log (|t| + 6) + 1) ≤ 8 * K * (2 * x) :=
      mul_le_mul_of_nonneg_left h1 hK0
    have h3 : 8 * K * (2 * x) ≤ 16 * K * x ^ 3 := by
      have hK1 : (0 : ℝ) ≤ 16 * K := mul_nonneg (by norm_num) (le_of_lt hKpos)
      have hh := mul_le_mul_of_nonneg_left hx3x hK1
      nlinarith only [hh]
    linarith only [h2, h3]
  have hfin : 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2)
        + 8 * (K * (Real.log (|t| + 6) + 1))
      ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * x ^ 3 := by
    have h3 : 224 * (Real.log (4 * Cg + 1) + 15 * x) + 16 * K * x ^ 3
        ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * x ^ 3 := by
      have hlogC0 : 0 ≤ Real.log (4 * Cg + 1) := Real.log_nonneg (by linarith only [hCgpos])
      have ha : 224 * Real.log (4 * Cg + 1) ≤ 224 * Real.log (4 * Cg + 1) * x ^ 3 := by
        have hh := mul_nonneg hlogC0 (by linarith only [hx31] : (0 : ℝ) ≤ x ^ 3 - 1)
        nlinarith only [hh]
      have hb : 3360 * x ≤ 3361 * x ^ 3 := by
        have hh := mul_le_mul_of_nonneg_left hx3x (by norm_num : (0 : ℝ) ≤ 3360)
        nlinarith only [hh, hx31]
      nlinarith only [ha, hb]
    linarith only [hbound1, hb1, hb2, h3]
  calc ‖logDeriv riemannZeta₁ s - T‖
      ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S - T‖ := by
        simpa [dist_eq_norm] using dist_triangle (logDeriv riemannZeta₁ s) S T
    _ ≤ 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) + 8 * (K * (Real.log (|t| + 6) + 1)) := by
        linarith only [hmain, hST_bound, hdivle]
    _ ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * (Real.log (|t| + 3) + 1) ^ 3 := hfin

end Commons.NumberTheory.Zeta
