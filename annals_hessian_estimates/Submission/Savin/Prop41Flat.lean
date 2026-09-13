import Submission.Savin.Prop41Main
import Submission.Savin.Correction
import Submission.Savin.Prop41

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

theorem pairOp_eq_trOp_mul (S M : ℝ⁴ →L[ℝ] ℝ⁴) : pairOp S M = trOp (S * M) := by
  rw [pairOp_eq_trace, trOp]
  rfl

theorem continuous_pairOp_left (M : ℝ⁴ →L[ℝ] ℝ⁴) :
    Continuous (fun S : ℝ⁴ →L[ℝ] ℝ⁴ => pairOp S M) := by
  have h : (fun S : ℝ⁴ →L[ℝ] ℝ⁴ => pairOp S M)
      = fun S => ∑ i : Fin 4, ⟪S (M (stdB4 i)), stdB4 i⟫ := by
    funext S
    rfl
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact Continuous.inner
    ((ContinuousLinearMap.apply ℝ ℝ⁴ (M (stdB4 i))).continuous) continuous_const

theorem one_div_le_one_div_of_le {a b : ℕ} (h : a ≤ b) (hb : 0 < b) :
    (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
  linarith

theorem tendsto_eseq {eseq : ℕ → ℝ} (he0 : ∀ m, 0 < eseq m) (he1 : ∀ m, eseq m ≤ 1 / (m + 1)) :
    Tendsto eseq atTop (𝓝 0) := by
  have h2 : ∀ m : ℕ, eseq m ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have h := he1 m
    have h3 : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    simpa only [h3] using h
  have h3 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h
  exact squeeze_zero (fun m => (he0 m).le) h2 h3


theorem eventually_abs_le_of_tendsto_zero {u : ℕ → ℝ} (h : Tendsto u atTop (𝓝 0)) {e : ℝ}
    (he : 0 < e) : ∀ᶠ m in atTop, |u m| ≤ e := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h e he
  rw [Filter.eventually_atTop]
  refine ⟨N, fun m hm => ?_⟩
  have h2 := hN m hm
  rw [Real.dist_eq, sub_zero] at h2
  exact h2.le

theorem prop41_core {c c' C θ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hC : 0 < C)
    (hθpos : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hθ1 : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2)
    (hθsmall : C * θ ^ 3 ≤ θ ^ ((5 : ℝ) / 2) / 4)
    (hCbound : ∀ (N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴) (e : ℕ → ℝ) (v : ℕ → ℝ⁴ → ℝ)
      (Nlim : ℝ⁴ →L[ℝ] ℝ⁴) (g : ℝ⁴ → ℝ) (φ : ℕ → ℕ)
      (hN : ∀ k, (N (φ k)).IsSymmetric) (hN1 : ∀ k, s2 (N (φ k)) = 1)
      (htrN : ∀ k, 0 < trOp (N (φ k))) (he0 : ∀ k, 0 < e (φ k))
      (hcq : ∀ k u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N (φ k)) u, u⟫)
      (hcq' : ∀ k u, ⟪cofOp (N (φ k)) u, u⟫ ≤ c' * ‖u‖ ^ 2)
      (hNtend : Tendsto (fun k => N (φ k)) atTop (𝓝 Nlim))
      (hetend : Tendsto (fun k => e (φ k)) atTop (𝓝 0))
      (hv : ∀ k, ContDiffOn ℝ 2 (v (φ k)) (ball 0 1))
      (heq : ∀ k, ∀ x ∈ ball 0 1, s2 (N (φ k) + e (φ k) • hessOp (v (φ k)) x) = 1)
      (hpos : ∀ k, ∀ x ∈ ball 0 1, 0 < trOp (N (φ k) + e (φ k) • hessOp (v (φ k)) x))
      (hbdd : ∀ k, ∀ x ∈ ball 0 1, |v (φ k) x| ≤ 1)
      (hconv : ∀ K, K ⊆ ball 0 1 → IsCompact K → TendstoUniformlyOn (fun k => v (φ k)) g atTop K)
      (θ' : ℝ) (hθ' : 0 < θ') (hθ'2 : θ' ≤ 1 / 2)
      (hθ'1 : 2 * θ' * Real.sqrt (c' / c) ≤ 1 / 2),
      ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
        P₂.IsSymmetric ∧ trOp (cofOp Nlim * P₂) = 0 ∧
        ∀ x ∈ closedBall 0 θ', |g x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ C * θ' ^ 3)
    {Nseq : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {eseq : ℕ → ℝ} {vseq : ℕ → ℝ⁴ → ℝ}
    (hN : ∀ m, (Nseq m).IsSymmetric) (hN1 : ∀ m, s2 (Nseq m) = 1) (htrN : ∀ m, 0 < trOp (Nseq m))
    (hcq : ∀ m u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (Nseq m) u, u⟫)
    (hcq' : ∀ m u, ⟪cofOp (Nseq m) u, u⟫ ≤ c' * ‖u‖ ^ 2)
    (he0 : ∀ m, 0 < eseq m) (he1 : ∀ m, eseq m ≤ 1 / (m + 1))
    (hv : ∀ m, ContDiffOn ℝ 2 (vseq m) (ball 0 2))
    (heq : ∀ m, ∀ x ∈ ball 0 2, Fop (cofOp (Nseq m)) (eseq m) (hessOp (vseq m) x) = 0)
    (hpos : ∀ m, ∀ x ∈ ball 0 2, 0 < trOp (Nseq m + eseq m • hessOp (vseq m) x))
    (hbdd : ∀ m, ∀ x ∈ ball 0 2, |vseq m x| ≤ 1)
    (hcon : ∀ m, ¬ ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
        P₂.IsSymmetric ∧ Fop (cofOp (Nseq m)) (eseq m) P₂ = 0 ∧
        ∀ x ∈ closedBall 0 θ, |vseq m x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ θ ^ ((5 : ℝ) / 2)) :
    False := by
  -- ## 1. subsequence with `N` convergent
  obtain ⟨φ₁, hφ₁, Nlim, hNtend₁⟩ := exists_subseq_base_tendsto hN hc hc'.le hcq hcq'
  -- ## 2. the `s2`-form on the subsequence
  have hball12 : ball (0 : ℝ⁴) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have heq_s2 : ∀ m, ∀ x ∈ ball 0 2,
      s2 (Nseq (φ₁ m) + eseq (φ₁ m) • hessOp (vseq (φ₁ m)) x) = 1 := by
    intro m x hx
    have hsym : (hessOp (vseq (φ₁ m)) x).IsSymmetric :=
      hessOp_symm_of_contDiffAt ((hv (φ₁ m)).contDiffAt (isOpen_ball.mem_nhds hx))
    exact (fop_eq_zero_iff_s2 (hN (φ₁ m)) hsym (ne_of_gt (he0 (φ₁ m)))
      (hN1 (φ₁ m))).mp (heq (φ₁ m) x hx)
  -- ## 3. the Arzelà--Ascoli subsequence
  have hp0 : (0 : ℝ) < 16 * c' / c + 2 := by positivity
  have hMrw : 1 + 128 * ((1 / (16 * c' / c + 2)) * (2 ^ (16 * c' / c + 2) - 1))
      = 1 + 128 * ((1 / (16 * c' / c + 2)) * (2 ^ (16 * c' / c + 2) - 1)) := rfl
  have hMgt : 1 < (1 + 128 * ((1 / (16 * c' / c + 2)) * (2 ^ (16 * c' / c + 2) - 1)) : ℝ) := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ (16 * c' / c + 2) :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    have h2 : 0 < (1 / (16 * c' / c + 2)) * ((2 : ℝ) ^ (16 * c' / c + 2) - 1) := by
      refine mul_pos (by positivity) ?_
      linarith
    linarith
  have het₁ : Tendsto (fun m => eseq (φ₁ m)) atTop (𝓝 0) :=
    (tendsto_eseq he0 he1).comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, g, hgconv₂⟩ :=
    exists_subseq_tendstoUniformly (N := fun m => Nseq (φ₁ m)) (e := fun m => eseq (φ₁ m))
      (v := fun m => vseq (φ₁ m)) (c := c) (c' := c') (p := 16 * c' / c + 2)
      (M := 1 + 128 * ((1 / (16 * c' / c + 2)) * (2 ^ (16 * c' / c + 2) - 1)))
      hc hc' hp0 hMgt rfl le_rfl (fun m => hN (φ₁ m)) (fun m => hN1 (φ₁ m))
      (fun m => htrN (φ₁ m)) (fun m => hcq (φ₁ m)) (fun m => hcq' (φ₁ m))
      (fun m => he0 (φ₁ m)) het₁ (fun m => hv (φ₁ m))
      heq_s2 (fun m x hx => hpos (φ₁ m) x hx)
      (fun m x hx => hbdd (φ₁ m) x hx)
  -- ## 4. the composed subsequence
  set φ : ℕ → ℕ := fun m => φ₁ (φ₂ m) with hφdef
  have hφt : Tendsto φ atTop atTop := hφ₁.tendsto_atTop.comp hφ₂.tendsto_atTop
  have hNtend : Tendsto (fun m => Nseq (φ m)) atTop (𝓝 Nlim) := by
    have h := hNtend₁.comp hφ₂.tendsto_atTop
    simpa [hφdef, Function.comp_def] using h
  have hetend : Tendsto (fun m => eseq (φ m)) atTop (𝓝 0) :=
    (tendsto_eseq he0 he1).comp hφt
  have hgconv : ∀ K, K ⊆ ball (0:ℝ⁴) 1 → IsCompact K →
      TendstoUniformlyOn (fun m => vseq (φ m)) g atTop K := by
    intro K hK hKc
    have h := hgconv₂.mono (fun z hz =>
      (by simpa only [mem_ball, mem_closedBall, dist_comm] using (le_of_lt (hK hz)) :
        z ∈ closedBall (0 : ℝ⁴) 1))
    simpa only [hφdef] using h
  -- ## 5. the limit is a viscosity solution
  have heq' : ∀ m, ∀ x ∈ ball (0:ℝ⁴) 1,
      s2 (Nseq (φ m) + eseq (φ m) • hessOp (vseq (φ m)) x) = 1 := by
    intro m x hx
    have h1 : x ∈ ball (0:ℝ⁴) 2 := hball12 hx
    have h2 := heq_s2 (φ₂ m) x h1
    simpa only [hφdef] using h2
  have hpos' : ∀ m, ∀ x ∈ ball (0:ℝ⁴) 1,
      0 < trOp (Nseq (φ m) + eseq (φ m) • hessOp (vseq (φ m)) x) := by
    intro m x hx
    have h1 : x ∈ ball (0:ℝ⁴) 2 := hball12 hx
    have h2 := hpos (φ m) x h1
    simpa only [hφdef] using h2
  have hisv : IsViscSolution (fun M => -trOp (cofOp Nlim * M)) g (ball 0 1) := by
    have h := isViscSolution_limit_s2 (s := ball (0:ℝ⁴) 1) isOpen_ball hc hc'.le
      (N := fun m => Nseq (φ m)) (e := fun m => eseq (φ m)) (v := fun m => vseq (φ m))
      (Nlim := Nlim) (g := g)
      (fun m => hN (φ m)) (fun m => hN1 (φ m)) (fun m => htrN (φ m)) (fun m => he0 (φ m))
      (fun m => hcq (φ m)) (fun m => hcq' (φ m)) hNtend hetend
      (fun m => (hv (φ m)).mono hball12) heq' hpos' hgconv
    have h1 : (fun M => -pairOp (cofOp Nlim) M) = fun M => -trOp (cofOp Nlim * M) := by
      funext M; rw [pairOp_eq_trOp_mul]
    rwa [h1] at h
  -- ## 6. continuity and boundedness of `g`
  have hgcont : ContinuousOn g (ball 0 1) := by
    intro x hx
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    have h1 : closedBall x (r / 2) ⊆ ball 0 1 := fun z hz =>
      hrsub (closedBall_subset_ball (by linarith) hz)
    have h2 : TendstoUniformlyOn (fun m => vseq (φ m)) g atTop (closedBall x (r / 2)) :=
      hgconv _ h1 (isCompact_closedBall x (r / 2))
    have h3 : ContinuousOn g (closedBall x (r / 2)) := by
      refine h2.continuousOn (Filter.Frequently.of_forall ?_)
      intro m
      exact ((hv (φ m)).continuousOn).mono (fun z hz => hball12 (h1 hz))
    have h4 : x ∈ closedBall x (r / 2) := by rw [mem_closedBall, dist_self]; positivity
    exact (h3.continuousWithinAt h4).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (by linarith)))
  have hgbdd : ∀ x ∈ ball 0 1, |g x| ≤ 1 := by
    intro x hx
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    have h1 : closedBall x (r / 2) ⊆ ball 0 1 := fun z hz =>
      hrsub (closedBall_subset_ball (by linarith) hz)
    have h2 : TendstoUniformlyOn (fun m => vseq (φ m)) g atTop (closedBall x (r / 2)) :=
      hgconv _ h1 (isCompact_closedBall x (r / 2))
    have hxmem : x ∈ closedBall x (r / 2) := by rw [mem_closedBall, dist_self]; positivity
    have h3 : Tendsto (fun m => vseq (φ m) x) atTop (𝓝 (g x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [← Filter.eventually_atTop]
      have h4 := (tendstoUniformlyOn_iff.mp h2) ε hε
      filter_upwards [h4] with m hm
      have h5 := hm x hxmem
      rw [Real.dist_eq] at h5 ⊢
      rwa [abs_sub_comm]
    exact le_of_tendsto h3.abs (Filter.Eventually.of_forall fun m => hbdd (φ m) x (hball12 hx))
  -- ## 7. the linear theory
  obtain ⟨P₂, P₁, P₀, hP₂sym, hP₂eq, hPbound⟩ :=
    hCbound (fun m => Nseq (φ m)) (fun m => eseq (φ m)) (fun m => vseq (φ m)) Nlim g id
      (fun m => hN (φ m)) (fun m => hN1 (φ m)) (fun m => htrN (φ m)) (fun m => he0 (φ m))
      (fun m => hcq (φ m)) (fun m => hcq' (φ m)) hNtend hetend
      (fun m => (hv (φ m)).mono hball12)
      (fun m x hx => heq_s2 (φ₂ m) x (hball12 hx)) (fun m x hx => hpos (φ m) x (hball12 hx))
      (fun m x hx => hbdd (φ m) x (hball12 hx)) hgconv θ hθpos hθ2 hθ1
  -- ## 8. the correction step
  have htrco_lim : 0 < trOp (cofOp Nlim) := by
    rw [trOp_eq_sum]
    have h1 : ∀ i : Fin 4, 0 < ⟪cofOp Nlim (stdB4 i), stdB4 i⟫ := by
      intro i
      have h2 : Tendsto (fun m => ⟪cofOp (Nseq (φ m)) (stdB4 i), stdB4 i⟫) atTop
          (𝓝 ⟪cofOp Nlim (stdB4 i), stdB4 i⟫) :=
        ((continuous_quadform (stdB4 i)).tendsto (cofOp Nlim)).comp (tendsto_cofOp hNtend)
      have h3 : ∀ᶠ m in atTop, c ≤ ⟪cofOp (Nseq (φ m)) (stdB4 i), stdB4 i⟫ := by
        filter_upwards with m
        have h4 := hcq (φ m) (stdB4 i)
        rw [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h4
        exact h4
      exact lt_of_lt_of_le hc (ge_of_tendsto h2 h3)
    exact Finset.sum_pos (fun i _ => h1 i) ⟨0, Finset.mem_univ 0⟩
  have hD0 : Tendsto (fun m => pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => pairOp (cofOp (Nseq (φ m))) P₂) atTop
        (𝓝 (pairOp (cofOp Nlim) P₂)) :=
      ((continuous_pairOp_left P₂).tendsto (cofOp Nlim)).comp (tendsto_cofOp hNtend)
    have h2 : pairOp (cofOp Nlim) P₂ = 0 := by rw [pairOp_eq_trOp_mul]; exact hP₂eq
    have h3 : Tendsto (fun m => eseq (φ m) * s2 P₂) atTop (𝓝 0) := by
      have h4 := hetend.mul_const (s2 P₂)
      simpa using h4
    have h5 : Tendsto (fun m => pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂) atTop
        (𝓝 (pairOp (cofOp Nlim) P₂ + 0)) := h1.add h3
    simpa [h2] using h5
  have hA0 : Tendsto (fun m => trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂) atTop
      (𝓝 (trOp (cofOp Nlim))) := by
    have h1 : Tendsto (fun m => trOp (cofOp (Nseq (φ m)))) atTop (𝓝 (trOp (cofOp Nlim))) :=
      tendsto_trOp (tendsto_cofOp hNtend)
    have h3 : Tendsto (fun m => 3 * eseq (φ m) * trOp P₂) atTop (𝓝 0) := by
      have h4 := hetend.const_mul (3 * trOp P₂)
      simpa [mul_assoc, mul_comm, mul_left_comm] using h4
    have h5 : Tendsto (fun m => trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂) atTop
        (𝓝 (trOp (cofOp Nlim) + 0)) := h1.add h3
    simpa using h5
  -- the corrected quadratics
  have htr_ev : ∀ᶠ m in atTop, trOp (cofOp Nlim) / 2 < trOp (cofOp (Nseq (φ m))) :=
    (tendsto_trOp (tendsto_cofOp hNtend)).eventually
      (isOpen_Ioi.mem_nhds (show trOp (cofOp Nlim) / 2 < trOp (cofOp Nlim) by linarith))
  have htr_ev2 : ∀ᶠ m in atTop, trOp (cofOp Nlim) / 2 ≤ trOp (cofOp (Nseq (φ m))) := by
    filter_upwards [htr_ev] with m hm
    linarith
  have hDsmall : ∀ᶠ m in atTop,
      |pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂|
        ≤ Real.sqrt θ * trOp (cofOp Nlim) / 16 := by
    refine eventually_abs_le_of_tendsto_zero hD0 ?_
    have h1 : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
    positivity
  have hA_ev : ∀ᶠ m in atTop,
      trOp (cofOp Nlim) / 4 ≤ trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂ := by
    have h3 : ∀ᶠ m in atTop, |3 * eseq (φ m) * trOp P₂| ≤ trOp (cofOp Nlim) / 4 := by
      have hu : Tendsto (fun m => 3 * eseq (φ m) * trOp P₂) atTop (𝓝 0) := by
        have h := (hetend.const_mul 3).mul_const (trOp P₂)
        simpa [mul_assoc] using h
      exact eventually_abs_le_of_tendsto_zero hu (by linarith)
    filter_upwards [htr_ev2, h3] with m hm hm2
    have h4 := neg_abs_le (3 * eseq (φ m) * trOp P₂)
    linarith
  have hdisc_ev : ∀ᶠ m in atTop,
      0 ≤ (trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂) ^ 2
        - 24 * eseq (φ m) * (pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂) := by
    have hbig : ∀ᶠ m in atTop,
        |24 * eseq (φ m) * (pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂)|
          ≤ (trOp (cofOp Nlim) / 4) ^ 2 / 2 := by
      have hu : Tendsto
          (fun m => 24 * eseq (φ m)
            * (pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂)) atTop (𝓝 0) := by
        have h := hD0.mul hetend
        have h2 : Tendsto (fun m => 24 * ((pairOp (cofOp (Nseq (φ m))) P₂
            + eseq (φ m) * s2 P₂) * eseq (φ m))) atTop (𝓝 0) := by
          simpa using h.const_mul 24
        simpa [mul_assoc, mul_comm, mul_left_comm] using h2
      refine eventually_abs_le_of_tendsto_zero hu ?_
      have h1 : 0 < trOp (cofOp Nlim) / 4 := by linarith
      positivity
    filter_upwards [hA_ev, hbig] with m hA hB
    have h1 : (trOp (cofOp Nlim) / 4) ^ 2
        ≤ (trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂) ^ 2 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ trOp (cofOp Nlim) / 4) hA 2
    have hb := abs_le.mp hB
    have h3 : 0 < (trOp (cofOp Nlim) / 4) ^ 2 := by
      have h4 : 0 < trOp (cofOp Nlim) / 4 := by linarith
      positivity
    linarith [h1, hb.2, h3]
  have hlam_ev : ∀ᶠ m in atTop,
      2 * |pairOp (cofOp (Nseq (φ m))) P₂ + eseq (φ m) * s2 P₂|
        / (trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂) ≤ Real.sqrt θ / 2 := by
    filter_upwards [hA_ev, hDsmall] with m hA hD
    have hApos : 0 < trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂ := by linarith
    have hsp : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
    rw [div_le_iff₀ hApos]
    have hmul := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ Real.sqrt θ / 2)
    linarith [hD, hmul, htrco_lim]
  have hgood : ∀ᶠ m in atTop, ∃ lam : ℝ,
      Fop (cofOp (Nseq (φ m))) (eseq (φ m)) (P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) = 0
        ∧ |lam| ≤ Real.sqrt θ / 2 := by
    filter_upwards [hA_ev, hdisc_ev, hlam_ev] with m h1 h2 h3
    have h1pos : 0 < trOp (cofOp (Nseq (φ m))) + 3 * eseq (φ m) * trOp P₂ := by linarith
    obtain ⟨lam, hlam1, hlam2⟩ :=
      exists_correct_fop (cofOp_isSymmetric (hN (φ m))) hP₂sym (he0 (φ m)) h1pos h2
    exact ⟨lam, hlam1, le_trans hlam2 h3⟩
  -- ## 9. the contradiction
  have hfinal : ∀ᶠ m in atTop, ∃ (Q₂ : ℝ⁴ →L[ℝ] ℝ⁴) (Q₁ : ℝ⁴ →L[ℝ] ℝ) (Q₀ : ℝ),
      Q₂.IsSymmetric ∧ Fop (cofOp (Nseq (φ m))) (eseq (φ m)) Q₂ = 0 ∧
      ∀ x ∈ closedBall 0 θ, |vseq (φ m) x - (⟪Q₂ x, x⟫ / 2 + Q₁ x + Q₀)| ≤ θ ^ ((5 : ℝ) / 2) := by
    have hconvθ : ∀ᶠ m in atTop, ∀ x ∈ closedBall (0 : ℝ⁴) θ,
        |vseq (φ m) x - g x| ≤ θ ^ ((5 : ℝ) / 2) / 4 := by
      have hsub : closedBall (0 : ℝ⁴) θ ⊆ ball 0 1 := by
        intro z hz
        rw [mem_closedBall, dist_zero_right] at hz
        rw [mem_ball, dist_zero_right]
        linarith
      have hpos : (0 : ℝ) < θ ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hθpos ((5 : ℝ) / 2)
      have h2 := hgconv _ hsub (isCompact_closedBall 0 θ)
      have h3 := (tendstoUniformlyOn_iff.mp h2) (θ ^ ((5 : ℝ) / 2) / 4) (by positivity)
      filter_upwards [h3] with m hm
      intro x hx
      have h4 := hm x hx
      rw [Real.dist_eq] at h4
      rw [abs_sub_comm] at h4
      exact le_of_lt h4
    filter_upwards [hgood, hconvθ] with m hg hc
    obtain ⟨lam, hlam1, hlam2⟩ := hg
    refine ⟨P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴), P₁, P₀,
      hP₂sym.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one), hlam1, ?_⟩
    intro x hx
    have h2 : |g x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ θ ^ ((5 : ℝ) / 2) / 4 :=
      le_trans (hPbound x hx) hθsmall
    have h4 : ⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀
        = ⟪P₂ x, x⟫ / 2 + P₁ x + P₀ + lam * ‖x‖ ^ 2 / 2 := by
      rw [add_apply, inner_add_left, ContinuousLinearMap.smul_apply, real_inner_smul_left,
        ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]
      ring
    have h3 : |(⟪P₂ x, x⟫ / 2 + P₁ x + P₀)
        - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)|
        ≤ θ ^ ((5 : ℝ) / 2) / 4 := by
      rw [h4]
      have h5 : ‖x‖ ≤ θ := by simpa [mem_closedBall, dist_zero_right] using hx
      have h6 : ‖x‖ ^ 2 ≤ θ ^ 2 := by nlinarith [norm_nonneg x]
      have hsq : Real.sqrt θ * θ ^ 2 = θ ^ ((5 : ℝ) / 2) := by
        have h1 : θ ^ ((5 : ℝ) / 2) = θ ^ (2 : ℝ) * θ ^ ((1 : ℝ) / 2) := by
          rw [show ((5 : ℝ) / 2) = (2 : ℝ) + (1 / 2 : ℝ) by norm_num,
            Real.rpow_add (by positivity)]
        rw [h1, Real.rpow_two, ← Real.sqrt_eq_rpow]
        ring
      have hA : (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)
          - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀ + lam * ‖x‖ ^ 2 / 2) = -(lam * ‖x‖ ^ 2 / 2) := by
        ring
      rw [hA, abs_neg]
      have h7 : |lam * ‖x‖ ^ 2 / 2| = |lam| * ‖x‖ ^ 2 / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [h7]
      have h10 : |lam| * ‖x‖ ^ 2 ≤ (Real.sqrt θ / 2) * θ ^ 2 :=
        mul_le_mul hlam2 h6 (sq_nonneg _) (by positivity)
      have h8 : |lam| * ‖x‖ ^ 2 / 2 ≤ Real.sqrt θ * θ ^ 2 / 4 := by linarith [h10]
      rw [hsq] at h8
      exact h8
    have h11 : |vseq (φ m) x - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)|
        ≤ |vseq (φ m) x - g x| + |g x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)|
          + |(⟪P₂ x, x⟫ / 2 + P₁ x + P₀)
            - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)| := by
      have h12 : vseq (φ m) x - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)
          = (vseq (φ m) x - g x) + (g x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀))
            + ((⟪P₂ x, x⟫ / 2 + P₁ x + P₀)
              - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)) := by ring
      rw [h12]
      exact abs_add_three _ _ _
    have h13 : θ ^ ((5 : ℝ) / 2) / 4 + θ ^ ((5 : ℝ) / 2) / 4 + θ ^ ((5 : ℝ) / 2) / 4
        < θ ^ ((5 : ℝ) / 2) := by
      have hp := Real.rpow_pos_of_pos hθpos ((5 : ℝ) / 2)
      linarith
    calc |vseq (φ m) x - (⟪(P₂ + lam • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) x, x⟫ / 2 + P₁ x + P₀)|
        ≤ θ ^ ((5 : ℝ) / 2) / 4 + θ ^ ((5 : ℝ) / 2) / 4 + θ ^ ((5 : ℝ) / 2) / 4 := by
          linarith [h11, hc x hx, h2, h3]
      _ ≤ θ ^ ((5 : ℝ) / 2) := le_of_lt h13
  obtain ⟨m, hm⟩ := hfinal.exists
  exact hcon (φ m) hm


/-! ## Savin's Proposition 4.1: improvement of flatness -/

/-- The "good" statement of Proposition 4.1 for a fixed `θ` and `ε₀`: every solution of the
perturbed equation with perturbation parameter `ε ≤ ε₀` is `θ^{5/2}`-close on `closedBall 0 θ` to an
exact solution of the same equation. -/
def FlatGood (c c' : ℝ) (θ ε₀ : ℝ) : Prop :=
  ∀ (N : ℝ⁴ →L[ℝ] ℝ⁴) (hN : N.IsSymmetric) (hN1 : s2 N = 1) (htrN : 0 < trOp N)
    (hcq : ∀ w, c * ‖w‖ ^ 2 ≤ ⟪cofOp N w, w⟫)
    (hcq' : ∀ w, ⟪cofOp N w, w⟫ ≤ c' * ‖w‖ ^ 2)
    (ε : ℝ) (v : ℝ⁴ → ℝ) (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hv : ContDiffOn ℝ 2 v (ball 0 2))
    (heq : ∀ x ∈ ball 0 2, Fop (cofOp N) ε (hessOp v x) = 0)
    (hpos : ∀ x ∈ ball 0 2, 0 < trOp (N + ε • hessOp v x))
    (hbdd : ∀ x ∈ ball 0 2, |v x| ≤ 1),
    ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
      P₂.IsSymmetric ∧ Fop (cofOp N) ε P₂ = 0 ∧
        ∀ x ∈ closedBall 0 θ, |v x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ θ ^ ((5 : ℝ) / 2)

/-- **Savin's Proposition 4.1 (improvement of flatness).**

There are `θ, ε₀ > 0`, depending only on the ellipticity constants `c ≤ c'`, such that for every
`σ₂ = 1` solution base `N` in the ellipticity class and every `C²` function `v` solving
`Fop (cofOp N) ε (D²v) = 0` on `ball 0 2` with `ε ≤ ε₀` and `|v| ≤ 1`, the function `v` is
`θ^{5/2}`-close on `closedBall 0 θ` to a quadratic that solves the same equation exactly. -/
theorem improvement_of_flatness {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 256 ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ FlatGood c c' θ ε₀ := by
  obtain ⟨C, hCpos, hCbound⟩ := quadratic_approx_of_limit hc hc'
  have hspos : 0 < Real.sqrt (c' / c) := Real.sqrt_pos.mpr (div_pos hc' hc)
  set θ : ℝ := min (min (min (1 / 2) (1 / (4 * C + 1) ^ 2)) (1 / (4 * Real.sqrt (c' / c) + 1)))
      (1 / 256)
    with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθ2 : θ ≤ 1 / 256 := by
    rw [hθdef]
    exact min_le_right _ _
  have hθ12 : θ ≤ 1 / 2 := by
    rw [hθdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθle1 : θ ≤ 1 / (4 * C + 1) ^ 2 := by
    rw [hθdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hθle2 : θ ≤ 1 / (4 * Real.sqrt (c' / c) + 1) := by
    rw [hθdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hsqθ : Real.sqrt θ ≤ 1 / (4 * C + 1) := by
    have h1 : Real.sqrt θ ≤ Real.sqrt (1 / (4 * C + 1) ^ 2) := Real.sqrt_le_sqrt hθle1
    have h2 : Real.sqrt (1 / (4 * C + 1) ^ 2) = 1 / (4 * C + 1) := by
      have h3 : (1 : ℝ) / (4 * C + 1) ^ 2 = (1 / (4 * C + 1)) ^ 2 := by
        rw [div_pow]
        norm_num
      rw [h3, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
    rwa [h2] at h1
  have h4Cθ : 4 * C * Real.sqrt θ ≤ 1 := by
    have h2 : (4 * C) * Real.sqrt θ ≤ (4 * C) * (1 / (4 * C + 1)) :=
      mul_le_mul_of_nonneg_left hsqθ (by linarith)
    have h3 : (4 * C) * (1 / (4 * C + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    linarith
  have hθsmall : C * θ ^ 3 ≤ θ ^ ((5 : ℝ) / 2) / 4 := by
    have hid : Real.sqrt θ * θ ^ ((5 : ℝ) / 2) = θ ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hθpos]
      norm_num
    have hpow : (0 : ℝ) < θ ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hθpos _
    have h1 : (4 * C) * (Real.sqrt θ * θ ^ ((5 : ℝ) / 2)) ≤ θ ^ ((5 : ℝ) / 2) := by
      have h2 := mul_le_mul_of_nonneg_right h4Cθ (le_of_lt hpow)
      rw [mul_assoc] at h2
      simpa using h2
    rw [hid] at h1
    linarith
  have hθs : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2 := by
    have h1 : θ * Real.sqrt (c' / c) ≤ (1 / (4 * Real.sqrt (c' / c) + 1)) * Real.sqrt (c' / c) :=
      mul_le_mul_of_nonneg_right hθle2 (le_of_lt hspos)
    have h3 : (1 / (4 * Real.sqrt (c' / c) + 1)) * Real.sqrt (c' / c) ≤ 1 / 4 := by
      rw [show (1 / (4 * Real.sqrt (c' / c) + 1)) * Real.sqrt (c' / c)
          = Real.sqrt (c' / c) / (4 * Real.sqrt (c' / c) + 1) by ring]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  by_contra hno
  have hno' : ∀ (t : ℝ), 0 < t → t ≤ 1 / 256 → ∀ e : ℝ, 0 < e → ¬ FlatGood c c' t e := by
    intro t ht1 ht2 e he hgood
    exact hno ⟨t, ht1, ht2, e, he, hgood⟩
  have hfail : ∀ m : ℕ, ∃ (N : ℝ⁴ →L[ℝ] ℝ⁴),
      N.IsSymmetric ∧ s2 N = 1 ∧ 0 < trOp N ∧
      (∀ w, c * ‖w‖ ^ 2 ≤ ⟪cofOp N w, w⟫) ∧ (∀ w, ⟪cofOp N w, w⟫ ≤ c' * ‖w‖ ^ 2) ∧
      ∃ (ε : ℝ) (v : ℝ⁴ → ℝ), 0 < ε ∧ ε ≤ 1 / ((m : ℝ) + 1) ∧ ContDiffOn ℝ 2 v (ball 0 2) ∧
        (∀ x ∈ ball 0 2, Fop (cofOp N) ε (hessOp v x) = 0) ∧
        (∀ x ∈ ball 0 2, 0 < trOp (N + ε • hessOp v x)) ∧
        (∀ x ∈ ball 0 2, |v x| ≤ 1) ∧
        (∀ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ), P₂.IsSymmetric →
          Fop (cofOp N) ε P₂ = 0 →
          ∃ x ∈ closedBall 0 θ, θ ^ ((5 : ℝ) / 2) < |v x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)|) := by
    intro m
    have h := hno' θ hθpos hθ2 (1 / ((m : ℝ) + 1)) (by positivity)
    unfold FlatGood at h
    push_neg at h
    exact h
  choose N hNsym hN1 htrN hcq hcq' ε v hε hεle hv heq hpos hbdd hconpart using hfail
  have hcon : ∀ m, ¬ ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ), P₂.IsSymmetric ∧
      Fop (cofOp (N m)) (ε m) P₂ = 0 ∧
      ∀ x ∈ closedBall 0 θ, |v m x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ θ ^ ((5 : ℝ) / 2) := by
    intro m hh
    obtain ⟨P₂, P₁, P₀, hP₂sym, hP₂eq, hPbd⟩ := hh
    obtain ⟨x, hx, hxg⟩ := hconpart m P₂ P₁ P₀ hP₂sym hP₂eq
    exact absurd (hPbd x hx) (not_le.mpr hxg)
  exact prop41_core (Nseq := N) (eseq := ε) (vseq := v) hc hc' hCpos hθpos hθ12 hθs hθsmall hCbound
    (fun m => hNsym m) (fun m => hN1 m) (fun m => htrN m)
    (fun m => hcq m) (fun m => hcq' m) (fun m => hε m) (fun m => hεle m)
    (fun m => hv m) (fun m => heq m) (fun m => hpos m) (fun m => hbdd m)
    (fun m => hcon m)


end

end Submission
