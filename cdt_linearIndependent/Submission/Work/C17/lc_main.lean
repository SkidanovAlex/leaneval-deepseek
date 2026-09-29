import Submission.Work.C17.lc_aux
import Submission.Work.C17I.logcoeff_eq_zero_region
import Submission.Work.C17I.seventeen_subst_eval
import Submission.Work.C17I.seventeen_subst_eval_disc
import Submission.Work.C17I.logP_coeff_bound_sharp
import Submission.Work.C17I.pw_continuation
import Submission.Work.C17I.J_package
import Submission.Work.C17I.dy_iter_log_struct
import Submission.Work.C17I.integral_log_struct
import Submission.Work.C17I.DyIter_comp_yC
import Submission.Work.C17I.Gfun_repr
import Submission.Work.C17I.seventeen_coeff_bounds_sharp

/-!
# The `(LC)` extraction for `Work.C17.relation_to_LC`
-/

namespace Work.C17I

open scoped BigOperators Topology
open Polynomial Filter

noncomputable section

/-! ## `pAtY` is holomorphic away from `z = 1` -/

lemma pAtY_differentiableOn {s δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 - s) (p : Polynomial ℚ) :
    DifferentiableOn ℂ (Work.C17.pAtY p) (Metric.ball ((s : ℂ)) δ) := by
  have hne : ∀ z ∈ Metric.ball ((s : ℂ)) δ, z ≠ 1 := by
    intro z hz hz1
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    rw [hz1] at hz
    have h2 : ‖(1:ℂ) - (s:ℂ)‖ = 1 - s := by
      have hc : (1:ℂ) - (s:ℂ) = (((1 - s : ℝ)) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h2] at hz
    linarith
  have hyC : DifferentiableOn ℂ Work.C17.yC (Metric.ball ((s : ℂ)) δ) := by
    have h : Work.C17.yC = fun z : ℂ => z ^ 2 / (z - 1) := rfl
    rw [h]
    refine (differentiableOn_id.pow 2).div
      (differentiableOn_id.sub (differentiableOn_const (1:ℂ))) (fun z hz => ?_)
    exact sub_ne_zero.mpr (hne z hz)
  have hpoly : DifferentiableOn ℂ (fun y : ℂ => (p.map (algebraMap ℚ ℂ)).eval y) Set.univ :=
    Polynomial.differentiableOn (p := p.map (algebraMap ℚ ℂ)) (s := Set.univ)
  refine (hpoly.comp hyC (fun z _ => Set.mem_univ _)).congr (fun z hz => ?_)
  simp only [Function.comp_apply, Work.C17.pAtY, Polynomial.eval_map]

/-! ## The extraction step -/

/-- **The `(LC)` extraction.**  Suppose that on the region
`V = ball (s:ℂ) δ ∩ ball 0 ρ` the three blocks of the pulled-back relation vanish
(`hR0`), that the `G`-block has the logarithm structure `(hGk)` with non-log parts
`Gk` holomorphic on the whole ball, and that the integral block has the logarithm
structure `(hHn)` with non-log parts `Hn` holomorphic on the whole ball.  Then the
`(LC)` relation holds on the whole ball. -/
theorem LC_extract
    (P : Fin 17 → Polynomial ℚ) {s δ ρ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hρ : ρ < s)
    (hδ1 : δ < 1 - s) (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2)
    (hneV : (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ).Nonempty)
    {y1 𝔾 : ℂ → ℂ} {κ : ℂ} (hκ : κ ≠ 0)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball (s : ℂ) δ))
    {J : Fin 6 → ℂ → ℂ} (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball (s : ℂ) δ))
    {Fb : Fin 7 → ℂ → ℂ} (hFbd : ∀ b, DifferentiableOn ℂ (Fb b) (Metric.ball (s : ℂ) δ))
    {Gk : Fin 4 → ℂ → ℂ} (hGkd : ∀ k, DifferentiableOn ℂ (Gk k) (Metric.ball (s : ℂ) δ))
    (hGk : ∀ k : Fin 4, ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        Work.C17.DyIter (k : ℕ) 𝔾 z
          = κ * Work.C17.DyIter (k : ℕ) y1 z * Complex.log (s - z)
            + Gk k z / (z - s) ^ (k : ℕ))
    {FI : Fin 6 → ℂ → ℂ}
    {Hn : Fin 6 → ℂ → ℂ} (hHnd : ∀ i, DifferentiableOn ℂ (Hn i) (Metric.ball (s : ℂ) δ))
    (hHn : ∀ i : Fin 6, ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        FI i z = κ * J (Work.C17.jrev i) z * Complex.log (s - z) + Hn i z / (z - s))
    (hR0 : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) 𝔾 z)
        + (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
        + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z) = 0) :
    ∀ z ∈ Metric.ball (s : ℂ) δ,
      (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) y1 z)
        + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z
            * J (Work.C17.jrev i) z) = 0 := by
  have hDy : ∀ k : ℕ, DifferentiableOn ℂ (Work.C17.DyIter k y1) (Metric.ball (s : ℂ) δ) :=
    fun k => Work.C17.DyIter_differentiableOn Metric.isOpen_ball hz0 hz2 k hy1d
  set Gt : ℂ → ℂ := fun z =>
      (z - s) ^ 3 * (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
        + (∑ k : Fin 4, (z - s) ^ (3 - (k : ℕ)) * Work.C17.pAtY (P (Work.C17.gIdx k)) z * Gk k z)
        + (∑ i : Fin 6, (z - s) ^ 2 * Work.C17.pAtY (P (Work.C17.iIdx i)) z * Hn i z) with hGt
  set LHS : ℂ → ℂ := fun z =>
      (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) y1 z)
        + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * J (Work.C17.jrev i) z) with hLHS
  set A : ℂ → ℂ := fun z => κ * LHS z with hA
  have hpa : ∀ q : Fin 17, DifferentiableOn ℂ (Work.C17.pAtY (P q)) (Metric.ball (s : ℂ) δ) :=
    fun q => pAtY_differentiableOn hδ hδ1 (P q)
  have hp0 : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ, z - s ≠ 0 := by
    intro z hz h
    have hzs : z = s := sub_eq_zero.mp h
    have h1 : ‖z‖ < ρ := by
      have h2 := hz.2
      rwa [Metric.mem_ball, dist_zero_right] at h2
    rw [hzs] at h1
    have h2 : ‖((s : ℝ) : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hs)]
    rw [h2] at h1
    linarith
  have hG : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      (z - s) ^ 3 * (∑ k : Fin 4,
          Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) 𝔾 z)
        = κ * (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
              * Work.C17.DyIter (k : ℕ) y1 z)
            * (z - s) ^ 3 * Complex.log (s - z)
          + ∑ k : Fin 4, (z - s) ^ (3 - (k : ℕ)) * Work.C17.pAtY (P (Work.C17.gIdx k)) z * Gk k z := by
    intro z hz
    have hzw : z - s ≠ 0 := hp0 z hz
    have hstep : ∀ k : Fin 4, (z - s) ^ 3 * (Work.C17.pAtY (P (Work.C17.gIdx k)) z
          * Work.C17.DyIter (k : ℕ) 𝔾 z)
        = Work.C17.pAtY (P (Work.C17.gIdx k)) z
            * (κ * Work.C17.DyIter (k : ℕ) y1 z * (z - s) ^ 3 * Complex.log (s - z))
          + (z - s) ^ (3 - (k : ℕ)) * Work.C17.pAtY (P (Work.C17.gIdx k)) z * Gk k z := by
      intro k
      have hk : (k : ℕ) ≤ 3 := by omega
      have hpow : (z - s) ^ (3 - (k : ℕ)) = (z - s) ^ 3 * ((z - s) ^ (k : ℕ))⁻¹ :=
        pow_sub₀ (z - s) hzw hk
      rw [hGk k z hz, div_eq_mul_inv, hpow]
      ring
    have hlog : (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
          * (κ * Work.C17.DyIter (k : ℕ) y1 z * (z - s) ^ 3 * Complex.log (s - z)))
        = κ * (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
              * Work.C17.DyIter (k : ℕ) y1 z) * (z - s) ^ 3 * Complex.log (s - z) := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_add_distrib, hlog]
  have hI : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      (z - s) ^ 3 * (∑ i : Fin 6,
          Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z)
        = κ * (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * J (Work.C17.jrev i) z)
            * (z - s) ^ 3 * Complex.log (s - z)
          + ∑ i : Fin 6, (z - s) ^ 2 * Work.C17.pAtY (P (Work.C17.iIdx i)) z * Hn i z := by
    intro z hz
    have hzw : z - s ≠ 0 := hp0 z hz
    have hstep : ∀ i : Fin 6, (z - s) ^ 3 * (Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z)
        = Work.C17.pAtY (P (Work.C17.iIdx i)) z
            * (κ * J (Work.C17.jrev i) z * (z - s) ^ 3 * Complex.log (s - z))
          + (z - s) ^ 2 * Work.C17.pAtY (P (Work.C17.iIdx i)) z * Hn i z := by
      intro i
      have hpow : (z - s) ^ 2 = (z - s) ^ 3 * (z - s)⁻¹ := by
        have h1 : (z - s) ^ 3 = (z - s) ^ 2 * (z - s) := by
          rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ]
        rw [h1, mul_assoc, mul_inv_cancel₀ hzw, mul_one]
      rw [hHn i z hz, div_eq_mul_inv, hpow]
      ring
    have hlog : (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z
          * (κ * J (Work.C17.jrev i) z * (z - s) ^ 3 * Complex.log (s - z)))
        = κ * (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * J (Work.C17.jrev i) z)
            * (z - s) ^ 3 * Complex.log (s - z) := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib, hlog]
  have hexp : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      (z - s) ^ 3 * ((∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
            * Work.C17.DyIter (k : ℕ) 𝔾 z)
          + (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
          + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z))
        = A z * (z - s) ^ 3 * Complex.log (s - z) + Gt z := by
    intro z hz
    rw [mul_add, mul_add, hG z hz, hI z hz]
    simp only [hA, hGt, hLHS]
    ring
  have hid : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      A z * (z - s) ^ 3 * Complex.log (s - z) + Gt z = 0 := by
    intro z hz
    have h1 := hexp z hz
    rw [hR0 z hz, mul_zero] at h1
    exact h1.symm
  have hLHSd : DifferentiableOn ℂ LHS (Metric.ball (s : ℂ) δ) := by
    rw [hLHS]
    refine DifferentiableOn.add ?_ ?_
    · exact DifferentiableOn.fun_sum (fun k _ => (hpa (Work.C17.gIdx k)).mul (hDy (k : ℕ)))
    · exact DifferentiableOn.fun_sum
        (fun i _ => (hpa (Work.C17.iIdx i)).mul (hJd (Work.C17.jrev i)))
  have hAd : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ) := by
    rw [hA]
    exact hLHSd.const_mul κ
  have hGtd : DifferentiableOn ℂ Gt (Metric.ball (s : ℂ) δ) := by
    rw [hGt]
    refine DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_
    · refine ((differentiableOn_id.sub (differentiableOn_const (s:ℂ))).pow 3).mul ?_
      exact DifferentiableOn.fun_sum (fun b _ => (hpa (Work.C17.bIdx b)).mul (hFbd b))
    · exact DifferentiableOn.fun_sum (fun (k : Fin 4) _ =>
        (((differentiableOn_id.sub (differentiableOn_const (s:ℂ))).pow (3 - (k:ℕ))).mul
          (hpa (Work.C17.gIdx k))).mul (hGkd k))
    · exact DifferentiableOn.fun_sum (fun (i : Fin 6) _ =>
        (((differentiableOn_id.sub (differentiableOn_const (s:ℂ))).pow 2).mul
          (hpa (Work.C17.iIdx i))).mul (hHnd i))
  have hA0 : ∀ z ∈ Metric.ball (s : ℂ) δ, A z = 0 :=
    logcoeff_eq_zero_region hδ hs hρ hneV hAd hGtd (m := 3) hid
  intro z hz
  show LHS z = 0
  have h := hA0 z hz
  rw [hA] at h
  exact (mul_eq_zero.mp h).resolve_left hκ

end

end Work.C17I
