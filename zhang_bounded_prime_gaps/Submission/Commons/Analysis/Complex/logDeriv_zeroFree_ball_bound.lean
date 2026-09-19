import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Submission.Commons.Analysis.Complex.harmonicOnNhd_log_norm_sub

open Complex Metric Set Filter Function
open scoped Real Topology

namespace Commons.Analysis.Complex


lemma logPrimitiveOnBall {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hgne : ∀ w : ℂ, w ∈ Metric.ball c R → g w ≠ 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.ball c R) ∧
      (∀ w : ℂ, w ∈ Metric.ball c R → HasDerivAt F (deriv g w / g w) w) ∧
      (F c).re = Real.log ‖g c‖ ∧
      ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re = Real.log ‖g w‖ := by
  let h : ℂ → ℂ := deriv g / g
  have hcBall : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hgne_c : g c ≠ 0 := hgne c hcBall
  have hgDiffOn : DifferentiableOn ℂ g (Metric.ball c R) := hg.differentiableOn
  have hdgDiffOn : DifferentiableOn ℂ (deriv g) (Metric.ball c R) := hg.deriv.differentiableOn
  have hhDiffOn : DifferentiableOn ℂ h (Metric.ball c R) := by
    simpa [h] using (DifferentiableOn.div hdgDiffOn hgDiffOn hgne)
  have hexact : IsExactOn h (Metric.ball c R) := hhDiffOn.isExactOn_ball
  obtain ⟨F, hFc, hFh⟩ := hexact.with_val_at c (Real.log ‖g c‖ : ℂ)
  let q : ℂ → ℂ := (fun z : ℂ => cexp (F z)) / g
  have hFc_re : (F c).re = Real.log ‖g c‖ := by simp [hFc]
  have hq0 : ∀ x : ℂ, x ∈ Metric.ball c R → HasDerivAt q 0 x := by
    intro x hx
    have hF : HasDerivAt F (deriv g x / g x) x := by simpa [h] using hFh x hx
    have hFexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x := by
      exact (hF.cexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x)
    have hg' : HasDerivAt g (deriv g x) x := (hg x).hasDerivAt
    have hqder := hFexp.div hg' (hgne x hx)
    have hzero : ((cexp (F x) * (deriv g x / g x)) * g x - cexp (F x) * deriv g x) / g x ^ 2 = 0 := by
      have hnum : cexp (F x) * (deriv g x / g x) * g x - cexp (F x) * deriv g x = 0 := by
        field_simp [hgne x hx]
        ring
      rw [hnum, zero_div]
    have hq0x : HasDerivAt q 0 x := by
      simpa [q] using (hqder.congr_deriv hzero)
    exact hq0x
  have hqDiffOn : DifferentiableOn ℂ q (Metric.ball c R) := by
    intro x hx
    exact (hq0 x hx).differentiableAt.differentiableWithinAt
  have hqderiv0 : EqOn (deriv q) 0 (Metric.ball c R) := by
    intro x hx
    exact (hq0 x hx).deriv
  have hqconst : ∀ w : ℂ, w ∈ Metric.ball c R → q w = q c := fun w hw =>
    (Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hqDiffOn hqderiv0
      (x := w) (y := c) hw hcBall)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFh x hx).differentiableAt.differentiableWithinAt
  · intro w hw
    simpa [h] using hFh w hw
  · exact hFc_re
  · intro w hw
    have hqnorm : ‖q w‖ = ‖q c‖ := by rw [hqconst w hw]
    have hgwn : g w ≠ 0 := hgne w hw
    have hnc : ‖g c‖ ≠ 0 := norm_ne_zero_iff.mpr hgne_c
    have hnorm_expc : ‖cexp (F c)‖ = ‖g c‖ := by
      calc
        ‖cexp (F c)‖ = Real.exp ((F c).re) := Complex.norm_exp (F c)
        _ = ‖g c‖ := by
          rw [hFc_re, Real.exp_log]
          exact (norm_pos_iff.mpr hgne_c)
    have hratio : ‖cexp (F w)‖ / ‖g w‖ = 1 := by
      have hq' : ‖cexp (F w) / g w‖ = ‖cexp (F c) / g c‖ := by
        simpa [q] using hqnorm
      rw [norm_div, norm_div] at hq'
      calc
        ‖cexp (F w)‖ / ‖g w‖ = ‖cexp (F c)‖ / ‖g c‖ := hq'
        _ = 1 := by
          rw [hnorm_expc]
          exact div_self hnc
    have hnw : ‖g w‖ ≠ 0 := norm_ne_zero_iff.mpr hgwn
    have hnorm_expw : ‖cexp (F w)‖ = ‖g w‖ := by
      exact (div_eq_one_iff_eq hnw).mp hratio
    calc
      (F w).re = Real.log ‖cexp (F w)‖ := by
        rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖g w‖ := by rw [hnorm_expw]

lemma normSubLeOfReLeOnBall {F : ℂ → ℂ} {c w : ℂ} {R m M : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hMm : m ≤ M)
    (hF : DifferentiableOn ℂ F (Metric.ball c R))
    (hFle : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ Real.log M)
    (hFc : Real.log m ≤ (F c).re)
    (hw : w ∈ Metric.ball c R) :
    ‖F w - F c‖ ≤
      2 * (Real.log (2 * M) - Real.log m) * ‖w - c‖ / (R - ‖w - c‖) := by
  let T : ℂ → ℂ := fun ξ => c + ξ
  let G : ℂ → ℂ := F ∘ T - fun _ : ℂ => F c
  let M₁ : ℝ := Real.log (2 * M) - Real.log m
  have hMpos : 0 < M := lt_of_lt_of_le hm hMm
  have hm2M : m < 2 * M := by nlinarith
  have hM₁pos : 0 < M₁ := by
    dsimp [M₁]
    exact sub_pos.mpr (Real.log_lt_log hm hm2M)
  have hG0 : G 0 = 0 := by simp [G, T]
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) R) := by
    intro ζ hζ
    have hcζ : c + ζ ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hFζ : DifferentiableAt ℂ F (c + ζ) := (hF.differentiableAt (isOpen_ball.mem_nhds hcζ))
    have hT : HasDerivAt T 1 ζ := by
      simpa [T] using ((hasDerivAt_id ζ).const_add c)
    have hcomp : HasDerivAt (F ∘ T) (deriv F (c + ζ)) ζ := by
      simpa [Function.comp_apply] using ((hFζ.hasDerivAt).comp ζ hT)
    have hGat : HasDerivAt G (deriv F (c + ζ)) ζ := by
      convert hcomp.sub_const (F c) using 1 <;> rfl
    exact hGat.differentiableAt.differentiableWithinAt
  have hGle : ∀ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) R → (G ζ).re ≤ M₁ := by
    intro ζ hζ
    have hcζ : c + ζ ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have h1 : (F (c + ζ)).re - (F c).re ≤ Real.log M - Real.log m := by
      have hle1 : (F (c + ζ)).re ≤ Real.log M := hFle (c + ζ) hcζ
      linarith
    have h2 : Real.log M - Real.log m ≤ M₁ := by
      dsimp [M₁]
      have hlog2 : Real.log M ≤ Real.log (2 * M) :=
        Real.log_le_log hMpos (by nlinarith)
      linarith
    have hsimp : (G ζ).re = (F (c + ζ)).re - (F c).re := by simp [G, T]
    rw [hsimp]
    exact le_trans h1 h2
  have hwz : w - c ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory_zero (M := M₁) hM₁pos hGdiff hGle hR hwz hG0
  have hGsimp : ‖G (w - c)‖ = ‖F w - F c‖ := by simp [G, T]
  rwa [hGsimp] at hb

lemma logDerivBoundOfReLeOnBall {F : ℂ → ℂ} {c z₀ : ℂ} {R m M ρ : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hMm : m ≤ M)
    (hF : DifferentiableOn ℂ F (Metric.ball c R))
    (hFle : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ Real.log M)
    (hFc : Real.log m ≤ (F c).re)
    (hz₀ : z₀ ∈ Metric.ball c R) (hρ : 0 < ρ) (hρR : ρ < R - ‖z₀ - c‖) :
    ‖deriv F z₀‖ ≤
      2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) / ((R - ‖z₀ - c‖ - ρ) * ρ) := by
  let M₁ : ℝ := Real.log (2 * M) - Real.log m
  let s : ℝ := ‖z₀ - c‖
  let C : ℝ := 2 * M₁ * (s + ρ) / (R - s - ρ)
  have hM₁pos : 0 < M₁ := by
    dsimp [M₁]
    have hm2M : m < 2 * M := by nlinarith
    exact sub_pos.mpr (Real.log_lt_log hm hm2M)
  have hz0 : ‖z₀ - c‖ = s := rfl
  have hRsub : 0 < R - s - ρ := by
    dsimp [s]
    linarith [hρR]
  have hclosed : Metric.closedBall z₀ ρ ⊆ Metric.ball c R := by
    intro x hx
    have hxρ : ‖x - z₀‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hxR : ‖x - c‖ < R := by
      have htri : ‖x - c‖ ≤ ‖x - z₀‖ + ‖z₀ - c‖ := by
        simpa [sub_add_sub_cancel] using (norm_add_le (x - z₀) (z₀ - c))
      dsimp [s] at hz0
      nlinarith [htri, hxρ, hz0, hρR]
    simpa [Metric.mem_ball, dist_eq_norm] using hxR
  have hFclosedDiff : DifferentiableOn ℂ (fun w : ℂ => F w - F c) (Metric.closedBall z₀ ρ) := by
    intro x hx
    have hxR : x ∈ Metric.ball c R := hclosed hx
    have hFdx : DifferentiableAt ℂ F x := (hF.differentiableAt (isOpen_ball.mem_nhds hxR))
    exact (hFdx.sub_const (F c)).differentiableWithinAt
  have hfDiffCl : DiffContOnCl ℂ (fun w : ℂ => F w - F c) (Metric.ball z₀ ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    simpa [closure_ball z₀ (ne_of_gt hρ)] using hFclosedDiff
  have hB : ∀ w : ℂ, w ∈ Metric.sphere z₀ ρ → ‖F w - F c‖ ≤ C := by
    intro w hw
    have hwρ : ‖w - z₀‖ = ρ := by simpa [Metric.sphere, dist_eq_norm] using hw
    have hwball : w ∈ Metric.ball c R := hclosed (by
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [hwρ])
    have hb1 := normSubLeOfReLeOnBall (F := F) (c := c) (w := w) hR hm hMm hF hFle hFc hwball
    have hwcs : ‖w - c‖ ≤ s + ρ := by
      have htri : ‖w - c‖ ≤ ‖w - z₀‖ + ‖z₀ - c‖ := by
        simpa [sub_add_sub_cancel] using (norm_add_le (w - z₀) (z₀ - c))
      nlinarith [htri, hwρ, hz0]
    have hdenpos : 0 < R - ‖w - c‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hwball
      exact sub_pos.mpr hwball
    have hfrac : ‖w - c‖ / (R - ‖w - c‖) ≤ (s + ρ) / (R - s - ρ) := by
      rw [div_le_div_iff₀ hdenpos hRsub]
      have hneg : ‖w - c‖ - s - ρ ≤ 0 := by linarith
      have hprod : (‖w - c‖ - s - ρ) * R ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg hR.le
      nlinarith [hprod]
    calc
      ‖F w - F c‖ ≤ 2 * M₁ * ‖w - c‖ / (R - ‖w - c‖) := by
        simpa [M₁] using hb1
      _ = 2 * M₁ * (‖w - c‖ / (R - ‖w - c‖)) := by ring
      _ ≤ 2 * M₁ * ((s + ρ) / (R - s - ρ)) := by
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * M₁ * (s + ρ) / (R - s - ρ) := by ring
      _ = C := by rfl
  have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => F w - F c)
    (c := z₀) (R := ρ) hρ hfDiffCl hB
  have hfder : deriv (fun w : ℂ => F w - F c) z₀ = deriv F z₀ := by
    have hFdz : DifferentiableAt ℂ F z₀ := hF.differentiableAt (isOpen_ball.mem_nhds hz₀)
    calc
      deriv (fun w : ℂ => F w - F c) z₀
          = deriv ((fun w : ℂ => F w) - (fun _ : ℂ => F c)) z₀ := by rfl
      _ = deriv F z₀ - deriv (fun _ : ℂ => F c) z₀ := by
          exact deriv_sub (f := fun w : ℂ => F w) (g := fun _ : ℂ => F c) hFdz
            (differentiableAt_const (F c))
      _ = deriv F z₀ := by simp
  rw [hfder] at hCau
  calc
    ‖deriv F z₀‖ ≤ C / ρ := hCau
    _ = 2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) / ((R - ‖z₀ - c‖ - ρ) * ρ) := by
      dsimp [C, M₁, s]
      have hρ0 : ρ ≠ 0 := ne_of_gt hρ
      have hR0 : R - ‖z₀ - c‖ - ρ ≠ 0 := by
        exact ne_of_gt (by simpa [s] using hRsub)
      field_simp [hρ0, hR0]

theorem logDeriv_zeroFree_ball_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ}
    {R m M : ℝ} (hR : 0 < R) (hm : 0 < m) (hMm : m ≤ M)
    (hgne : ∀ w : ℂ, w ∈ Metric.ball c R → g w ≠ 0)
    (hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖g w‖ ≤ M)
    (hgm : m ≤ ‖g c‖) :
    ∀ ⦃z₀ : ℂ⦄, z₀ ∈ Metric.ball c R → ∀ ρ : ℝ, 0 < ρ → ρ < R - ‖z₀ - c‖ →
      ‖deriv g z₀ / g z₀‖ ≤
        2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) /
          ((R - ‖z₀ - c‖ - ρ) * ρ) := by
  intro z₀ hz₀ ρ hρ hρR
  rcases logPrimitiveOnBall hg hR hgne with ⟨F, hFdiff, hFh, hFc_re, hFre⟩
  have hFle : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ Real.log M := by
    intro w hw
    rw [hFre w hw]
    exact Real.log_le_log (norm_pos_iff.mpr (hgne w hw)) (hgM w hw)
  have hFc : Real.log m ≤ (F c).re := by
    rw [hFc_re]
    exact Real.log_le_log hm hgm
  have hb := logDerivBoundOfReLeOnBall (F := F) (z₀ := z₀) (ρ := ρ) hR hm hMm hFdiff hFle hFc hz₀ hρ hρR
  have hzF : deriv F z₀ = deriv g z₀ / g z₀ := (hFh z₀ hz₀).deriv
  calc
    ‖deriv g z₀ / g z₀‖ = ‖deriv F z₀‖ := by rw [hzF]
    _ ≤ 2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - c‖ + ρ) /
          ((R - ‖z₀ - c‖ - ρ) * ρ) := hb


end Commons.Analysis.Complex