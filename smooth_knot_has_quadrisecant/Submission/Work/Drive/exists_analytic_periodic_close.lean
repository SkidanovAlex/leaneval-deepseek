import Mathlib
import Submission.Helpers
import Submission.Work.Drive.circleBandArc
import Submission.Work.Drive.trigFun
import Submission.Work.Drive.trigFun_contDiff
import Submission.Work.Drive.trigFun_periodic
import Submission.Work.Drive.trigFun_prim_zero
import Submission.Work.Drive.trigFun_hasDerivAt_prim
import Submission.Work.Drive.exists_trigFun_close_zeroMean

/-!
# Analytic periodic approximation of a `C¹` periodic curve

`Work.Drive.exists_analytic_periodic_close`: given a `C¹` `period`-periodic curve
`f : ℝ → Space` and `ε > 0` there is an **analytic** (`ContDiff ℝ ⊤`) `period`-periodic curve `g`
that is `C¹`-close to `f`: `‖f t - g t‖ < ε` and `‖velocity f t - velocity g t‖ < ε` for all `t`.

Route (trigonometric-polynomial approximation on the circle, with the primitive trick):
* the derivative `velocity f` is continuous and `period`-periodic with zero mean over a period;
* each coordinate of `velocity f` is uniformly approximated by a trigonometric sum
  `q : TrigFun ℝ` with vanishing constant coefficient (`Work.Drive.exists_trigFun_close_zeroMean`);
* assembling the three coordinates gives `Q : TrigFun Space` with `Q.c 0 = 0` and
  `‖Q.toFun t - velocity f t‖ < 2δ`;
* `g := fun t => f 0 + (TrigFun.prim Q).toFun t` is analytic and `period`-periodic, with
  `velocity g = Q.toFun` (the primitive trick) and `g t - f t = ∫₀ᵗ (Q.toFun - velocity f)`,
  bounded by `period * 2δ`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

open scoped Real

/-- For `T > 0` and `x : ℝ` there is an integer `n` with `x - n * T ∈ [0, T)`. -/
private lemma exists_int_sub_mul_mem_Ico {T x : ℝ} (hT : 0 < T) :
    ∃ n : ℤ, x - n * T ∈ Set.Ico 0 T := by
  have h2 : Int.fract (x / T) = x / T - (⌊x / T⌋ : ℝ) := (Int.self_sub_floor (x / T)).symm
  have h1 : x - (⌊x / T⌋ : ℝ) * T = T * Int.fract (x / T) := by rw [h2]; field_simp
  exact ⟨⌊x / T⌋, by
    rw [h1]
    exact ⟨mul_nonneg hT.le (Int.fract_nonneg _),
      calc T * Int.fract (x / T) < T * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one _) hT
        _ = T := mul_one T⟩⟩

/-- **Analytic periodic approximation of a `C¹` periodic curve in position and velocity.** -/
theorem exists_analytic_periodic_close {f : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f LeanEval.KnotTheory.Quadrisecant.period)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ ⊤ g ∧ Function.Periodic g LeanEval.KnotTheory.Quadrisecant.period ∧
        (∀ t : ℝ, ‖f t - g t‖ < ε) ∧
          (∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity f t -
            LeanEval.KnotTheory.Quadrisecant.velocity g t‖ < ε) := by
  have hT : 0 < period := period_pos
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hvel_cont : Continuous (velocity f) := by
    rw [show velocity f = deriv f from rfl]
    exact hf.continuous_deriv (le_refl (1 : WithTop ℕ∞))
  have hvel_per : Function.Periodic (velocity f) period := fun t => periodic_velocity hper hdiff t
  have hvel_int : IntervalIntegrable (velocity f) MeasureTheory.volume (0 : ℝ) period :=
    hvel_cont.intervalIntegrable _ _
  -- the approximation radius
  set δ : ℝ := ε / (4 * (period + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ2ε : 2 * δ < ε := by
    rw [hδ, mul_div_assoc' (2) ε (4 * (period + 1))]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hε, hT]
  have hδTε : period * (2 * δ) < ε := by
    rw [hδ, mul_div_assoc' (2) ε (4 * (period + 1)),
      mul_div_assoc' period (2 * ε) (4 * (period + 1))]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hε, hT]
  -- density in each coordinate of the velocity
  have hex : ∀ j : Fin 3, ∃ q : TrigFun ℝ, q.c 0 = 0 ∧
      ∀ t : ℝ, |q.toFun t - (velocity f t).ofLp j| < δ := by
    intro j
    have hcj : Continuous (fun t : ℝ => (velocity f t).ofLp j) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous.comp hvel_cont
    have hpj : Function.Periodic (fun t : ℝ => (velocity f t).ofLp j) period :=
      fun t => congrArg (fun v : Space => v.ofLp j) (hvel_per t)
    have hmeanj : ∫ t in (0 : ℝ)..period, (velocity f t).ofLp j = 0 := by
      have h1 : ∫ t in (0 : ℝ)..period, (velocity f t).ofLp j
          = (∫ t in (0 : ℝ)..period, velocity f t).ofLp j := by
        have := ContinuousLinearMap.intervalIntegral_comp_comm
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) (μ := MeasureTheory.volume) hvel_int
        simpa [PiLp.proj_apply] using this
      have h2 : ∫ t in (0 : ℝ)..period, velocity f t = f period - f 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hdiff x).hasDerivAt) hvel_int
      have hper0 : f period = f 0 := by simpa using hper 0
      rw [h1, h2, hper0, sub_self]
      simp
    exact exists_trigFun_close_zeroMean hcj hpj hmeanj hδpos
  choose q hq0 hqclose using hex
  -- the assembled `Space`-valued trigonometric sum (the three coordinates of the velocity)
  let e : Fin 3 → Space := fun j => EuclideanSpace.single j (1 : ℝ)
  let Q : TrigFun Space :=
    TrigFun.smulVec (q 0) (e 0) + (TrigFun.smulVec (q 1) (e 1) + TrigFun.smulVec (q 2) (e 2))
  have hQc : Q.c 0 = 0 := by
    simp [Q, TrigFun.smulVec, hq0]
  have hQfun : ∀ t : ℝ, Q.toFun t = (q 0).toFun t • e 0 +
      ((q 1).toFun t • e 1 + (q 2).toFun t • e 2) := by
    intro t
    simp [Q, TrigFun.toFun_add, TrigFun.toFun_smulVec]
  have hQcoord : ∀ (t : ℝ) (i : Fin 3), (Q.toFun t).ofLp i = (q i).toFun t := by
    intro t i
    fin_cases i <;> simp [hQfun t, e, PiLp.add_apply, PiLp.smul_apply]
  have hQbound : ∀ t : ℝ, ‖Q.toFun t - velocity f t‖ < 2 * δ := by
    intro t
    have hlt : ∀ j : Fin 3, ‖(Q.toFun t - velocity f t).ofLp j‖ ^ 2 < δ ^ 2 := by
      intro j
      have hcoord : (Q.toFun t - velocity f t).ofLp j
          = (q j).toFun t - (velocity f t).ofLp j := by
        rw [PiLp.sub_apply, hQcoord t j]
      rw [hcoord, Real.norm_eq_abs]
      exact pow_lt_pow_left₀ (hqclose j t) (abs_nonneg _) (by norm_num)
    have hsq : ‖Q.toFun t - velocity f t‖ ^ 2 < (2 * δ) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ j : Fin 3, ‖(Q.toFun t - velocity f t).ofLp j‖ ^ 2
          ≤ ∑ _j : Fin 3, δ ^ 2 := Finset.sum_le_sum fun j _ => le_of_lt (hlt j)
        _ = 3 * δ ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
        _ < (2 * δ) ^ 2 := by nlinarith [hδpos]
    have h := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * δ)] at h
  -- the primitive of `Q`: the analytic periodic candidate
  set g : ℝ → Space := fun t => f 0 + (TrigFun.prim Q).toFun t with hg
  have hgan : ContDiff ℝ ⊤ g := contDiff_const.add (trigFun_contDiff (TrigFun.prim Q))
  have hgper : Function.Periodic g period := by
    intro t
    have h := trigFun_periodic (TrigFun.prim Q) t
    simpa [g, period] using congrArg (fun z => f 0 + z) h
  have hgvel : ∀ t : ℝ, velocity g t = Q.toFun t := by
    intro t
    have hderiv : HasDerivAt (fun u : ℝ => f 0 + (TrigFun.prim Q).toFun u) (Q.toFun t) t :=
      (trigFun_hasDerivAt_prim Q hQc t).const_add (f 0)
    simpa [g, velocity] using hderiv.deriv
  have hgInt : ∀ s : ℝ, g s - f s = ∫ u in (0 : ℝ)..s, (Q.toFun u - velocity f u) := by
    intro s
    have h1 : (TrigFun.prim Q).toFun s = ∫ u in (0 : ℝ)..s, Q.toFun u := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := (TrigFun.prim Q).toFun) (f' := Q.toFun)
        (fun x _ => trigFun_hasDerivAt_prim Q hQc x)
        ((trigFun_contDiff Q).continuous.intervalIntegrable _ _)
      rw [trigFun_prim_zero, sub_zero] at h
      exact h.symm
    have h2 : f s = f 0 + ∫ u in (0 : ℝ)..s, velocity f u := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := f) (f' := velocity f) (fun x _ => (hdiff x).hasDerivAt)
        (hvel_cont.intervalIntegrable (0 : ℝ) s)
      rw [eq_sub_iff_add_eq, add_comm] at h
      exact h.symm
    have h3 : ∫ u in (0 : ℝ)..s, (Q.toFun u - velocity f u)
        = (∫ u in (0 : ℝ)..s, Q.toFun u) - (∫ u in (0 : ℝ)..s, velocity f u) :=
      intervalIntegral.integral_sub ((trigFun_contDiff Q).continuous.intervalIntegrable _ _)
        (hvel_cont.intervalIntegrable (0 : ℝ) s)
    simp only [g]
    rw [h1, h2, h3]
    abel
  have hgclose : ∀ t : ℝ, ‖f t - g t‖ < ε := by
    intro t
    obtain ⟨n, hn⟩ := exists_int_sub_mul_mem_Ico (T := period) hT (x := t)
    set t₀ : ℝ := t - (n : ℝ) * period with ht₀
    have ht : t = t₀ + (n : ℝ) * period := by rw [ht₀]; ring
    have hgt : g t = g t₀ := by
      rw [ht, show (n : ℝ) * period = n • period by rw [zsmul_eq_mul]]
      exact hgper.zsmul n t₀
    have hft : f t = f t₀ := by
      rw [ht, show (n : ℝ) * period = n • period by rw [zsmul_eq_mul]]
      exact hper.zsmul n t₀
    rw [hgt, hft, norm_sub_rev, hgInt t₀]
    calc ‖∫ u in (0 : ℝ)..t₀, (Q.toFun u - velocity f u)‖
        ≤ (2 * δ) * |t₀ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => le_of_lt (hQbound x)
      _ = (2 * δ) * t₀ := by rw [sub_zero, abs_of_nonneg hn.1]
      _ ≤ (2 * δ) * period :=
          mul_le_mul_of_nonneg_left hn.2.le (by linarith : (0 : ℝ) ≤ 2 * δ)
      _ = period * (2 * δ) := by ring
      _ < ε := hδTε
  refine ⟨g, hgan, hgper, hgclose, ?_⟩
  intro t
  rw [show velocity f t - velocity g t = -(Q.toFun t - velocity f t) by rw [hgvel t]; abel,
    norm_neg]
  exact lt_trans (hQbound t) hδ2ε

end Work.Drive
