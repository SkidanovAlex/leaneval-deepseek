import Mathlib
import Submission.Commons.Analysis.ODE.exists_linearODE_solution_continuousOn
import Submission.Commons.Analysis.ODE.solution_close_of_lipschitz
import Submission.Commons.Analysis.ODE.dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le

namespace Commons.Analysis.ODE

set_option autoImplicit false

open Set Metric Filter
open scoped NNReal

/-- **Existence on a closed interval in a fixed tube (strict case).**

Let `H : ℝ → E → E` be a time-dependent field with `H t 0 = 0`, `K`-Lipschitz in its second
argument on the closed ball of radius `r` (uniformly in `t`) and jointly continuous at the points
`(t, w)` with `‖w‖ < r`.  Let `a < b`, `c₀ ≥ 0` and suppose `c₀ * exp (K (t - a)) < r` for all
`t ∈ [a,b]`.  Then for every `w₀` with `‖w₀‖ ≤ c₀` there is a solution of `w' = H t w` on the
closed interval `[a,b]` with `w a = w₀`, satisfying the Grönwall bound
`‖w t‖ ≤ c₀ * exp (K * (t - a))`. -/
theorem exists_solution_Icc_of_lipschitz_ball_strict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : ℝ → E → E} {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hH0 : ∀ t, H t 0 = 0)
    (hH_lip : ∀ t, ∀ w w' : E, ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖H t w - H t w'‖ ≤ K * ‖w - w'‖)
    (hH_cont : ∀ t, ∀ w : E, ‖w‖ < r → ContinuousAt (Function.uncurry H) (t, w))
    {a b c₀ : ℝ} (hab : a < b) (hc₀ : 0 ≤ c₀)
    (henv : ∀ t ∈ Set.Icc a b, c₀ * Real.exp (K * (t - a)) < r)
    {w₀ : E} (hw₀ : ‖w₀‖ ≤ c₀) :
    ∃ w : ℝ → E, w a = w₀ ∧ (∀ t ∈ Set.Icc a b, HasDerivAt w (H t (w t)) t) ∧
      (∀ t ∈ Set.Icc a b, ‖w t‖ ≤ c₀ * Real.exp (K * (t - a))) := by
  classical
  have hExpb : c₀ * Real.exp (K * (b - a)) < r := henv b ⟨le_of_lt hab, le_refl b⟩
  -- The radius of the ball on which `H` is truncated.
  set r' : ℝ := (c₀ * Real.exp (K * (b - a)) + r) / 2 with hr'def
  have hr'pos : 0 < r' := by
    rw [hr'def]
    have h1 : 0 ≤ c₀ * Real.exp (K * (b - a)) := mul_nonneg hc₀ (Real.exp_pos _).le
    linarith
  have hr'nonneg : 0 ≤ r' := le_of_lt hr'pos
  have hr'lt : r' < r := by rw [hr'def]; linarith
  -- The radial retraction does not increase the norm.
  have hRd : ∀ x : E, ‖radialRetract r' x‖ ≤ ‖x‖ := by
    intro x
    by_cases h : ‖x‖ ≤ r'
    · rw [radialRetract, if_pos h]
    · rw [radialRetract, if_neg h, norm_smul,
        Real.norm_of_nonneg (div_nonneg hr'nonneg (norm_nonneg x))]
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hr'nonneg (lt_of_not_ge h)
      rw [div_mul_cancel₀ r' (ne_of_gt hxpos)]
      exact le_of_lt (lt_of_not_ge h)
  -- The truncated field.
  let Ht : ℝ → E → E := fun (t : ℝ) (x : E) => H t (radialRetract r' x)
  have hRetract_lip : LipschitzWith (2 : ℝ≥0) (radialRetract r' : E → E) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simpa using dist_radialRetract_le hr'nonneg x y
  have hRetract_cont : Continuous (radialRetract r' : E → E) := hRetract_lip.continuous
  -- Joint continuity of the truncated field.
  have hHt_contAt : ∀ p : ℝ × E, ContinuousAt (Function.uncurry Ht) p := by
    rintro ⟨t, x⟩
    have hRnorm : ‖radialRetract r' x‖ < r :=
      lt_of_le_of_lt (norm_radialRetract_le hr'nonneg x) hr'lt
    have h1 : ContinuousAt (Function.uncurry H) (t, radialRetract r' x) := hH_cont t _ hRnorm
    have h2 : ContinuousAt (fun p : ℝ × E => (p.1, radialRetract r' p.2)) (t, x) :=
      continuousAt_fst.prodMk (hRetract_cont.continuousAt.comp continuousAt_snd)
    have hfun : Function.uncurry Ht = Function.uncurry H ∘
        (fun p : ℝ × E => (p.1, radialRetract r' p.2)) := by
      funext p
      rcases p with ⟨t', x'⟩
      rfl
    rw [hfun]
    exact ContinuousAt.comp (f := fun p : ℝ × E => (p.1, radialRetract r' p.2)) h1 h2
  have hHt_cont : Continuous (Function.uncurry Ht) := continuous_iff_continuousAt.mpr hHt_contAt
  -- Global Lipschitz bound for the truncated field, and the bound `‖H̃‖ ≤ K ‖x‖`.
  have hHt_lip : ∀ t, LipschitzWith (⟨2 * K, by linarith⟩ : ℝ≥0) (Ht t) := by
    intro t
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    have hxr : ‖radialRetract r' x‖ ≤ r :=
      le_of_lt (lt_of_le_of_lt (norm_radialRetract_le hr'nonneg x) hr'lt)
    have hyr : ‖radialRetract r' y‖ ≤ r :=
      le_of_lt (lt_of_le_of_lt (norm_radialRetract_le hr'nonneg y) hr'lt)
    have h1 := hH_lip t (radialRetract r' x) (radialRetract r' y) hxr hyr
    have h2 : ‖radialRetract r' x - radialRetract r' y‖ ≤ 2 * ‖x - y‖ := by
      have h := dist_radialRetract_le hr'nonneg x y
      rwa [dist_eq_norm, dist_eq_norm] at h
    change ‖H t (radialRetract r' x) - H t (radialRetract r' y)‖ ≤ 2 * K * ‖x - y‖
    calc ‖H t (radialRetract r' x) - H t (radialRetract r' y)‖
        ≤ K * ‖radialRetract r' x - radialRetract r' y‖ := h1
      _ ≤ K * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 hK
      _ = 2 * K * ‖x - y‖ := by ring
  have hFieldBound : ∀ (s : ℝ) (x : E), ‖Ht s x‖ ≤ K * ‖x‖ := by
    intro s x
    have hrx : ‖radialRetract r' x‖ ≤ r :=
      le_of_lt (lt_of_le_of_lt (norm_radialRetract_le hr'nonneg x) hr'lt)
    have h0r : ‖(0 : E)‖ ≤ r := by rw [norm_zero]; exact hr.le
    have h1 := hH_lip s (radialRetract r' x) 0 hrx h0r
    rw [hH0 s, sub_zero, sub_zero] at h1
    change ‖H s (radialRetract r' x)‖ ≤ K * ‖x‖
    calc ‖H s (radialRetract r' x)‖ ≤ K * ‖radialRetract r' x‖ := h1
      _ ≤ K * ‖x‖ := mul_le_mul_of_nonneg_left (hRd x) hK
  -- Existence on a slightly larger window for the truncated field.
  have hle : a - 1 ≤ b + 1 := by linarith
  have hamem : a ∈ Set.Icc (a - 1) (b + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨y, hy0, _hycont, hyderiv, _hyint⟩ :=
    exists_solution_Icc_of_continuousOn_of_lipschitzWith (f := Ht) (a := a - 1) (b := b + 1)
      (K := ⟨2 * K, by linarith⟩) (t₀ := a) hle hamem w₀ hHt_cont.continuousOn
      (fun t _ => hHt_lip t)
  -- The Grönwall bound.
  have hExpmono : ∀ t ∈ Set.Icc a b,
      c₀ * Real.exp (K * (t - a)) ≤ c₀ * Real.exp (K * (b - a)) := by
    intro t ht
    apply mul_le_mul_of_nonneg_left _ hc₀
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hK
    linarith [ht.2]
  have hlt_r' : ∀ t ∈ Set.Icc a b, c₀ * Real.exp (K * (t - a)) < r' := by
    intro t ht
    have h1 := hExpmono t ht
    rw [hr'def]
    linarith [hExpb]
  have hBound : ∀ t ∈ Set.Icc a b, ‖y t‖ ≤ c₀ * Real.exp (K * (t - a)) := by
    intro t ht
    have hyderiv' : ∀ s ∈ Set.Icc a t, HasDerivAt y (Ht s (y s)) s := by
      intro s hs
      exact hyderiv s ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
    have h0deriv : ∀ s ∈ Set.Icc a t, HasDerivAt (fun _ : ℝ => (0 : E)) 0 s :=
      fun s _ => hasDerivAt_const s 0
    have hxy : ∀ s ∈ Set.Icc a t, ‖Ht s (y s) - 0‖ ≤ K * ‖y s - 0‖ := by
      intro s _
      rw [sub_zero, sub_zero]
      exact hFieldBound s (y s)
    have h := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le (x := y)
      (y := fun _ : ℝ => (0 : E)) (x' := fun s => Ht s (y s)) (y' := fun _ => 0)
      ht.1 hK hyderiv' h0deriv hxy
    have h' : ‖y t‖ ≤ ‖y a‖ * Real.exp (K * (t - a)) := by
      simpa [dist_eq_norm] using h
    calc ‖y t‖ ≤ ‖y a‖ * Real.exp (K * (t - a)) := h'
      _ = ‖w₀‖ * Real.exp (K * (t - a)) := by rw [hy0]
      _ ≤ c₀ * Real.exp (K * (t - a)) :=
            mul_le_mul_of_nonneg_right hw₀ (Real.exp_pos _).le
  refine ⟨y, hy0, ?_, hBound⟩
  intro t ht
  have hmem : t ∈ Set.Ioo (a - 1) (b + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := hyderiv t hmem
  have hlt : ‖y t‖ < r' := lt_of_le_of_lt (hBound t ht) (hlt_r' t ht)
  have hret : radialRetract r' (y t) = y t := radialRetract_eq_self (y t) (le_of_lt hlt)
  have hEq : Ht t (y t) = H t (y t) := by simp only [Ht, hret]
  rwa [hEq] at hd

end Commons.Analysis.ODE
