import Mathlib
import Submission.Work.Drive.exists_cInf_angle_lift

/-!
# Angle lift of a positively oriented circle that meets the ray `(1,0)` only once

Given a `C^∞` unit vector field `(a,b)` (`a² + b² = 1`), `(a,b)(0) = (1,0)`, `period`-periodic,
whose angular velocity `a b' - b a'` is everywhere positive, and which returns to `(1,0)` only at
parameters `≡ 0` mod `period` (the "single ray" hypothesis), there is a `C^∞` angle lift `ψ`, i.e.
`a = cos ∘ ψ`, `b = sin ∘ ψ`, `ψ 0 = 0` and `ψ (t + period) = ψ t + period`.

The point is that positiveness of the angular velocity makes `ψ` strictly increasing on one period,
so the shift `ψ period` is positive; `(cos, sin) ∘ ψ = (a,b)` gives `cos (ψ period) = 1`, hence
`ψ period = 2πk` with `k ≥ 1`; the intermediate value theorem produces `t₂ ∈ [0, period]` with
`ψ t₂ = period`, which is `(a,b)(t₂) = (1,0)`; the single-ray hypothesis forces `t₂ = period` and
therefore `k = 1`, i.e. `ψ period = period`.  Periodicity of `ψ` then follows by constancy of the
difference `t ↦ ψ (t + period) - ψ t`, whose derivative is the (periodic) angular velocity minus
itself.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

theorem angleLift_singleRay {a b : ℝ → ℝ} (ha : ContDiff ℝ Work.Drive.cInfT a) (hb : ContDiff ℝ Work.Drive.cInfT b)
    (hnorm : ∀ t : ℝ, a t ^ 2 + b t ^ 2 = 1)
    (h0 : a 0 = 1 ∧ b 0 = 0)
    (hper : ∀ t : ℝ, a (t + LeanEval.KnotTheory.Quadrisecant.period) = a t ∧ b (t + LeanEval.KnotTheory.Quadrisecant.period) = b t)
    (hsingle : ∀ t : ℝ, 0 < t → t < LeanEval.KnotTheory.Quadrisecant.period → ¬ (a t = 1 ∧ b t = 0))
    (hpos : ∀ t : ℝ, 0 < a t * deriv b t - b t * deriv a t) :
    ∃ psi : ℝ → ℝ, ContDiff ℝ Work.Drive.cInfT psi ∧ psi 0 = 0 ∧
      (∀ t : ℝ, psi (t + LeanEval.KnotTheory.Quadrisecant.period) = psi t + LeanEval.KnotTheory.Quadrisecant.period) ∧
      (∀ t : ℝ, a t = Real.cos (psi t) ∧ b t = Real.sin (psi t)) := by
  have hper_pos : 0 < period := by rw [period]; positivity
  -- the angular velocity and its primitive
  have hda : Continuous (deriv a) := ha.continuous_deriv one_le_cInfT
  have hdb : Continuous (deriv b) := hb.continuous_deriv one_le_cInfT
  set f : ℝ → ℝ := fun t => a t * deriv b t - b t * deriv a t with hf_def
  have hf_cont : Continuous f := by
    rw [hf_def]
    exact (ha.continuous.mul hdb).sub (hb.continuous.mul hda)
  have hpos' : ∀ x : ℝ, 0 < f x := fun x => by rw [hf_def]; exact hpos x
  let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s
  have hψ_has : ∀ t, HasDerivAt ψ (f t) t := by
    intro t
    simpa [ψ] using (hf_cont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hψ_deriv : ∀ t, deriv ψ t = f t := by
    intro t
    simpa [ψ] using Continuous.deriv_integral f hf_cont 0 t
  have hψ_has' : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t => by
    rw [hψ_deriv t]; exact hψ_has t
  have hψ_diff : Differentiable ℝ ψ := fun t => (hψ_has t).differentiableAt
  have hψ_zero : ψ 0 = 0 := by simp [ψ]
  have hψ_cont : Continuous ψ := hψ_diff.continuous
  have hderiv_a : ContDiff ℝ cInfT (deriv a) :=
    (contDiff_infty_iff_deriv.mp ha).2
  have hderiv_b : ContDiff ℝ cInfT (deriv b) :=
    (contDiff_infty_iff_deriv.mp hb).2
  have hf_Cinf : ContDiff ℝ cInfT f := by
    rw [hf_def]
    exact (ha.mul hderiv_b).sub (hb.mul hderiv_a)
  have hψ_Cinf : ContDiff ℝ cInfT ψ := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨hψ_diff, ?_⟩
    rw [show deriv ψ = f from funext hψ_deriv]
    exact hf_Cinf
  have hpsi_eq : ∀ t, deriv ψ t = a t * deriv b t - b t * deriv a t := by
    intro t; rw [hψ_deriv t, hf_def]
  -- differentiating the unit-norm relation
  have horth : ∀ t : ℝ, a t * deriv a t + b t * deriv b t = 0 := by
    intro t
    have hda_t : HasDerivAt a (deriv a t) t := (ha.differentiable cInfT_ne_zero t).hasDerivAt
    have hdb_t : HasDerivAt b (deriv b t) t := (hb.differentiable cInfT_ne_zero t).hasDerivAt
    have hd : HasDerivAt (a ^ 2 + b ^ 2) (2 * a t * deriv a t + 2 * b t * deriv b t) t := by
      have h1 : HasDerivAt (a ^ 2) (2 * a t * deriv a t) t := by simpa using hda_t.pow 2
      have h2 : HasDerivAt (b ^ 2) (2 * b t * deriv b t) t := by simpa using hdb_t.pow 2
      simpa using h1.add h2
    have hc : HasDerivAt (a ^ 2 + b ^ 2) 0 t := by
      have huniq : (a ^ 2 + b ^ 2 : ℝ → ℝ) = fun _ => (1 : ℝ) := funext fun s => hnorm s
      rw [huniq]
      exact hasDerivAt_const t 1
    have := hd.unique hc
    linarith
  -- the two constant scalar functions realising the rotation
  let P : ℝ → ℝ := fun s => a s * Real.cos (ψ s) + b s * Real.sin (ψ s)
  let Q : ℝ → ℝ := fun s => b s * Real.cos (ψ s) - a s * Real.sin (ψ s)
  have hP_deriv : ∀ t, deriv P t = 0 := by
    intro t
    have ha_t : HasDerivAt a (deriv a t) t := (ha.differentiable cInfT_ne_zero t).hasDerivAt
    have hb_t : HasDerivAt b (deriv b t) t := (hb.differentiable cInfT_ne_zero t).hasDerivAt
    simpa [P] using
      deriv_cos_sin_add_eq_zero ha_t hb_t (hψ_has' t) (hnorm t) (horth t) (hpsi_eq t)
  have hQ_deriv : ∀ t, deriv Q t = 0 := by
    intro t
    have ha_t : HasDerivAt a (deriv a t) t := (ha.differentiable cInfT_ne_zero t).hasDerivAt
    have hb_t : HasDerivAt b (deriv b t) t := (hb.differentiable cInfT_ne_zero t).hasDerivAt
    simpa [Q] using
      deriv_cos_sin_sub_eq_zero ha_t hb_t (hψ_has' t) (hnorm t) (horth t) (hpsi_eq t)
  have hP_diff : Differentiable ℝ P := by
    have ha_d : Differentiable ℝ a := ha.differentiable cInfT_ne_zero
    have hb_d : Differentiable ℝ b := hb.differentiable cInfT_ne_zero
    intro t
    show DifferentiableAt ℝ (fun s => a s * Real.cos (ψ s) + b s * Real.sin (ψ s)) t
    fun_prop
  have hQ_diff : Differentiable ℝ Q := by
    have ha_d : Differentiable ℝ a := ha.differentiable cInfT_ne_zero
    have hb_d : Differentiable ℝ b := hb.differentiable cInfT_ne_zero
    intro t
    show DifferentiableAt ℝ (fun s => b s * Real.cos (ψ s) - a s * Real.sin (ψ s)) t
    fun_prop
  have hP_one : ∀ t, P t = 1 := by
    intro t
    have h := is_const_of_deriv_eq_zero hP_diff hP_deriv t 0
    rw [h]
    simp [P, hψ_zero, h0.1, h0.2]
  have hQ_zero : ∀ t, Q t = 0 := by
    intro t
    have h := is_const_of_deriv_eq_zero hQ_diff hQ_deriv t 0
    rw [h]
    simp [Q, hψ_zero, h0.1, h0.2]
  -- the lift identities
  have hcos : ∀ t, Real.cos (ψ t) = a t := by
    intro t
    have key : Real.cos (ψ t) = a t * P t + b t * Q t := by
      show Real.cos (ψ t) = a t * (a t * Real.cos (ψ t) + b t * Real.sin (ψ t)) +
        b t * (b t * Real.cos (ψ t) - a t * Real.sin (ψ t))
      linear_combination - Real.cos (ψ t) * hnorm t
    rw [hP_one t, hQ_zero t] at key
    simpa using key
  have hsin : ∀ t, Real.sin (ψ t) = b t := by
    intro t
    have key : Real.sin (ψ t) = b t * P t - a t * Q t := by
      show Real.sin (ψ t) = b t * (a t * Real.cos (ψ t) + b t * Real.sin (ψ t)) -
        a t * (b t * Real.cos (ψ t) - a t * Real.sin (ψ t))
      linear_combination - Real.sin (ψ t) * hnorm t
    rw [hP_one t, hQ_zero t] at key
    simpa using key
  -- the integrand is periodic, so the primitive has the required shift
  have hda_per : ∀ t, deriv a (t + period) = deriv a t := by
    intro t
    have hEq : (fun s : ℝ => a (s + period)) = fun s => a s := funext fun s => (hper s).1
    have h := congrArg (fun g : ℝ → ℝ => deriv g t) hEq
    simpa [deriv_comp_add_const] using h
  have hdb_per : ∀ t, deriv b (t + period) = deriv b t := by
    intro t
    have hEq : (fun s : ℝ => b (s + period)) = fun s => b s := funext fun s => (hper s).2
    have h := congrArg (fun g : ℝ → ℝ => deriv g t) hEq
    simpa [deriv_comp_add_const] using h
  have hf_per : Function.Periodic f period := by
    intro t
    simp only [hf_def]
    rw [hda_per t, hdb_per t, (hper t).1, (hper t).2]
  have hψ_add : ∀ t, ψ (t + period) = ψ t + ψ period := by
    intro t
    have h_int : ∀ t₁ t₂ : ℝ, IntervalIntegrable f (MeasureTheory.volume) t₁ t₂ :=
      fun t₁ t₂ => hf_cont.intervalIntegrable t₁ t₂
    have := hf_per.intervalIntegral_add_eq_add 0 t h_int
    simpa [ψ, zero_add] using this
  -- the shift over one period is a positive integer multiple of `2π`
  have hψ_pos : 0 < ψ period := by
    have := intervalIntegral.integral_pos hper_pos hf_cont.continuousOn
      (fun x _ => le_of_lt (hpos' x)) ⟨0, ⟨le_refl 0, hper_pos.le⟩, hpos' 0⟩
    simpa [ψ] using this
  have hcos_per : Real.cos (ψ period) = 1 := by
    have hp0 : a period = a 0 := by simpa using (hper 0).1
    rw [hcos period, hp0, h0.1]
  obtain ⟨k, hk0⟩ := (Real.cos_eq_one_iff (ψ period)).1 hcos_per
  have hk : (k : ℝ) * period = ψ period := by simpa [period] using hk0
  have hk_pos : 0 < k := by
    have h1 : (0 : ℝ) < (k : ℝ) := by
      have := hψ_pos
      rw [← hk] at this
      nlinarith [hper_pos]
    exact_mod_cast h1
  have hk_ge : (1 : ℤ) ≤ k := by omega
  -- the intermediate value theorem forces the shift to be exactly one period
  have hIVT : ∃ t₂ ∈ Set.Icc (0 : ℝ) period, ψ t₂ = period := by
    have hmem : period ∈ Set.Icc (ψ 0) (ψ period) := by
      refine ⟨?_, ?_⟩
      · rw [hψ_zero]; exact hper_pos.le
      · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
        calc period = 1 * period := (one_mul period).symm
          _ ≤ (k : ℝ) * period := mul_le_mul_of_nonneg_right h1 hper_pos.le
          _ = ψ period := hk
    obtain ⟨t₂, ht₂, hψt₂⟩ := intermediate_value_Icc hper_pos.le hψ_cont.continuousOn hmem
    exact ⟨t₂, ht₂, hψt₂⟩
  have hk_eq_one : k = 1 := by
    obtain ⟨t₂, ht₂, hψt₂⟩ := hIVT
    obtain ⟨ht₂_0, ht₂_le⟩ := ht₂
    rcases lt_or_eq_of_le ht₂_le with hlt | heq
    · -- `t₂` is an interior second preimage of `(1,0)`, contradicting the single-ray hypothesis
      have ht₂_pos : 0 < t₂ := by
        rcases lt_or_eq_of_le ht₂_0 with h' | h'
        · exact h'
        · exfalso
          have hz : ψ t₂ = 0 := by rw [← h', hψ_zero]
          rw [hψt₂] at hz
          exact absurd hz (ne_of_gt hper_pos)
      have hab : a t₂ = 1 ∧ b t₂ = 0 := by
        refine ⟨?_, ?_⟩
        · rw [← hcos t₂, hψt₂,
            show Real.cos period = 1 from by rw [period]; exact Real.cos_two_pi]
        · rw [← hsin t₂, hψt₂,
            show Real.sin period = 0 from by rw [period]; exact Real.sin_two_pi]
      exact (hsingle t₂ ht₂_pos hlt hab).elim
    · have hψper : ψ period = period := by simpa [heq] using hψt₂
      have hk1 : (k : ℝ) * period = period := hk.trans hψper
      have : (k : ℝ) = 1 := mul_right_cancel₀ (ne_of_gt hper_pos) (by simpa using hk1)
      exact_mod_cast this
  have hψ_period : ψ period = period := by rw [← hk, hk_eq_one]; ring
  refine ⟨ψ, hψ_Cinf, hψ_zero, ?_, ?_⟩
  · intro t
    rw [hψ_add t, hψ_period]
  · intro t
    exact ⟨(hcos t).symm, (hsin t).symm⟩

end Work.Drive
