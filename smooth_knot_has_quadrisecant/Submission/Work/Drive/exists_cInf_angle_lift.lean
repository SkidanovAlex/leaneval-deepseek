import Mathlib
import ChallengeDeps
import Submission.Work.Drive.framedCInfSlices

/-!
# Existence of a `C^∞` angle lift for a positively oriented embedded circle

Given two analytic `period`-periodic functions `a b : ℝ → ℝ` with `a² + b² = 1`,
`(a,b)(0) = (1,0)`, `(a,b)` injective on `[0, period)`, and positive angular
velocity `a b' - b a' > 0`, there is a `C¹` function `ψ` with `ψ 0 = 0`,
`ψ (t + period) = ψ t + period`, and `a = cos ∘ ψ`, `b = sin ∘ ψ`.

The proof is entirely elementary and avoids any degree theory: with
`f := a b' - b a'` (continuous, by `ContDiff ℝ ⊤ →` analytic derivative), the
candidate is the integral `ψ t = ∫_0^t f`.  Differentiating the two scalar
functions
`P t = a t cos (ψ t) + b t sin (ψ t)`, `Q t = b t cos (ψ t) - a t sin (ψ t)`
gives `P' = Q' = 0` — this uses only `a² + b² = 1`, `(a² + b²)' = 0`, and
`ψ' = a b' - b a'` — so `P ≡ P 0 = 1` and `Q ≡ Q 0 = 0`; the pair `(cos ∘ ψ,
sin ∘ ψ)` is then recovered from `P, Q` by inverting the rotation
`(cos, sin) ↦ (a cos + b sin, b cos - a sin)`.

The periodicity shift `ψ (t + period) = ψ t + ψ period` uses the standard
integral identity for periodic integrands.  Finally `cos (ψ period) = 1`
forces `ψ period = 2πk` with `k ∈ ℤ`; the integrand is strictly positive, so
`k ≥ 1`; the intermediate value theorem produces `t₂ ∈ [0, period]` with
`ψ t₂ = period`, and injectivity on `[0, period)` forces `t₂ = period` (else
`(a, b)(t₂) = (1,0) = (a,b)(0)`), whence `k = 1` and `ψ period = period`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The angle identity (sum form).**  If `(A,B)` is a unit vector
orthogonal to `(p,q)` and `Ψ = A q - B p`, then `p + B Ψ = 0`.  This is the
algebraic core of the derivative computation below. -/
lemma orth_angle_sum {A B p q Ψ : ℝ} (hnorm : A ^ 2 + B ^ 2 = 1)
    (horth : A * p + B * q = 0) (hpsi : Ψ = A * q - B * p) : p + B * Ψ = 0 := by
  rw [hpsi]
  linear_combination A * horth - p * hnorm

/-- **The angle identity (difference form).**  If `(A,B)` is a unit vector
orthogonal to `(p,q)` and `Ψ = A q - B p`, then `q - A Ψ = 0`. -/
lemma orth_angle_diff {A B p q Ψ : ℝ} (hnorm : A ^ 2 + B ^ 2 = 1)
    (horth : A * p + B * q = 0) (hpsi : Ψ = A * q - B * p) : q - A * Ψ = 0 := by
  rw [hpsi]
  linear_combination B * horth - q * hnorm

/-- **The rotated pair `(a cos ψ + b sin ψ)` is constant** when `(a,b)` is a
unit vector field, `(a, b) ⊥ (a', b')`, and `ψ' = a b' - b a'`: the
`(a,b)`-component of the rotated frame `((cos ∘ ψ, sin ∘ ψ))` has vanishing
derivative. -/
lemma deriv_cos_sin_add_eq_zero {a b ψ : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (deriv a t) t) (hb : HasDerivAt b (deriv b t) t)
    (hψ : HasDerivAt ψ (deriv ψ t) t)
    (hnorm : a t ^ 2 + b t ^ 2 = 1) (horth : a t * deriv a t + b t * deriv b t = 0)
    (hpsi : deriv ψ t = a t * deriv b t - b t * deriv a t) :
    deriv (fun s => a s * Real.cos (ψ s) + b s * Real.sin (ψ s)) t = 0 := by
  have h1 := ha.mul ((Real.hasDerivAt_cos (ψ t)).comp t hψ)
  have h2 := hb.mul ((Real.hasDerivAt_sin (ψ t)).comp t hψ)
  have h : deriv (fun s => a s * Real.cos (ψ s) + b s * Real.sin (ψ s)) t =
      deriv a t * Real.cos (ψ t) + a t * (-Real.sin (ψ t) * deriv ψ t) +
        (deriv b t * Real.sin (ψ t) + b t * (Real.cos (ψ t) * deriv ψ t)) :=
    (h1.add h2).deriv
  rw [h]
  have hp : deriv a t + b t * deriv ψ t = 0 := orth_angle_sum hnorm horth hpsi
  have hq : deriv b t - a t * deriv ψ t = 0 := orth_angle_diff hnorm horth hpsi
  linear_combination Real.cos (ψ t) * hp + Real.sin (ψ t) * hq

/-- **The rotated pair `(b cos ψ - a sin ψ)` is constant** under the same
hypotheses: the `(b,-a)`-component of the rotated frame has vanishing
derivative. -/
lemma deriv_cos_sin_sub_eq_zero {a b ψ : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (deriv a t) t) (hb : HasDerivAt b (deriv b t) t)
    (hψ : HasDerivAt ψ (deriv ψ t) t)
    (hnorm : a t ^ 2 + b t ^ 2 = 1) (horth : a t * deriv a t + b t * deriv b t = 0)
    (hpsi : deriv ψ t = a t * deriv b t - b t * deriv a t) :
    deriv (fun s => b s * Real.cos (ψ s) - a s * Real.sin (ψ s)) t = 0 := by
  have h1 := hb.mul ((Real.hasDerivAt_cos (ψ t)).comp t hψ)
  have h2 := ha.mul ((Real.hasDerivAt_sin (ψ t)).comp t hψ)
  have h : deriv (fun s => b s * Real.cos (ψ s) - a s * Real.sin (ψ s)) t =
      deriv b t * Real.cos (ψ t) + b t * (-Real.sin (ψ t) * deriv ψ t) -
        (deriv a t * Real.sin (ψ t) + a t * (Real.cos (ψ t) * deriv ψ t)) :=
    (h1.sub h2).deriv
  rw [h]
  have hp : deriv a t + b t * deriv ψ t = 0 := orth_angle_sum hnorm horth hpsi
  have hq : deriv b t - a t * deriv ψ t = 0 := orth_angle_diff hnorm horth hpsi
  linear_combination Real.cos (ψ t) * hq - Real.sin (ψ t) * hp

theorem exists_cInf_angle_lift {a b : ℝ → ℝ} (ha : ContDiff ℝ cInfT a) (hb : ContDiff ℝ cInfT b)
    (hnorm : ∀ t : ℝ, a t ^ 2 + b t ^ 2 = 1)
    (h0 : a 0 = 1 ∧ b 0 = 0)
    (hper : ∀ t : ℝ, a (t + LeanEval.KnotTheory.Quadrisecant.period) = a t ∧
      b (t + LeanEval.KnotTheory.Quadrisecant.period) = b t)
    (hinj : Set.InjOn (fun t : ℝ => (a t, b t))
      (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period))
    (hpos : ∀ t : ℝ, 0 < a t * deriv b t - b t * deriv a t) :
    ∃ psi : ℝ → ℝ, ContDiff ℝ cInfT psi ∧ psi 0 = 0 ∧
      (∀ t : ℝ, psi (t + LeanEval.KnotTheory.Quadrisecant.period)
        = psi t + LeanEval.KnotTheory.Quadrisecant.period) ∧
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
    · -- `t₂` is an interior second preimage of `(1,0)`, contradicting injectivity
      have ht₂_pos : 0 < t₂ := by
        rcases lt_or_eq_of_le ht₂_0 with h' | h'
        · exact h'
        · exfalso
          have hz : ψ t₂ = 0 := by rw [← h', hψ_zero]
          rw [hψt₂] at hz
          exact absurd hz (ne_of_gt hper_pos)
      have hmem₂ : t₂ ∈ Set.Ico 0 period := ⟨ht₂_pos.le, hlt⟩
      have hmem₀ : (0 : ℝ) ∈ Set.Ico 0 period := ⟨le_refl 0, hper_pos⟩
      have hEq : (fun t : ℝ => (a t, b t)) t₂ = (fun t : ℝ => (a t, b t)) 0 := by
        show (a t₂, b t₂) = (a 0, b 0)
        rw [← hcos t₂, ← hsin t₂, ← hcos 0, ← hsin 0, hψt₂, hψ_zero,
          show Real.cos period = 1 from by rw [period]; exact Real.cos_two_pi,
          show Real.sin period = 0 from by rw [period]; exact Real.sin_two_pi,
          Real.cos_zero, Real.sin_zero]
      exact absurd (hinj hmem₂ hmem₀ hEq) (ne_of_gt ht₂_pos)
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
