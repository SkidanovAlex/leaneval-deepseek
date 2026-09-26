import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral_decay
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound

noncomputable section

open MeasureTheory UpperHalfPlane
open Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

section IntervalIntegralSmoothness

/-- One step of differentiation under the integral sign for `y ↦ ∫_a^b g t · e^{-π y t}`, where
`g` is only assumed measurable and essentially bounded on `(a,b]`. -/
lemma hasDerivAt_intervalIntegral_exp_bound (g : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖g t‖ ≤ B) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
      (∫ t in a..b, g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))
      x := by
  set M : ℝ := max |a| |b| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left |a| |b|)
  have hπM0 : 0 ≤ Real.pi * M := mul_nonneg Real.pi_pos.le hM0
  have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ M := by
    intro t ht
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : |a| ≤ M := le_max_left |a| |b|
      have h2 : -M ≤ -|a| := neg_le_neg h1
      have h3 : -|a| ≤ a := neg_abs_le a
      linarith [ht.1]
    · have h1 : b ≤ M := le_trans (le_abs_self b) (le_max_right |a| |b|)
      linarith [ht.2]
  set B' : ℝ := B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) with hB'
  have hB'0 : 0 ≤ B' := by
    rw [hB']
    exact mul_nonneg (mul_nonneg hB (le_trans zero_le_one (le_max_left 1 (Real.pi * M))))
      (Real.exp_pos _).le
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), t ∈ Set.Ioc a b :=
    self_mem_ae_restrict measurableSet_Ioc
  have hx1 : 0 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have hE0 : 0 ≤ Real.exp (Real.pi * (|x| + 1) * M) := (Real.exp_pos _).le
  have hexp_le : ∀ t y : ℝ, t ∈ Set.Ioc a b → y ∈ Metric.ball x 1 →
      Real.exp (-(Real.pi * y * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) := by
    intro t y ht hy
    apply Real.exp_le_exp.mpr
    have hy1 : |y| ≤ |x| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have h := abs_lt.mp hy
      rw [abs_le]
      exact ⟨by linarith [h.1, neg_abs_le x], by linarith [h.2, le_abs_self x]⟩
    have ht1 : |t| ≤ M := htM t ht
    have h1 : -(Real.pi * y * t) ≤ Real.pi * |y| * |t| := by
      have h := neg_le_abs (Real.pi * y * t)
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos] at h
      exact h
    have h2 : Real.pi * |y| * |t| ≤ Real.pi * (|x| + 1) * M := by
      have hπy : Real.pi * |y| ≤ Real.pi * (|x| + 1) :=
        mul_le_mul_of_nonneg_left hy1 Real.pi_pos.le
      calc Real.pi * |y| * |t| ≤ Real.pi * (|x| + 1) * |t| :=
            mul_le_mul_of_nonneg_right hπy (abs_nonneg t)
        _ ≤ Real.pi * (|x| + 1) * M :=
            mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hx1)
    linarith
  have hbd' : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ y ∈ Metric.ball x 1,
      ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)‖ ≤ B' := by
    filter_upwards [hbd, hmem] with t hb ht y hy
    have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * |t| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    have hexp : ‖(Real.exp (-(Real.pi * y * t)) : ℂ)‖ = Real.exp (-(Real.pi * y * t)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hstep : Real.exp (-(Real.pi * y * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) :=
      hexp_le t y ht hy
    have h3 : Real.pi * |t| ≤ Real.pi * M := mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le
    calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)‖
        = ‖g t‖ * (Real.pi * |t|) * Real.exp (-(Real.pi * y * t)) := by
          rw [norm_mul, norm_mul, hfac, hexp]
      _ ≤ B * (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) :=
          mul_le_mul (mul_le_mul hb h3 (mul_nonneg Real.pi_pos.le (abs_nonneg t)) hB)
            hstep (Real.exp_pos _).le (mul_nonneg hB hπM0)
      _ ≤ B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right 1 (Real.pi * M)) hB) (Real.exp_pos _).le
      _ = B' := by rw [hB']
  have hbd'' : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ y ∈ Metric.ball x 1,
      HasDerivAt (fun y : ℝ => g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
        (g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)) y := by
    filter_upwards with t y _
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(Real.pi * y * t)))
        (Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))) y := by
      have h2 : HasDerivAt (fun y : ℝ => -(Real.pi * y * t)) (-(Real.pi * t)) y := by
        have h3 : (fun y : ℝ => -(Real.pi * y * t)) = fun y : ℝ => (-(Real.pi * t)) * y := by
          funext y; ring
        rw [h3]
        simpa using (hasDerivAt_id y).const_mul (-(Real.pi * t))
      simpa using h2.exp
    have h5 := (h1.ofReal_comp).const_mul (g t)
    have heq : g t * (↑(Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))))
        = g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      push_cast; ring
    rwa [heq] at h5
  have hIoc_lt : (volume : Measure ℝ) (Set.Ioc a b) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) (isCompact_Icc.measure_lt_top)
  have hIntFx : Integrable (fun t : ℝ => g t * (Real.exp (-(Real.pi * x * t)) : ℂ))
      (volume.restrict (Set.Ioc a b)) := by
    refine IntegrableOn.of_bound hIoc_lt ?_ B' ?_
    · exact hmeas.mul (by fun_prop)
    · filter_upwards [hbd, hmem] with t hb ht
      have hexp : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ = Real.exp (-(Real.pi * x * t)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(Real.pi * x * t)) ≤ Real.exp (Real.pi * (|x| + 1) * M) := by
        apply Real.exp_le_exp.mpr
        have ht1 : |t| ≤ M := htM t ht
        have h1 : -(Real.pi * x * t) ≤ Real.pi * |x| * |t| := by
          have h := neg_le_abs (Real.pi * x * t)
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos] at h
          exact h
        have h2 : Real.pi * |x| * |t| ≤ Real.pi * (|x| + 1) * M := by
          have hπy : Real.pi * |x| ≤ Real.pi * (|x| + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg x]) Real.pi_pos.le
          calc Real.pi * |x| * |t| ≤ Real.pi * (|x| + 1) * |t| :=
                mul_le_mul_of_nonneg_right hπy (abs_nonneg t)
            _ ≤ Real.pi * (|x| + 1) * M :=
                mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hx1)
        linarith
      calc ‖g t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
          = ‖g t‖ * Real.exp (-(Real.pi * x * t)) := by rw [norm_mul, hexp]
        _ ≤ B * Real.exp (Real.pi * (|x| + 1) * M) :=
            mul_le_mul hb hle (Real.exp_pos _).le hB
        _ ≤ B * max 1 (Real.pi * M) * Real.exp (Real.pi * (|x| + 1) * M) := by
            have h1 : B ≤ B * max 1 (Real.pi * M) := by
              simpa using mul_le_mul_of_nonneg_left (le_max_left 1 (Real.pi * M)) hB
            exact mul_le_mul_of_nonneg_right h1 hE0
        _ = B' := by rw [hB']
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc a b))
    (F := fun y (t : ℝ) => g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (F' := fun y (t : ℝ) => g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (x₀ := x) (s := Metric.ball x 1) (bound := fun _ => B')
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall (fun y => hmeas.mul (by fun_prop)))
    hIntFx
    ((hmeas.mul (by fun_prop)).mul (by fun_prop))
    hbd' (integrable_const B') hbd''
  have hconv : ∀ f : ℝ → ℂ,
      (∫ t : ℝ, f t ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hab]
  have hfun : (fun y : ℝ => ∫ t : ℝ, g t * (Real.exp (-(Real.pi * y * t)) : ℂ)
        ∂(volume.restrict (Set.Ioc a b)))
      = fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ) :=
    funext (fun y => hconv _)
  rw [hfun] at hmain
  rw [hconv (fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))]
    at hmain
  exact hmain.2

/-- **Iterated differentiation under the integral sign** on `(a,b]` for a measurable, essentially
bounded amplitude. -/
theorem iteratedDeriv_intervalIntegral_exp_bound (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖f t‖ ≤ B) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) x
      = ∫ t in a..b, f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
          * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
  induction m generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    set M : ℝ := max |a| |b| with hM
    have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left |a| |b|)
    have hπM0 : 0 ≤ Real.pi * M := mul_nonneg Real.pi_pos.le hM0
    have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ M := by
      intro t ht
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : |a| ≤ M := le_max_left |a| |b|
        have h2 : -M ≤ -|a| := neg_le_neg h1
        have h3 : -|a| ≤ a := neg_abs_le a
        linarith [ht.1]
      · have h1 : b ≤ M := le_trans (le_abs_self b) (le_max_right |a| |b|)
        linarith [ht.2]
    set g : ℝ → ℂ := fun t => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hg
    have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)) :=
      hmeas.mul (by fun_prop)
    have hgbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖g t‖ ≤ B * (Real.pi * M) ^ k := by
      filter_upwards [hbd, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ k‖ = (Real.pi * |t|) ^ k := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      rw [hg, norm_mul, hfac]
      refine mul_le_mul hb (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (abs_nonneg t))
        (mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le) k)
        (pow_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg t)) k) hB
    have hstep := hasDerivAt_intervalIntegral_exp_bound g a b hab hgmeas
      (mul_nonneg hB (pow_nonneg hπM0 k)) hgbd x
    have hIH : iteratedDeriv k (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ))
        = fun y : ℝ => ∫ t in a..b, g t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      funext y
      rw [ih y, hg]
    rw [iteratedDeriv_succ, hIH, hstep.deriv]
    have hcongr : (fun t : ℝ => g t * (((-(Real.pi * t) : ℝ)) : ℂ)
          * (Real.exp (-(Real.pi * x * t)) : ℂ))
        = fun t : ℝ => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ (k + 1)
          * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
      funext t
      rw [hg, pow_succ]
      ring
    rw [hcongr]

/-! ## The derivative formula for a compact interval integral plus a tail integral -/

/-- **Smoothness of the finite-interval Laplace transform.**
If `f` is measurable and essentially bounded on `(a,b]`, then `y ↦ ∫_a^b f t · e^{-π y t} dt`
is `C^n` on `(-1,∞)`, with the `m`-th derivative given by
`iteratedDeriv_intervalIntegral_exp_bound`.  This mirrors `tailIntegral_contDiffOn`. -/
theorem contDiffOn_intervalIntegral_exp_bound (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖f t‖ ≤ B) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ))
      (Set.Ioi (-1)) := by
  have hM0 : (0:ℝ) ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  refine contDiffOn_of_continuousOn_differentiableOn_deriv (n := (n : ℕ∞)) ?_ ?_
  · intro m hm
    have hmn : m ≤ n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioc a b)) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ => (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ max |a| |b| := by
      intro t ht
      rw [abs_le]; constructor
      · have h1 : |a| ≤ max |a| |b| := le_max_left _ _
        have h2 : -max |a| |b| ≤ -|a| := neg_le_neg h1
        have h3 : -|a| ≤ a := neg_abs_le a
        linarith [ht.1]
      · have h1 : b ≤ max |a| |b| := le_trans (le_abs_self b) (le_max_right _ _)
        linarith [ht.2]
    have hGbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖G t‖ ≤ B * (Real.pi * max |a| |b|) ^ m := by
      filter_upwards [hbd, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * |t|) ^ m := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      rw [hG, norm_mul, hfac]
      refine mul_le_mul hb ?_ (pow_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg t)) m) hB
      exact pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (abs_nonneg t))
        (mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le) m
    have hBm : 0 ≤ B * (Real.pi * max |a| |b|) ^ m :=
      mul_nonneg hB (pow_nonneg (mul_nonneg Real.pi_pos.le hM0) m)
    have hGdiff : DifferentiableOn ℝ
        (fun y : ℝ => ∫ t in a..b, G t * (Real.exp (-(Real.pi * y * t)) : ℂ)) (Set.Ioi (-1)) :=
      fun lam _ => (hasDerivAt_intervalIntegral_exp_bound G a b hab hGmeas hBm hGbd lam)
        |>.differentiableAt.differentiableWithinAt
    refine hGdiff.continuousOn.congr ?_
    intro x hx
    show iteratedDerivWithin m
        (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) (Set.Ioi (-1)) x
      = ∫ t in a..b, G t * (Real.exp (-(Real.pi * x * t)) : ℂ)
    rw [iteratedDerivWithin_of_isOpen (n := m)
      (f := fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) isOpen_Ioi hx, hG]
    exact iteratedDeriv_intervalIntegral_exp_bound f a b hab hmeas hB hbd m x
  · intro m hm
    have hmn : m < n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => f t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioc a b)) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ => (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have htM : ∀ t ∈ Set.Ioc a b, |t| ≤ max |a| |b| := by
      intro t ht
      rw [abs_le]; constructor
      · have h1 : |a| ≤ max |a| |b| := le_max_left _ _
        have h2 : -max |a| |b| ≤ -|a| := neg_le_neg h1
        have h3 : -|a| ≤ a := neg_abs_le a
        linarith [ht.1]
      · have h1 : b ≤ max |a| |b| := le_trans (le_abs_self b) (le_max_right _ _)
        linarith [ht.2]
    have hGbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖G t‖ ≤ B * (Real.pi * max |a| |b|) ^ m := by
      filter_upwards [hbd, self_mem_ae_restrict measurableSet_Ioc] with t hb ht
      have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * |t|) ^ m := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      rw [hG, norm_mul, hfac]
      refine mul_le_mul hb ?_ (pow_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg t)) m) hB
      exact pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (abs_nonneg t))
        (mul_le_mul_of_nonneg_left (htM t ht) Real.pi_pos.le) m
    have hBm : 0 ≤ B * (Real.pi * max |a| |b|) ^ m :=
      mul_nonneg hB (pow_nonneg (mul_nonneg Real.pi_pos.le hM0) m)
    have hGdiff : DifferentiableOn ℝ
        (fun y : ℝ => ∫ t in a..b, G t * (Real.exp (-(Real.pi * y * t)) : ℂ)) (Set.Ioi (-1)) :=
      fun lam _ => (hasDerivAt_intervalIntegral_exp_bound G a b hab hGmeas hBm hGbd lam)
        |>.differentiableAt.differentiableWithinAt
    refine hGdiff.congr fun x hx => ?_
    show iteratedDerivWithin m
        (fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) (Set.Ioi (-1)) x
      = ∫ t in a..b, G t * (Real.exp (-(Real.pi * x * t)) : ℂ)
    rw [iteratedDerivWithin_of_isOpen (n := m)
      (f := fun y : ℝ => ∫ t in a..b, f t * (Real.exp (-(Real.pi * y * t)) : ℂ)) isOpen_Ioi hx, hG]
    exact iteratedDeriv_intervalIntegral_exp_bound f a b hab hmeas hB hbd m x

end IntervalIntegralSmoothness

section SpikeModel

open Work.Asymptotics.HalfFunnel in
/-- Sharp base case of the spike model integral: for `y > 1`, `a ≥ 0`, `ε ≠ 0`, `|ε| ≤ 1/4`,
`‖∫_{-1}^{1} e^{-a(y+u)} (u+iε)⁻¹ du‖ ≤ (π+2) e^{-a(y-1)}`. -/
lemma spikeModelSharpZero :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y a ε : ℝ), 1 < y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖
        ≤ C * Real.exp (-(a * (y - 1))) := by
  refine ⟨Real.pi + 2, by positivity, ?_⟩
  intro y a ε hy ha hε hε4
  have hs : ∀ u : ℝ, u ^ 2 + ε ^ 2 ≠ 0 := by
    intro u; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
  have hD : ∀ u : ℝ, 0 < u ^ 2 + ε ^ 2 := by
    intro u; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
  have hpt : ∀ u : ℝ,
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹
      = ((Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
        - (ε : ℂ) * Complex.I * ((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
    intro u
    rw [Work.Asymptotics.HalfFunnel.spike_exp_neg_mul_ofReal,
      Work.Asymptotics.HalfFunnel.spike_inv_add_mul_I hε]
    push_cast
    field_simp
  have hcontA : Continuous
      (fun u : ℝ => ((Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Continuous.div (by fun_prop) (by fun_prop) hs)
  have hcontB : Continuous
      (fun u : ℝ => ((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Continuous.div (by fun_prop) (by fun_prop) hs)
  have hid : (∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
        ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹)
      = (∫ u in (-1 : ℝ)..1, ((Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        - (ε : ℂ) * Complex.I
          * (∫ u in (-1 : ℝ)..1, ((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) := by
    rw [show (∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹)
        = ∫ u in (-1 : ℝ)..1, (((Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
            - (ε : ℂ) * Complex.I *
              ((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) by
      apply intervalIntegral.integral_congr
      intro u _
      exact hpt u]
    have hI : IntervalIntegrable
        (fun u : ℝ => (ε : ℂ) * Complex.I *
          ↑(Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2))) volume (-1) 1 :=
      (continuous_const.mul hcontB).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (hcontA.intervalIntegrable _ _) hI,
      intervalIntegral.integral_const_mul]
  rw [hid]
  simp_rw [intervalIntegral.integral_ofReal]
  have h1 : |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)|
      ≤ 2 * Real.exp (-(a * (y - 1))) := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hzero : (∫ u in (-1 : ℝ)..1, Real.exp (-(0 * (y + u))) * u / (u ^ 2 + ε ^ 2)) = 0 := by
        rw [show (∫ u in (-1 : ℝ)..1, Real.exp (-(0 * (y + u))) * u / (u ^ 2 + ε ^ 2))
            = ∫ u in (-1 : ℝ)..1, u / (u ^ 2 + ε ^ 2) by
              apply intervalIntegral.integral_congr
              intro u _; simp]
        exact Work.Asymptotics.HalfFunnel.spike_odd_integral 1 ε
      rw [hzero, abs_zero]; positivity
    · exact Work.Asymptotics.HalfFunnel.spike_re_num_integral_bound h one_pos hy hε
  have h2 : |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)|
      ≤ Real.exp (-(a * (y - 1))) * (Real.pi / |ε|) := by
    have hnn : 0 ≤ ∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2) :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun u _ => div_nonneg (Real.exp_nonneg _) (hD u).le)
    rw [abs_of_nonneg hnn]
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have heq : (∫ u in (-1 : ℝ)..1, Real.exp (-(0 * (y + u))) / (u ^ 2 + ε ^ 2))
          = ∫ u in (-1 : ℝ)..1, (u ^ 2 + ε ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro u _
        simp [div_eq_mul_inv]
      rw [heq]
      simpa using Work.Asymptotics.HalfFunnel.spike_inv_sq_integral_le (ρ := (1 : ℝ)) hε
    · exact Work.Asymptotics.HalfFunnel.spike_re_den_integral_bound h one_pos hy hε
  have hX : ‖(((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ)‖
      = |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hY : ‖(ε : ℂ) * Complex.I *
        (((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ)‖
      = |ε| * |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)| := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs]
  have harith : 2 * Real.exp (-(a * (y - 1))) +
        |ε| * (Real.exp (-(a * (y - 1))) * (Real.pi / |ε|))
      = (Real.pi + 2) * Real.exp (-(a * (y - 1))) := by
    have hne : (|ε| : ℝ) ≠ 0 := abs_ne_zero.mpr hε
    have hexp : Real.exp (-(a * (y - 1))) ≠ 0 := Real.exp_ne_zero _
    field_simp
    ring
  calc ‖(((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ)
        - (ε : ℂ) * Complex.I *
          (((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ)‖
      ≤ |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)|
        + |ε| * |∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)| := by
        have hstep := norm_sub_le
          (((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) * u / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ)
          ((ε : ℂ) * Complex.I *
            (((∫ u in (-1 : ℝ)..1, Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ))
        rw [hX, hY] at hstep
        exact hstep
    _ ≤ 2 * Real.exp (-(a * (y - 1))) + |ε| * (Real.exp (-(a * (y - 1))) * (Real.pi / |ε|)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg ε))
    _ = (Real.pi + 2) * Real.exp (-(a * (y - 1))) := harith
/-- **Sharp spike model integral with a polynomial numerator.**  For `y > 1`, `a ≥ 0`, `ε ≠ 0`,
`|ε| ≤ 1/4` and every `m`,
`‖∫_{-1}^{1} e^{-a(y+u)} (u+iε)⁻¹ (y+u)^m du‖ ≤ C (1+y)^m e^{-a(y-1)}`,
with `C` independent of `m`, `y`, `a`, `ε`.  The proof is the elementary recursion
`(y+u)^{m+1}/(u+iε) = (y+u)^m + (y-iε)(y+u)^m/(u+iε)` on top of `spikeModelSharpZero`;
no `(1+a)` factor is produced, which is what makes the bound usable for a fixed
exponential weight `e^{-π x}`. -/
lemma spikeModelSharpPoly :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), ∀ (y a ε : ℝ), 1 < y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m‖
        ≤ C * (1 + y) ^ m * Real.exp (-(a * (y - 1))) := by
  obtain ⟨C₀, hC₀, hbase⟩ := spikeModelSharpZero
  refine ⟨max C₀ (8 / 3), le_trans (by norm_num : (0:ℝ) ≤ 8 / 3) (le_max_right _ _), ?_⟩
  intro m
  induction m with
  | zero =>
    intro y a ε hy ha hε hε4
    have h := hbase y a ε hy ha hε hε4
    have he : (∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ 0)
        = ∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [pow_zero, mul_one]
    rw [he]
    calc ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖
        ≤ C₀ * Real.exp (-(a * (y - 1))) := h
      _ ≤ max C₀ (8 / 3) * (1 + y) ^ 0 * Real.exp (-(a * (y - 1))) := by
          rw [pow_zero, mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  | succ k ih =>
    intro y a ε hy ha hε hε4
    have hs : ∀ u : ℝ, ((u : ℂ) + (ε : ℂ) * Complex.I) ≠ 0 := by
      intro u h
      have h2 := congrArg Complex.im h
      simp at h2
      exact hε h2
    have hident : ∀ u : ℝ, ((y : ℂ) + (u : ℂ)) ^ (k + 1) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹
        = ((y : ℂ) + (u : ℂ)) ^ k + ((y : ℂ) - (ε : ℂ) * Complex.I) *
            (((y : ℂ) + (u : ℂ)) ^ k * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹) := by
      intro u
      have h := hs u
      rw [pow_succ]
      field_simp
      ring
    have hpt : ∀ u : ℝ,
        Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
          ((y : ℂ) + (u : ℂ)) ^ (k + 1)
        = Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k
          + ((y : ℂ) - (ε : ℂ) * Complex.I) *
            (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
              ((y : ℂ) + (u : ℂ)) ^ k) := by
      intro u
      rw [show Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
            ((y : ℂ) + (u : ℂ)) ^ (k + 1)
          = Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            (((y : ℂ) + (u : ℂ)) ^ (k + 1) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹) by ring]
      rw [hident u]
      ring
    have hcont1 : Continuous
        (fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k) :=
      by fun_prop
    have hcont2 : Continuous (fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
        ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ k) := by
      apply Continuous.mul
      · apply Continuous.mul
        · fun_prop
        · exact Continuous.inv₀ (by fun_prop) hs
      · fun_prop
    have hI2 : IntervalIntegrable (fun u : ℝ => ((y : ℂ) - (ε : ℂ) * Complex.I) *
        (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
          ((y : ℂ) + (u : ℂ)) ^ k)) volume (-1) 1 :=
      (continuous_const.mul hcont2).intervalIntegrable _ _
    have hG : ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
        ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ k‖
        ≤ max C₀ (8 / 3) * (1 + y) ^ k * Real.exp (-(a * (y - 1))) := ih y a ε hy ha hε hε4
    have hF : ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
        ((y : ℂ) + (u : ℂ)) ^ k‖ ≤ 2 * (1 + y) ^ k * Real.exp (-(a * (y - 1))) := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (-1 : ℝ)) (b := 1) (C := (1 + y) ^ k * Real.exp (-(a * (y - 1))))
        (f := fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k) ?_
      · rw [show (1 : ℝ) - (-1) = 2 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
        calc ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k‖
            ≤ (1 + y) ^ k * Real.exp (-(a * (y - 1))) * 2 := hb
          _ = 2 * (1 + y) ^ k * Real.exp (-(a * (y - 1))) := by ring
      · intro u hu
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
        have hu1 : -1 ≤ u := le_of_lt hu.1
        have hu2 : u ≤ 1 := hu.2
        have hyu : 0 < y + u := by linarith
        have hnorm : ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k‖
            = Real.exp (-(a * (y + u))) * (y + u) ^ k := by
          rw [norm_mul, Complex.norm_exp, norm_pow]
          congr 2
          · simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
          · rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyu]
        rw [hnorm]
        have h1 : Real.exp (-(a * (y + u))) ≤ Real.exp (-(a * (y - 1))) := by
          apply Real.exp_le_exp.mpr; nlinarith [hu1, ha]
        have h2 : (y + u) ^ k ≤ (y + 1) ^ k :=
          pow_le_pow_left₀ hyu.le (by linarith) k
        calc Real.exp (-(a * (y + u))) * (y + u) ^ k
            ≤ Real.exp (-(a * (y - 1))) * (y + 1) ^ k :=
              mul_le_mul h1 h2 (pow_nonneg hyu.le k) (Real.exp_nonneg _)
          _ = (1 + y) ^ k * Real.exp (-(a * (y - 1))) := by ring
    have hConst : ‖((y : ℂ) - (ε : ℂ) * Complex.I)‖ ≤ y + 1 / 4 := by
      have h1 : ‖((y : ℂ) - (ε : ℂ) * Complex.I)‖ ≤ ‖(y : ℂ)‖ + ‖(ε : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (le_of_lt (lt_trans zero_lt_one hy))] at h1
      linarith [abs_le.mp hε4]
    rw [show (∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ (k + 1))
          = ∫ u in (-1 : ℝ)..1, (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k
              + ((y : ℂ) - (ε : ℂ) * Complex.I) *
                (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
                  ((y : ℂ) + (u : ℂ)) ^ k)) by
            apply intervalIntegral.integral_congr
            intro u _
            exact hpt u]
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) hI2,
      intervalIntegral.integral_const_mul]
    calc ‖(∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ k)
              + ((y : ℂ) - (ε : ℂ) * Complex.I) *
                (∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
                  ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ k)‖
          ≤ 2 * (1 + y) ^ k * Real.exp (-(a * (y - 1)))
            + (y + 1 / 4) * (max C₀ (8 / 3) * (1 + y) ^ k * Real.exp (-(a * (y - 1)))) := by
            refine le_trans (norm_add_le _ _) ?_
            exact add_le_add hF (le_trans (le_of_eq (norm_mul _ _))
              (mul_le_mul hConst hG (norm_nonneg _) (by positivity)))
        _ ≤ max C₀ (8 / 3) * (1 + y) ^ (k + 1) * Real.exp (-(a * (y - 1))) := by
            have hkey : 2 + max C₀ (8 / 3) * (y + 1 / 4) ≤ max C₀ (8 / 3) * (y + 1) := by
              have hC8 : (8 : ℝ) / 3 ≤ max C₀ (8 / 3) := le_max_right _ _
              nlinarith
            have hP : (0 : ℝ) ≤ (1 + y) ^ k * Real.exp (-(a * (y - 1))) := by positivity
            calc 2 * (1 + y) ^ k * Real.exp (-(a * (y - 1)))
                  + (y + 1 / 4) * (max C₀ (8 / 3) * (1 + y) ^ k * Real.exp (-(a * (y - 1))))
                = (2 + max C₀ (8 / 3) * (y + 1 / 4)) *
                    ((1 + y) ^ k * Real.exp (-(a * (y - 1)))) := by ring
              _ ≤ max C₀ (8 / 3) * (y + 1) * ((1 + y) ^ k * Real.exp (-(a * (y - 1)))) :=
                  mul_le_mul_of_nonneg_right hkey hP
              _ = max C₀ (8 / 3) * (1 + y) ^ (k + 1) * Real.exp (-(a * (y - 1))) := by
                  rw [pow_succ]; ring

/-- Window bound for the CKMRV kernel on the spike `|t - Im τ| ≤ 1` of the funnel:
the two translate poles `τ ∓ 1` stay at distance `1 ∓ Re τ > 0` from the contour, so the
decomposition `funnelKernelSpike` turns the (τ-dependent) bound into a bound. -/
lemma spikeWindow_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : Funnel τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, τ.im - 1 ≤ t → t ≤ τ.im + 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ B := by
  obtain ⟨c₁, c₂, Cc, Nd, M, hCc, hNd, hM, hc₁, hc₂, hdec⟩ :=
    (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ d hd).2
  have hy : 2 ≤ τ.im := hτ.2
  have hD : τ ∈ DomainD := hτ.1
  have hre_lt : τ.re < 1 := hD.2.1
  have hre_gt : -1 < τ.re := hD.1
  have hδ : 0 < 1 - τ.re := by linarith
  have hδ' : 0 < 1 + τ.re := by linarith
  refine ⟨‖c₁‖ / (1 - τ.re) + ‖c₂‖ / (1 + τ.re)
    + Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M, ?_, ?_⟩
  · have h1 : 0 ≤ ‖c₁‖ / (1 - τ.re) := div_nonneg (norm_nonneg _) hδ.le
    have h2 : 0 ≤ ‖c₂‖ / (1 + τ.re) := div_nonneg (norm_nonneg _) hδ'.le
    have h3 : 0 ≤ Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M :=
      mul_nonneg (mul_nonneg hCc.le (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) Nd))
        (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 + τ.im) M)
    linarith
  intro t ht1 ht2
  have hb := hdec τ t hD hy ht1 ht2
  have hpole1 : ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))‖ ≤ ‖c₁‖ / (1 - τ.re) := by
    rw [norm_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) hδ ?_
    have hzre : (((t : ℂ) * Complex.I - ((τ : ℂ) - 1)).re) = 1 - τ.re := by
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, UpperHalfPlane.coe_re]
    calc 1 - τ.re = |1 - τ.re| := (abs_of_pos hδ).symm
      _ = |(((t : ℂ) * Complex.I - ((τ : ℂ) - 1)).re)| := by rw [hzre]
      _ ≤ ‖(t : ℂ) * Complex.I - ((τ : ℂ) - 1)‖ := Complex.abs_re_le_norm _
  have hpole2 : ‖c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖ ≤ ‖c₂‖ / (1 + τ.re) := by
    rw [norm_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) hδ' ?_
    have hzre : (((t : ℂ) * Complex.I - ((τ : ℂ) + 1)).re) = -(1 + τ.re) := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, Complex.one_re,
        Complex.one_im, Complex.ofReal_one]
      ring
    calc 1 + τ.re = |-(1 + τ.re)| := by rw [abs_neg, abs_of_pos hδ']
      _ = |(((t : ℂ) * Complex.I - ((τ : ℂ) + 1)).re)| := by rw [hzre]
      _ ≤ ‖(t : ℂ) * Complex.I - ((τ : ℂ) + 1)‖ := Complex.abs_re_le_norm _
  have h1t : (0:ℝ) < 1 + t := by linarith
  have hpM : (1 + t) ^ M ≤ (2 + τ.im) ^ M :=
    Real.rpow_le_rpow (by linarith) (by linarith) hM
  have hsplit : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤
      ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))‖ + ‖c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖
        + Cc * (Work.Kernels.scale τ) ^ Nd * (1 + t) ^ M := by
    have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
              (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
                c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))‖
          + ‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
                c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖ := by
      have h := norm_add_le
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
          (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
            c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))))
        (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
          c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))
      rwa [sub_add_cancel] at h
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ _ + _ := h1
      _ ≤ Cc * (Work.Kernels.scale τ) ^ Nd * (1 + t) ^ M
            + (‖c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1))‖
              + ‖c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))‖) :=
          add_le_add hb (norm_add_le _ _)
      _ = _ := by ring
  refine le_trans hsplit ?_
  refine add_le_add (add_le_add hpole1 hpole2) ?_
  exact mul_le_mul_of_nonneg_left hpM
    (mul_nonneg hCc.le (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) Nd))

/-- Pointwise bound for a spike pole the contour stays away from (`|ε| > 1/4`). -/
lemma spikeFarPointwise (y x : ℝ) (m : ℕ) (ε : ℝ) (hε : ε ≠ 0) (hgt : 1 / 4 < |ε|) (hx : 0 ≤ x)
    (hy : 1 < y) (u : ℝ) (hu1 : -1 ≤ u) (hu2 : u ≤ 1) :
    ‖((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m *
        Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ)))‖
      ≤ 4 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) := by
  have hyu : 0 < y + u := by linarith
  have hnorminv : ‖((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have him : |ε| ≤ ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((u : ℂ) + (ε : ℂ) * Complex.I)
      simpa [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, one_mul, add_zero] using h
    have hpos : 0 < ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ := lt_of_lt_of_le (by linarith) him
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hnormpow : ‖((y : ℂ) + (u : ℂ)) ^ m‖ = (y + u) ^ m := by
    rw [norm_pow, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyu]
  have hnormexp : ‖Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ)))‖
      = Real.exp (-(Real.pi * x * (y + u))) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_im, Complex.add_im, mul_zero, zero_add]
    ring
  have hexp : Real.exp (-(Real.pi * x * (y + u))) ≤ Real.exp (-(Real.pi * x * (y - 1))) := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.pi * x * (y - 1) ≤ Real.pi * x * (y + u) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ Real.pi * x)
      linarith
    linarith
  have hpow : (y + u) ^ m ≤ (1 + y) ^ m := pow_le_pow_left₀ hyu.le (by linarith) m
  rw [norm_mul, norm_mul, hnormpow, hnormexp]
  calc ‖((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖ * (y + u) ^ m * Real.exp (-(Real.pi * x * (y + u)))
      ≤ 4 * (y + u) ^ m * Real.exp (-(Real.pi * x * (y + u))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_right hnorminv (pow_nonneg hyu.le m)
    _ ≤ 4 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hexp (Real.exp_nonneg _)
          (by positivity)

/-- **Bound for one spike pole of the funnel layer.**  For every `ε ≠ 0`,
`‖∫_{-1}^1 (u+iε)⁻¹ (y+u)^m e^{-πx(y+u)} du‖ ≤ max Cm 8 · (1+y)^m · e^{-πx(y-1)}`,
where `Cm` is the constant of the sharp model integral `spikeModelSharpPoly`: if `|ε| ≤ 1/4`
the (signed) model integral is exponentially small in `πx(y-1)`, otherwise the pole is at
distance `> 1/4` and a crude absolute value estimate suffices. -/
lemma spikePoleQ (Cm : ℝ)
    (hmodel : ∀ (m : ℕ) (y a ε : ℝ), 1 < y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-1 : ℝ)..1, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m‖
        ≤ Cm * (1 + y) ^ m * Real.exp (-(a * (y - 1))))
    (m : ℕ) (y x : ℝ) (hy : 1 < y) (hx : 0 ≤ x) (ε : ℝ) (hε : ε ≠ 0) :
    ‖∫ u in (-1 : ℝ)..1, ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m *
        Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ)))‖
      ≤ max Cm 8 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) := by
  rcases (lt_or_ge (1 / 4 : ℝ) |ε|).symm with hle | hgt
  · have h := hmodel m y (Real.pi * x) ε hy (mul_nonneg Real.pi_pos.le hx) hε hle
    rw [show (∫ u in (-1 : ℝ)..1, ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m *
          Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ))))
        = ∫ u in (-1 : ℝ)..1, Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m by
      apply intervalIntegral.integral_congr
      intro u _
      ring]
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cm 8) (by positivity)) (Real.exp_nonneg _)
  · have hbound : ∀ u ∈ Set.uIoc (-1 : ℝ) 1,
        ‖((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m *
          Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ)))‖
          ≤ 4 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) := by
      intro u hu
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
      exact spikeFarPointwise y x m ε hε hgt hx hy u (le_of_lt hu.1) hu.2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := 4 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))))
      (f := fun u : ℝ => ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m *
        Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ)))) hbound
    rw [show (1 : ℝ) - (-1) = 2 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    refine le_trans h ?_
    rw [show 4 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) * 2
        = 8 * (1 + y) ^ m * Real.exp (-(Real.pi * x * (y - 1))) by ring]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Cm 8) (by positivity)) (Real.exp_nonneg _)

/-- The elementary pole shift `(a + iu)⁻¹ = -i (u - ia)⁻¹` for real `a`, `u`. -/
lemma spike_shift_inv (a u : ℝ) :
    ((a : ℂ) + (u : ℂ) * Complex.I)⁻¹ = -Complex.I * ((u : ℂ) + ((-a : ℝ) : ℂ) * Complex.I)⁻¹ := by
  have hkey : -Complex.I * ((a : ℂ) + (u : ℂ) * Complex.I)
      = (u : ℂ) + ((-a : ℝ) : ℂ) * Complex.I := by
    have h1 : -Complex.I * ((u : ℂ) * Complex.I) = (u : ℂ) := by
      rw [show -Complex.I * ((u : ℂ) * Complex.I)
          = -((u : ℂ) * (Complex.I * Complex.I)) by ring, Complex.I_mul_I]
      ring
    rw [mul_add, h1]
    push_cast
    ring
  have hI : (-Complex.I : ℂ)⁻¹ = Complex.I := by
    rw [← neg_inv, Complex.inv_I]
    ring
  have hgen : ∀ z : ℂ, -Complex.I * (z * Complex.I) = z := by
    intro z
    rw [show -Complex.I * (z * Complex.I) = -(z * (Complex.I * Complex.I)) by ring,
      Complex.I_mul_I]
    ring
  rw [← hkey, mul_inv_rev, hI]
  exact (hgen _).symm

/-- The `m`-th power of the derivative weight: `(-(π'(y+u)))ᵐ = (-π')ᵐ (y+u)ᵐ` in `ℂ`. -/
lemma spike_pow_shift (π' y u : ℝ) (m : ℕ) :
    (((-(π' * (y + u)) : ℝ)) : ℂ) ^ m = (-(↑π')) ^ m * ((y : ℂ) + (u : ℂ)) ^ m := by
  rw [show (((-(π' * (y + u)) : ℝ)) : ℂ) = (-(↑π')) * ((y : ℂ) + (u : ℂ)) by
    push_cast; ring, mul_pow]

/-- Casting the Laplace weight: `↑(e^{-π x (y+u)}) = e^{-↑(πx)(y+u)}`. -/
lemma spike_exp_shift (x y u : ℝ) :
    (Real.exp (-(Real.pi * x * (y + u))) : ℂ)
      = Complex.exp (-(↑(Real.pi * x) : ℂ) * ((y : ℂ) + (u : ℂ))) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Pointwise identity for the first spike pole. -/
lemma spike_term1 (τ : UpperHalfPlane) (x : ℝ) (m : ℕ) (u : ℝ) :
    (((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) - 1))⁻¹
        * ((((-(Real.pi * (τ.im + u)) : ℝ)) : ℂ) ^ m
            * (Real.exp (-(Real.pi * x * (τ.im + u))) : ℂ))
      = (-Complex.I) * ((-(Real.pi : ℂ)) ^ m)
        * (((u : ℂ) + ((τ.re - 1 : ℝ) : ℂ) * Complex.I)⁻¹ * ((τ.im : ℂ) + (u : ℂ)) ^ m
            * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))) := by
  have hτc : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hIt : ((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) - 1)
      = ((1 - τ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I := by
    rw [hτc]; push_cast; ring
  rw [hIt, spike_shift_inv (1 - τ.re) u,
    show (-(1 - τ.re) : ℝ) = τ.re - 1 by ring,
    spike_pow_shift Real.pi τ.im u m, spike_exp_shift x τ.im u]
  ring

/-- Pointwise identity for the second spike pole. -/
lemma spike_term2 (τ : UpperHalfPlane) (x : ℝ) (m : ℕ) (u : ℝ) :
    (((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) + 1))⁻¹
        * ((((-(Real.pi * (τ.im + u)) : ℝ)) : ℂ) ^ m
            * (Real.exp (-(Real.pi * x * (τ.im + u))) : ℂ))
      = (-Complex.I) * ((-(Real.pi : ℂ)) ^ m)
        * (((u : ℂ) + ((τ.re + 1 : ℝ) : ℂ) * Complex.I)⁻¹ * ((τ.im : ℂ) + (u : ℂ)) ^ m
            * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))) := by
  have hτc : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hIt : ((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) + 1)
      = ((-(1 + τ.re) : ℝ) : ℂ) + (u : ℂ) * Complex.I := by
    rw [hτc]; push_cast; ring
  rw [hIt, spike_shift_inv (-(1 + τ.re)) u,
    show (-(-(1 + τ.re)) : ℝ) = τ.re + 1 by ring,
    spike_pow_shift Real.pi τ.im u m, spike_exp_shift x τ.im u]
  ring

/-- An `IntervalIntegrable` on `(-1,1)` from an a.e. bound on `(-1,1]`. -/
lemma intervalIntegrable_of_bound_uIoc {f : ℝ → ℂ} (B : ℝ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc (-1 : ℝ) 1)))
    (hbd : ∀ᵐ u ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)), ‖f u‖ ≤ B) :
    IntervalIntegrable f volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc (-1 : ℝ) 1) < ⊤ := by
    have hsub : Set.uIoc (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 := by
      rw [← Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Set.uIoc_subset_uIcc
    exact lt_of_le_of_lt (measure_mono hsub) isCompact_Icc.measure_lt_top
  exact MeasureTheory.IntegrableOn.of_bound hfin hmeas B hbd

/-- **Iterated-derivative bound for the spike piece of the funnel layer.** -/
lemma spikeIteratedDeriv_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (l : ℕ) :
    ∃ A N : ℝ, 0 ≤ A ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane), Funnel τ → ∀ (m : ℕ), m ≤ l →
      ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (spikeT ℓ d τ) x‖
        ≤ A * (Work.Kernels.scale τ) ^ N * Real.exp (-(Real.pi * x)) := by
  obtain ⟨c₁, c₂, Cc, Nd, M, hCc, hNd, hM, hc₁, hc₂, hdec⟩ :=
    (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ d hd).2
  obtain ⟨Cm, hCm0, hmodel⟩ := spikeModelSharpPoly
  let A : ℝ := 2 * Cc * Real.pi ^ l * max Cm 8 * ((2 : ℝ) ^ l)
      + 2 * Cc * ((3 : ℝ) ^ M) * Real.pi ^ l * ((2 : ℝ) ^ l)
  let N : ℝ := max (l : ℝ) (Nd + M + l)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hN0 : 0 ≤ N := by
    dsimp only [N]
    positivity
  refine ⟨A, N, hA0, hN0, ?_⟩
  intro τ hτ m hm x hx
  have hy : 2 ≤ τ.im := hτ.2
  have hD : τ ∈ DomainD := hτ.1
  have hre_lt : τ.re < 1 := hD.2.1
  have hre_gt : -1 < τ.re := hD.1
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hSp : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  obtain ⟨B, hB0, hBw⟩ := spikeWindow_bound ℓ d hd τ hτ
  have hab : τ.im - 1 ≤ τ.im + 1 := by linarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))),
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact hBw t (le_of_lt ht.1) ht.2
  have hF_eq : spikeT ℓ d τ = fun y : ℝ => ∫ t in (τ.im - 1)..(τ.im + 1),
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [spikeT]
    apply intervalIntegral.integral_congr
    intro t _
    show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * wgt y t
      = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ)
    rw [wgt_apply, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hderiv := iteratedDeriv_intervalIntegral_exp_bound
    (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
    (τ.im - 1) (τ.im + 1) hab hmeas hB0 hbd m x
  rw [hF_eq, hderiv]
  let Aint : ℝ → ℂ := fun u => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ (τ.im + u)
  let W : ℝ → ℂ := fun u => (((-(Real.pi * (τ.im + u)) : ℝ)) : ℂ) ^ m
    * (Real.exp (-(Real.pi * x * (τ.im + u))) : ℂ)
  let It1 : ℝ → ℂ := fun u => ((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) - 1)
  let It2 : ℝ → ℂ := fun u => ((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) + 1)
  let pp : ℝ → ℂ := fun u => c₁ * (It1 u)⁻¹ + c₂ * (It2 u)⁻¹
  let En : ℝ → ℂ := fun u => Aint u - pp u
  have hsub : (∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * ((((-(Real.pi * t) : ℝ)) : ℂ) ^ m) * (Real.exp (-(Real.pi * x * t)) : ℂ))
      = ∫ u in (-1 : ℝ)..1, Aint u * W u := by
    rw [show (∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * ((((-(Real.pi * t) : ℝ)) : ℂ) ^ m) * (Real.exp (-(Real.pi * x * t)) : ℂ))
        = ∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * (((((-(Real.pi * t) : ℝ)) : ℂ) ^ m) * (Real.exp (-(Real.pi * x * t)) : ℂ)) by
      apply intervalIntegral.integral_congr
      intro t _
      ring]
    rw [show τ.im - 1 = τ.im + (-1) by ring]
    rw [← intervalIntegral.integral_comp_add_left (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * (((((-(Real.pi * t) : ℝ)) : ℂ) ^ m) * (Real.exp (-(Real.pi * x * t)) : ℂ))) τ.im]
  rw [hsub]
  -- ## the pointwise decomposition of the integrand
  have hpoint : ∀ u : ℝ, Aint u * W u
      = c₁ * ((It1 u)⁻¹ * W u) + c₂ * ((It2 u)⁻¹ * W u) + En u * W u := by
    intro u
    simp only [En, pp]
    ring
  -- ## non-vanishing of the two pole factors, and their norms
  have hIt1re : ∀ u : ℝ, (It1 u).re = 1 - τ.re := by
    intro u
    have hτc : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    simp only [It1]
    rw [hτc]
    simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      mul_zero, add_zero, zero_mul, zero_sub]
    ring
  have hIt2re : ∀ u : ℝ, (It2 u).re = -(1 + τ.re) := by
    intro u
    have hτc : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    simp only [It2]
    rw [hτc]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      mul_zero, add_zero, zero_mul, zero_sub]
    ring
  have hIt1ne : ∀ u : ℝ, It1 u ≠ 0 := by
    intro u h
    have hre := congrArg Complex.re h
    rw [hIt1re u] at hre
    simp at hre
    linarith
  have hIt2ne : ∀ u : ℝ, It2 u ≠ 0 := by
    intro u h
    have hre := congrArg Complex.re h
    rw [hIt2re u] at hre
    simp at hre
    linarith
  have hcIt1 : Continuous It1 := by simp only [It1]; fun_prop
  have hcIt2 : Continuous It2 := by simp only [It2]; fun_prop
  have hcW : Continuous W := by simp only [W]; fun_prop
  have hInt1 : IntervalIntegrable (fun u : ℝ => (It1 u)⁻¹ * W u) volume (-1) 1 :=
    ((hcIt1.inv₀ hIt1ne).mul hcW).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun u : ℝ => (It2 u)⁻¹ * W u) volume (-1) 1 :=
    ((hcIt2.inv₀ hIt2ne).mul hcW).intervalIntegrable _ _

  -- ## norm estimates for the building blocks
  have hSnn : (0 : ℝ) ≤ Work.Kernels.scale τ ^ Nd := Real.rpow_nonneg (le_of_lt hSp) Nd
  have hEnbd : ∀ u : ℝ, -1 ≤ u → u ≤ 1 →
      ‖En u‖ ≤ Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M := by
    intro u hu1 hu2
    have h := hdec τ (τ.im + u) hD hy (by linarith) (by linarith)
    have hEq : En u = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ (τ.im + u)
        - (c₁ / (((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) - 1))
            + c₂ / (((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) + 1))) := by
      simp only [En, pp, It1, It2, Aint, div_eq_mul_inv]
    rw [hEq]
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCc.le hSnn)
    exact Real.rpow_le_rpow (by linarith) (by linarith) hM
  have hWbd : ∀ u : ℝ, -1 ≤ u → u ≤ 1 →
      ‖W u‖ ≤ Real.pi ^ m * (1 + τ.im) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
    intro u hu1 hu2
    have hyu : 0 < τ.im + u := by linarith
    have hnorm : ‖W u‖
        = (Real.pi * (τ.im + u)) ^ m * Real.exp (-(Real.pi * x * (τ.im + u))) := by
      simp only [W]
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * (τ.im + u)),
        abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    have h1 : (Real.pi * (τ.im + u)) ^ m ≤ (Real.pi * (1 + τ.im)) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt Real.pi_pos)
    have h2 : Real.exp (-(Real.pi * x * (τ.im + u)))
        ≤ Real.exp (-(Real.pi * x * (τ.im - 1))) := by
      apply Real.exp_le_exp.mpr
      have : Real.pi * x * (τ.im - 1) ≤ Real.pi * x * (τ.im + u) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ Real.pi * x)
        linarith
      linarith
    calc (Real.pi * (τ.im + u)) ^ m * Real.exp (-(Real.pi * x * (τ.im + u)))
        ≤ (Real.pi * (1 + τ.im)) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1))) :=
          mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
      _ = Real.pi ^ m * (1 + τ.im) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
          rw [mul_pow]
  -- ## integrability of `En · W`
  have hmeasEn : Measurable En := by
    have h1 : Measurable Aint :=
      (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).comp (by fun_prop)
    have h2 : Measurable pp := by
      simp only [pp]
      exact ((continuous_const.mul (hcIt1.inv₀ hIt1ne)).add
        (continuous_const.mul (hcIt2.inv₀ hIt2ne))).measurable
    have : En = fun u : ℝ => Aint u - pp u := rfl
    rw [this]
    exact h1.sub h2
  have hintEn : IntervalIntegrable (fun u : ℝ => En u * W u) volume (-1) 1 := by
    refine intervalIntegrable_of_bound_uIoc
      (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M
        * (Real.pi ^ m * (1 + τ.im) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1)))))
      (hmeasEn.mul hcW.measurable).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    have hu1 : -1 ≤ u := le_of_lt hu.1
    have hu2 : u ≤ 1 := hu.2
    calc ‖En u * W u‖ ≤ ‖En u‖ * ‖W u‖ := le_of_eq (norm_mul _ _)
      _ ≤ (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
            * (Real.pi ^ m * (1 + τ.im) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1)))) :=
          mul_le_mul (hEnbd u hu1 hu2) (hWbd u hu1 hu2) (norm_nonneg _) (by positivity)

  -- ## bounds for the two pole contributions
  have hε₁ : τ.re - 1 ≠ 0 := by linarith
  have hε₂ : τ.re + 1 ≠ 0 := by linarith
  have hp1 : ‖∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u‖
      ≤ (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
        * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
    have hcongr : (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)
        = (-Complex.I) * ((-(Real.pi : ℂ)) ^ m) *
          (∫ u in (-1 : ℝ)..1, ((u : ℂ) + ((τ.re - 1 : ℝ) : ℂ) * Complex.I)⁻¹
              * ((τ.im : ℂ) + (u : ℂ)) ^ m
              * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      simp only [It1, W]
      exact spike_term1 τ x m u
    rw [hcongr, norm_mul, norm_mul]
    have hnormI : ‖(-Complex.I : ℂ)‖ = 1 := by rw [norm_neg, Complex.norm_I]
    have hnormpi : ‖((-(Real.pi : ℂ)) ^ m)‖ = Real.pi ^ m := by
      rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnormI, one_mul, hnormpi]
    have hm := spikePoleQ Cm hmodel m τ.im x (by linarith) hx (τ.re - 1) hε₁
    calc Real.pi ^ m * ‖∫ u in (-1 : ℝ)..1, ((u : ℂ) + ((τ.re - 1 : ℝ) : ℂ) * Complex.I)⁻¹
            * ((τ.im : ℂ) + (u : ℂ)) ^ m
            * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))‖
        ≤ Real.pi ^ m * (max Cm 8 * (1 + τ.im) ^ m
            * Real.exp (-(Real.pi * x * (τ.im - 1)))) :=
          mul_le_mul_of_nonneg_left hm (pow_nonneg Real.pi_pos.le m)
      _ = (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
            * Real.exp (-(Real.pi * x * (τ.im - 1))) := by ring
  have hp2 : ‖∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u‖
      ≤ (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
        * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
    have hcongr : (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)
        = (-Complex.I) * ((-(Real.pi : ℂ)) ^ m) *
          (∫ u in (-1 : ℝ)..1, ((u : ℂ) + ((τ.re + 1 : ℝ) : ℂ) * Complex.I)⁻¹
              * ((τ.im : ℂ) + (u : ℂ)) ^ m
              * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      simp only [It2, W]
      exact spike_term2 τ x m u
    rw [hcongr, norm_mul, norm_mul]
    have hnormI : ‖(-Complex.I : ℂ)‖ = 1 := by rw [norm_neg, Complex.norm_I]
    have hnormpi : ‖((-(Real.pi : ℂ)) ^ m)‖ = Real.pi ^ m := by
      rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnormI, one_mul, hnormpi]
    have hm := spikePoleQ Cm hmodel m τ.im x (by linarith) hx (τ.re + 1) hε₂
    calc Real.pi ^ m * ‖∫ u in (-1 : ℝ)..1, ((u : ℂ) + ((τ.re + 1 : ℝ) : ℂ) * Complex.I)⁻¹
            * ((τ.im : ℂ) + (u : ℂ)) ^ m
            * Complex.exp (-(↑(Real.pi * x) : ℂ) * ((τ.im : ℂ) + (u : ℂ)))‖
        ≤ Real.pi ^ m * (max Cm 8 * (1 + τ.im) ^ m
            * Real.exp (-(Real.pi * x * (τ.im - 1)))) :=
          mul_le_mul_of_nonneg_left hm (pow_nonneg Real.pi_pos.le m)
      _ = (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
            * Real.exp (-(Real.pi * x * (τ.im - 1))) := by ring

  -- ## the `En · W` contribution
  have hpe : ‖∫ u in (-1 : ℝ)..1, En u * W u‖
      ≤ 2 * (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
        * (Real.pi ^ m * (1 + τ.im) ^ m) * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1)
      (C := (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
        * (Real.pi ^ m * (1 + τ.im) ^ m * Real.exp (-(Real.pi * x * (τ.im - 1)))))
      (f := fun u : ℝ => En u * W u) ?_
    · rw [show (1 : ℝ) - (-1) = 2 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
      refine le_trans hb (le_of_eq ?_)
      ring
    · intro u hu
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
      have hu1 : -1 ≤ u := le_of_lt hu.1
      have hu2 : u ≤ 1 := hu.2
      refine le_trans (le_of_eq (norm_mul _ _)) ?_
      refine le_trans (mul_le_mul (hEnbd u hu1 hu2) (hWbd u hu1 hu2) (norm_nonneg _) ?_) ?_
      · positivity
      · exact le_of_eq (by ring)

  have hlin : (∫ u in (-1 : ℝ)..1, Aint u * W u)
      = c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)
        + c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)
        + (∫ u in (-1 : ℝ)..1, En u * W u) := by
    rw [show (∫ u in (-1 : ℝ)..1, Aint u * W u)
        = ∫ u in (-1 : ℝ)..1,
            (c₁ * ((It1 u)⁻¹ * W u) + c₂ * ((It2 u)⁻¹ * W u) + En u * W u) by
      apply intervalIntegral.integral_congr
      intro u _
      exact hpoint u]
    rw [intervalIntegral.integral_add ((hInt1.const_mul c₁).add (hInt2.const_mul c₂)) hintEn,
      intervalIntegral.integral_add (hInt1.const_mul c₁) (hInt2.const_mul c₂),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hfinal : ‖∫ u in (-1 : ℝ)..1, Aint u * W u‖
      ≤ ((‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
          + 2 * (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
              * (Real.pi ^ m * (1 + τ.im) ^ m))
        * Real.exp (-(Real.pi * x * (τ.im - 1))) := by
    rw [hlin]
    have h1 : ‖c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)‖
        ≤ ‖c₁‖ * ((Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
            * Real.exp (-(Real.pi * x * (τ.im - 1)))) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hp1 (norm_nonneg _)
    have h2 : ‖c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)‖
        ≤ ‖c₂‖ * ((Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
            * Real.exp (-(Real.pi * x * (τ.im - 1)))) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
    have h3 : ‖∫ u in (-1 : ℝ)..1, En u * W u‖
        ≤ 2 * ((Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
            * (Real.pi ^ m * (1 + τ.im) ^ m)
            * Real.exp (-(Real.pi * x * (τ.im - 1)))) :=
      le_trans hpe (le_of_eq (by ring))
    calc ‖c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)
            + c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)
            + (∫ u in (-1 : ℝ)..1, En u * W u)‖
        ≤ ‖c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)
              + c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)‖
            + ‖∫ u in (-1 : ℝ)..1, En u * W u‖ := norm_add_le _ _
      _ ≤ (‖c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u)‖
              + ‖c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u)‖)
            + ‖∫ u in (-1 : ℝ)..1, En u * W u‖ := by
          have hh := norm_add_le (c₁ * (∫ u in (-1 : ℝ)..1, (It1 u)⁻¹ * W u))
            (c₂ * (∫ u in (-1 : ℝ)..1, (It2 u)⁻¹ * W u))
          linarith
      _ ≤ (‖c₁‖ * ((Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
              * Real.exp (-(Real.pi * x * (τ.im - 1))))
            + ‖c₂‖ * ((Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
              * Real.exp (-(Real.pi * x * (τ.im - 1)))))
          + 2 * ((Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
              * (Real.pi ^ m * (1 + τ.im) ^ m)
              * Real.exp (-(Real.pi * x * (τ.im - 1)))) := by
          linarith [h1, h2, h3]
      _ = ((‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
          + 2 * (Cc * (Work.Kernels.scale τ) ^ Nd * (2 + τ.im) ^ M)
              * (Real.pi ^ m * (1 + τ.im) ^ m))
        * Real.exp (-(Real.pi * x * (τ.im - 1))) := by ring

  -- ## final arithmetic
  have hS1y : 1 + τ.im ≤ Work.Kernels.scale τ := by
    have h1 : τ.im ≤ ‖((τ : ℂ))‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ))
      rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
      exact h
    have h2 : ‖((τ : ℂ))‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
    have h3 : (0 : ℝ) ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
    simp only [Work.Kernels.scale]
    linarith
  have hS2 : 1 + τ.im ≤ 2 * Work.Kernels.scale τ := by linarith
  have hS3 : 2 + τ.im ≤ 3 * Work.Kernels.scale τ := by linarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hmax : (0 : ℝ) ≤ max Cm 8 := le_trans (by norm_num) (le_max_right Cm 8)
  have hpm : Real.pi ^ m ≤ Real.pi ^ l := pow_le_pow_right₀ hpi1 hm
  have h1yl : (1 + τ.im) ^ m ≤ (2 * Work.Kernels.scale τ) ^ l :=
    le_trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + τ.im) hm)
      (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + τ.im) hS2 l)
  have h1yS : (1 + τ.im) ^ m ≤ ((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ (l : ℝ) := by
    refine le_trans h1yl ?_
    rw [mul_pow, Real.rpow_natCast (Work.Kernels.scale τ) l]
  have hT1 : (‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
      ≤ (2 * Cc * Real.pi ^ l * max Cm 8 * ((2 : ℝ) ^ l)) * Work.Kernels.scale τ ^ N := by
    have hA1 : ‖c₁‖ + ‖c₂‖ ≤ 2 * Cc := by linarith
    have hinner : Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m
        ≤ (Real.pi ^ l * max Cm 8) * (((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ (l : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul hpm le_rfl hmax (pow_nonneg Real.pi_pos.le l)
      · exact h1yS
      · positivity
      · exact mul_nonneg (pow_nonneg Real.pi_pos.le l) hmax
    calc (‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
        ≤ (2 * Cc) * ((Real.pi ^ l * max Cm 8) * (((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ (l : ℝ))) :=
          mul_le_mul hA1 hinner (by positivity) (by positivity)
      _ ≤ (2 * Cc) * ((Real.pi ^ l * max Cm 8) * (((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left (l : ℝ) (Nd + M + l)))
            (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ l)
      _ = (2 * Cc * Real.pi ^ l * max Cm 8 * ((2 : ℝ) ^ l)) * Work.Kernels.scale τ ^ N := by ring
  have hT2 : 2 * (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
        * (Real.pi ^ m * (1 + τ.im) ^ m)
      ≤ (2 * Cc * ((3 : ℝ) ^ M) * Real.pi ^ l * ((2 : ℝ) ^ l)) * Work.Kernels.scale τ ^ N := by
    have h2m : (2 + τ.im) ^ M ≤ ((3 : ℝ) ^ M) * Work.Kernels.scale τ ^ M := by
      refine le_trans (Real.rpow_le_rpow (by linarith) hS3 hM) ?_
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hSp.le]
    have hinner : (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
          * (Real.pi ^ m * (1 + τ.im) ^ m)
        ≤ (Cc * Work.Kernels.scale τ ^ Nd * (((3 : ℝ) ^ M) * Work.Kernels.scale τ ^ M))
          * (Real.pi ^ l * (((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ (l : ℝ))) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact le_rfl
        · exact h2m
        · positivity
        · exact mul_nonneg hCc.le (Real.rpow_nonneg hSp.le Nd)
      · exact mul_le_mul hpm h1yS (by positivity) (pow_nonneg Real.pi_pos.le l)
      · positivity
      · exact mul_nonneg (mul_nonneg hCc.le (Real.rpow_nonneg hSp.le Nd))
          (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) M) (Real.rpow_nonneg hSp.le M))
    calc 2 * (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
            * (Real.pi ^ m * (1 + τ.im) ^ m)
        = 2 * ((Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
            * (Real.pi ^ m * (1 + τ.im) ^ m)) := by ring
      _ ≤ 2 * ((Cc * Work.Kernels.scale τ ^ Nd * (((3 : ℝ) ^ M) * Work.Kernels.scale τ ^ M))
            * (Real.pi ^ l * (((2 : ℝ) ^ l) * Work.Kernels.scale τ ^ (l : ℝ)))) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = (2 * Cc * ((3 : ℝ) ^ M) * Real.pi ^ l * ((2 : ℝ) ^ l))
            * (Work.Kernels.scale τ ^ Nd * Work.Kernels.scale τ ^ M
              * Work.Kernels.scale τ ^ (l : ℝ)) := by ring
      _ = (2 * Cc * ((3 : ℝ) ^ M) * Real.pi ^ l * ((2 : ℝ) ^ l))
            * Work.Kernels.scale τ ^ (Nd + M + (l : ℝ)) := by
          rw [← Real.rpow_add hSp, ← Real.rpow_add hSp]
      _ ≤ (2 * Cc * ((3 : ℝ) ^ M) * Real.pi ^ l * ((2 : ℝ) ^ l)) * Work.Kernels.scale τ ^ N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right (l : ℝ) (Nd + M + l))
  have hK : (‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
        + 2 * (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
            * (Real.pi ^ m * (1 + τ.im) ^ m) ≤ A * Work.Kernels.scale τ ^ N := by
    refine le_trans (add_le_add hT1 hT2) (le_of_eq ?_)
    dsimp only [A]
    ring
  have he1 : Real.exp (-(Real.pi * x * (τ.im - 1))) ≤ Real.exp (-(Real.pi * x)) := by
    apply Real.exp_le_exp.mpr
    have : Real.pi * x * 1 ≤ Real.pi * x * (τ.im - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ Real.pi * x)
      linarith
    linarith
  calc ‖∫ u in (-1 : ℝ)..1, Aint u * W u‖
      ≤ ((‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
          + 2 * (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
              * (Real.pi ^ m * (1 + τ.im) ^ m))
        * Real.exp (-(Real.pi * x * (τ.im - 1))) := hfinal
    _ ≤ ((‖c₁‖ + ‖c₂‖) * (Real.pi ^ m * max Cm 8 * (1 + τ.im) ^ m)
          + 2 * (Cc * Work.Kernels.scale τ ^ Nd * (2 + τ.im) ^ M)
              * (Real.pi ^ m * (1 + τ.im) ^ m))
        * Real.exp (-(Real.pi * x)) :=
        mul_le_mul_of_nonneg_left he1 (by positivity)
    _ ≤ (A * Work.Kernels.scale τ ^ N) * Real.exp (-(Real.pi * x)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ = A * Work.Kernels.scale τ ^ N * Real.exp (-(Real.pi * x)) := by ring

end SpikeModel

/-- `sinSq s = 2 - 2cos(π s²)` written with a real cosine. -/
lemma spike_sinSq_eq_two_sub_two_cos (s : ℝ) :
    Work.Asymptotics.sinSq s = (2 - 2 * ↑(Real.cos (Real.pi * s ^ 2)) : ℂ) := by
  have hsin : Complex.sin ((Real.pi : ℂ) * (s : ℂ) ^ 2 / 2)
      = ↑(Real.sin (Real.pi * s ^ 2 / 2)) := by
    rw [show (Real.pi : ℂ) * (s : ℂ) ^ 2 / 2 = ((Real.pi * s ^ 2 / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_sin]
  rw [Work.Asymptotics.sinSq, hsin]
  have h : Real.sin (Real.pi * s ^ 2 / 2) ^ 2 = (1 - Real.cos (Real.pi * s ^ 2)) / 2 := by
    have hc := Real.cos_two_mul (Real.pi * s ^ 2 / 2)
    rw [show 2 * (Real.pi * s ^ 2 / 2) = Real.pi * s ^ 2 by ring] at hc
    have hsq := Real.sin_sq (Real.pi * s ^ 2 / 2)
    rw [hsq]
    linarith [hc]
  have h1 : (4 : ℂ) * ↑(Real.sin (Real.pi * s ^ 2 / 2)) ^ 2
      = 4 * ↑(Real.sin (Real.pi * s ^ 2 / 2) ^ 2) := by
    rw [Complex.ofReal_pow]
  rw [h1, h]
  push_cast
  ring

/-- **Seminorm bound for the spike piece of the funnel layer.** -/
theorem funnelSpikeSeminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.Funnel τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r‖ ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨c₀, hc₀, H⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  obtain ⟨A, N, hA0, hN0, hbound⟩ := spikeIteratedDeriv_bound ℓ d hd l
  refine ⟨c₀ * A, N, by positivity, hN0, ?_⟩
  intro τ r hτ
  have hcd : ContDiffOn ℝ (l : WithTop ℕ∞) (spikeT ℓ d τ) (Set.Ioi (-1)) := by
    obtain ⟨B, hB0, hBw⟩ := spikeWindow_bound ℓ d hd τ hτ
    have hab : τ.im - 1 ≤ τ.im + 1 := by linarith
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        (volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))) :=
      (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
    have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ B := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact hBw t (le_of_lt ht.1) ht.2
    have hfun : spikeT ℓ d τ = fun y : ℝ => ∫ t in (τ.im - 1)..(τ.im + 1),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      funext y
      rw [spikeT]
      apply intervalIntegral.integral_congr
      intro t _
      show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * wgt y t
        = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ)
      rw [wgt_apply, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hfun]
    exact contDiffOn_intervalIntegral_exp_bound _ _ _ hab hmeas hB0 hbd l
  have hFb : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (spikeT ℓ d τ) x‖
        ≤ (A * Work.Kernels.scale τ ^ N) * Real.exp (-(Real.pi * x)) := by
    intro m hm x hx
    calc ‖iteratedDeriv m (spikeT ℓ d τ) x‖
        ≤ A * Work.Kernels.scale τ ^ N * Real.exp (-(Real.pi * x)) := hbound τ hτ m hm x hx
      _ = (A * Work.Kernels.scale τ ^ N) * Real.exp (-(Real.pi * x)) := by ring
  have key := H (spikeT ℓ d τ) (A * Work.Kernels.scale τ ^ N)
    (mul_nonneg hA0 (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N)) hcd hFb r
  rw [show (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s ^ 2))
      = (fun s : ℝ => (2 - 2 * ↑(Real.cos (Real.pi * s ^ 2)))
          * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) by
    funext s
    rw [spike_sinSq_eq_two_sub_two_cos]]
  exact le_trans key (le_of_eq (by ring))

end Work.Asymptotics
