/-
# The `r`-seminorm of the tail piece `tangTail` of the tangency layer

`tangTail ℓ d τ x = ∫_{3/2}^∞ (K - Aexp)(τ,it)e^{-πxt}dt`.  By the cusp expansion
`Work.Asymptotics.HalfFunnel.tangTailExpansion` the amplitude `K - Aexp` decays like
`(1+t)^M e^{-πt}`, so the tail integral is well behaved for every `x > -1`, differentiating under
the integral sign multiplies the amplitude by `(-πt)^m`, and the resulting bound
`C π^m t^{M+m} e^{-πt}` yields the decay `e^{-3πx/2} ≤ C (1+x)^{-N}`.

The differentiation-under-the-integral-sign lemmas are the `Ioi (3/2)` analogues of the
`tailIntegral` lemmas of `Submission/Work/Asymptotics/TailIntegral.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.HFN.HalfFunnel.tangTailExpansion
import Submission.Work.HFN.HalfFunnel.tangADeriv
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

lemma norm_ofReal_eq_abs' (r : ℝ) : ‖(r : ℂ)‖ = |r| := Complex.norm_real r

/-- Integrability of the tail integrand on `(3/2,∞)` for `x > -1`. -/
private lemma integrableOn_Ioi_tail (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (3 / 2 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    {x : ℝ} (hx : -1 < x) :
    IntegrableOn (fun t : ℝ => g t * (Real.exp (-(Real.pi * x * t)) : ℂ))
      (Set.Ioi (3 / 2 : ℝ)) := by
  have hcpos : 0 < Real.pi * (x + 1) := mul_pos Real.pi_pos (by linarith)
  have hmaj : Integrable (fun t : ℝ => C * t ^ M * Real.exp (-(Real.pi * (x + 1) * t)))
      (volume.restrict (Set.Ioi (3 / 2 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_Ioi_pos M (a := 3 / 2)
      (d := Real.pi * (x + 1)) (by norm_num) hcpos
    simpa only [mul_assoc] using h1.const_mul C
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (Real.exp (-(Real.pi * x * t)) : ℂ)).aestronglyMeasurable
  · filter_upwards [hb] with t hb
    have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * x * t))
        = Real.exp (-(Real.pi * (x + 1) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖g t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        = ‖g t‖ * Real.exp (-(Real.pi * x * t)) := by
          rw [norm_mul, norm_ofReal_eq_abs', abs_of_pos (Real.exp_pos _)]
      _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * x * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = C * t ^ M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * x * t))) := by ring
      _ = C * t ^ M * Real.exp (-(Real.pi * (x + 1) * t)) := by rw [hexp]

/-- The a.e. bound for the amplitude `t ↦ g t · (-πt)^m`. -/
private lemma amp_ae_bound (g : ℝ → ℂ) {C M : ℝ}
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) (m : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m‖
        ≤ C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
  filter_upwards [hb, ae_restrict_mem measurableSet_Ioi] with t hb ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * t := by
    rw [norm_ofReal_eq_abs', abs_of_neg (by have := mul_pos Real.pi_pos ht0; linarith)]
    ring
  have htM : t ^ (M + (m : ℝ)) = t ^ M * t ^ (m : ℝ) := Real.rpow_add ht0 M _
  have htm : t ^ (m : ℝ) = t ^ m := Real.rpow_natCast t m
  calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m‖ = ‖g t‖ * (Real.pi * t) ^ m := by
        rw [norm_mul, norm_pow, hfac]
    _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t) ^ m :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
        rw [mul_pow, htM, htm]; ring

/-- Differentiation under the integral sign on `(3/2,∞)`. -/
private lemma hasDerivAt_Ioi_tail (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (3 / 2 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
      (∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ)) x := by
  set r : ℝ := (x + 1) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hcpos : 0 < Real.pi * (x - r + 1) := mul_pos Real.pi_pos (by rw [hrdef]; linarith)
  have hmajor : Integrable
      (fun t : ℝ => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (x - r + 1) * t)))
      (volume.restrict (Set.Ioi (3 / 2 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_Ioi_pos (M + 1) (a := 3 / 2)
      (d := Real.pi * (x - r + 1)) (by norm_num) hcpos
    simpa only [mul_assoc] using h1.const_mul (C * Real.pi)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (3 / 2 : ℝ)))
    (F := fun y (t : ℝ) => g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (F' := fun y (t : ℝ) =>
      g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ))
    (x₀ := x) (s := Metric.ball x r)
    (bound := fun t : ℝ => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (x - r + 1) * t)))
    (Metric.ball_mem_nhds x hr) ?_ ?_ ?_ ?_ hmajor ?_).2
  · exact Filter.Eventually.of_forall (fun y => hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (Real.exp (-(Real.pi * y * t)) : ℂ)).aestronglyMeasurable)
  · exact integrableOn_Ioi_tail g hmeas hC hb hx
  · exact (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (((-(Real.pi * t) : ℝ)) : ℂ)).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ =>
        (Real.exp (-(Real.pi * x * t)) : ℂ)).aestronglyMeasurable
  · filter_upwards [hb, ae_restrict_mem measurableSet_Ioi] with t hb ht y hy
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have hxd : |y - x| < r := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
    have hyr : x - r < y := by have h' := (abs_lt.mp hxd).1; linarith
    have hexple : Real.exp (-(Real.pi * y * t)) ≤ Real.exp (-(Real.pi * (x - r) * t)) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * (x - r) * t ≤ Real.pi * y * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyr.le Real.pi_pos.le) ht0.le
      linarith
    have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * t := by
      rw [norm_ofReal_eq_abs', abs_of_neg (by have := mul_pos Real.pi_pos ht0; linarith)]
      ring
    have hexpn : ‖(Real.exp (-(Real.pi * y * t)) : ℂ)‖ = Real.exp (-(Real.pi * y * t)) := by
      rw [norm_ofReal_eq_abs', abs_of_pos (Real.exp_pos _)]
    have htM : t ^ (M + 1) = t ^ M * t ^ (1 : ℝ) := Real.rpow_add ht0 M 1
    have ht1 : t ^ (1 : ℝ) = t := Real.rpow_one t
    calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ)‖
        = ‖g t‖ * (Real.pi * t) * Real.exp (-(Real.pi * y * t)) := by
          rw [norm_mul, norm_mul, hfac, hexpn]
      _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t)
            * Real.exp (-(Real.pi * (x - r) * t)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hb (by positivity)) hexple
            (Real.exp_pos _).le (by positivity)
      _ = C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (x - r + 1) * t)) := by
          rw [htM, ht1]
          have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * (x - r) * t))
              = Real.exp (-(Real.pi * (x - r + 1) * t)) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * t ^ M * Real.exp (-(Real.pi * t)) * (Real.pi * t)
                * Real.exp (-(Real.pi * (x - r) * t))
              = C * Real.pi * (t ^ M * t) * (Real.exp (-(Real.pi * t))
                * Real.exp (-(Real.pi * (x - r) * t))) := by ring
            _ = C * Real.pi * (t ^ M * t)
                * Real.exp (-(Real.pi * (x - r + 1) * t)) := by rw [hexp]
  · refine Filter.Eventually.of_forall (fun t y _ => ?_)
    have h1 : HasDerivAt (fun z : ℝ => Real.exp (-(Real.pi * z * t)))
        (Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))) y := by
      have h2 : HasDerivAt (fun z : ℝ => -(Real.pi * z * t)) (-(Real.pi * t)) y := by
        have h3 : (fun z : ℝ => -(Real.pi * z * t)) = fun z : ℝ => (-(Real.pi * t)) * z := by
          funext z; ring
        rw [h3]
        simpa using (hasDerivAt_id y).const_mul (-(Real.pi * t))
      simpa using h2.exp
    have h5 := (h1.ofReal_comp).const_mul (g t)
    have heq : g t * (↑(Real.exp (-(Real.pi * y * t)) * (-(Real.pi * t))))
        = g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
      push_cast; ring
    rwa [heq] at h5

/-- The iterated derivative of the tail integral on `(3/2,∞)`. -/
private lemma iteratedDeriv_Ioi_tail (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (3 / 2 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) (m : ℕ) :
    ∀ x : ℝ, -1 < x → iteratedDeriv m (fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (Real.exp (-(Real.pi * y * t)) : ℂ)) x
      = ∫ t in Set.Ioi (3 / 2 : ℝ),
          g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
  induction m with
  | zero =>
      intro x _
      simp [iteratedDeriv_zero]
  | succ k ih =>
      intro x hx
      set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hG
      have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
        hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
          (((-(Real.pi * t) : ℝ)) : ℂ) ^ k).aestronglyMeasurable
      have hGbound := amp_ae_bound g hb k
      have hev : iteratedDeriv k (fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
            g t * (Real.exp (-(Real.pi * y * t)) : ℂ))
          =ᶠ[𝓝 x] (fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
            G t * (Real.exp (-(Real.pi * y * t)) : ℂ)) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) (fun y hy => ih y hy)
      rw [iteratedDeriv_succ, hev.deriv_eq,
        (hasDerivAt_Ioi_tail G hGmeas (by positivity) hGbound hx).deriv]
      congr 1
      funext t
      simp only [hG]
      rw [pow_succ]
      ring

/-- **Growth bound for the iterated derivatives of the tail integral.** -/
private lemma norm_iteratedDeriv_Ioi_tail_bound (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (3 / 2 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖iteratedDeriv m (fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (Real.exp (-(Real.pi * y * t)) : ℂ)) x‖
      ≤ C * Real.pi ^ m * (∫ t in Set.Ioi (3 / 2 : ℝ), t ^ (M + (m : ℝ))
          * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * (3 / 2) * x)) := by
  set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
    hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
  have hmaj : Integrable (fun t : ℝ => C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x))
      * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))))
      (volume.restrict (Set.Ioi (3 / 2 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_Ioi_pos (M + m) (a := 3 / 2)
      (d := Real.pi) (by norm_num) Real.pi_pos
    simpa only [mul_assoc] using h1.const_mul (C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x)))
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖G t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        ≤ C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x))
          * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) := by
    filter_upwards [amp_ae_bound g hb m, ae_restrict_mem measurableSet_Ioi] with t ht ht1
    have ht0 : 0 < t := lt_trans (by norm_num) ht1
    have ht32 : (3 / 2 : ℝ) ≤ t := le_of_lt ht1
    have hexp : Real.exp (-(Real.pi * x * t)) ≤ Real.exp (-(Real.pi * (3 / 2) * x)) := by
      apply Real.exp_le_exp.mpr
      have h2 : (3 / 2 : ℝ) * x ≤ x * t := by
        rw [mul_comm ((3 : ℝ) / 2) x]
        exact mul_le_mul_of_nonneg_left ht32 hx
      have h1 : Real.pi * ((3 / 2 : ℝ) * x) ≤ Real.pi * (x * t) :=
        mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
      nlinarith [h1]
    calc ‖G t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        = ‖G t‖ * Real.exp (-(Real.pi * x * t)) := by
          rw [norm_mul, norm_ofReal_eq_abs', abs_of_pos (Real.exp_pos _)]
      _ ≤ (C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))
            * Real.exp (-(Real.pi * (3 / 2) * x)) := mul_le_mul ht hexp (Real.exp_pos _).le (by positivity)
      _ = C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x))
            * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) := by ring
  have hnorm_int : IntegrableOn
      (fun t : ℝ => ‖G t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖) (Set.Ioi (3 / 2 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun t : ℝ => ‖G t * (Real.exp (-(Real.pi * x * t)) : ℂ)‖)
      (g := fun t : ℝ => C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x))
        * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))) hmaj ?_ ?_
    · exact ((hGmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (Real.exp (-(Real.pi * x * t)) : ℂ)).aestronglyMeasurable)).norm
    · filter_upwards [hpoint] with t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [iteratedDeriv_Ioi_tail g hmeas hC hM hb m x (by linarith)]
  calc ‖∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
      ≤ ∫ t in Set.Ioi (3 / 2 : ℝ),
          ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m
            * (Real.exp (-(Real.pi * x * t)) : ℂ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (3 / 2 : ℝ), C * Real.pi ^ m * Real.exp (-(Real.pi * (3 / 2) * x))
          * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) :=
        integral_mono_ae hnorm_int hmaj hpoint
    _ = C * Real.pi ^ m * (∫ t in Set.Ioi (3 / 2 : ℝ),
          t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * (3 / 2) * x)) := by
        rw [MeasureTheory.integral_const_mul]
        ring

/-- **Smoothness of the tail integral on `(3/2,∞)`.** -/
lemma contDiffOn_Ioi_tail (n : ℕ) (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (3 / 2 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℝ (n : ℕ∞ω) (fun x : ℝ => (∫ t in Set.Ioi (3 / 2 : ℝ),
      g t * (Real.exp (-(Real.pi * x * t)) : ℂ))) (Set.Ioi (-1)) := by
  refine contDiffOn_of_continuousOn_differentiableOn_deriv (n := (n : ℕ∞)) ?_ ?_
  · intro m hm
    have hmn : m ≤ n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have hGbound := amp_ae_bound g hb m
    have hGdiff : DifferentiableOn ℝ (fun x : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
        G t * (Real.exp (-(Real.pi * x * t)) : ℂ)) (Set.Ioi (-1)) := fun lam hlam =>
      (hasDerivAt_Ioi_tail G hGmeas (by positivity) hGbound hlam).differentiableAt.differentiableWithinAt
    refine hGdiff.continuousOn.congr ?_
    intro x hx
    show iteratedDerivWithin m (fun x : ℝ => (∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (Real.exp (-(Real.pi * x * t)) : ℂ))) (Set.Ioi (-1)) x
      = ∫ t in Set.Ioi (3 / 2 : ℝ), G t * (Real.exp (-(Real.pi * x * t)) : ℂ)
    rw [iteratedDerivWithin_of_isOpen (n := m) (f := fun x : ℝ => (∫ t in Set.Ioi (3 / 2 : ℝ),
      g t * (Real.exp (-(Real.pi * x * t)) : ℂ))) isOpen_Ioi hx,
      iteratedDeriv_Ioi_tail g hmeas hC hM hb m x hx, hG]
  · intro m hm
    have hmn : m < n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have hGbound := amp_ae_bound g hb m
    have hGdiff : DifferentiableOn ℝ (fun x : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
        G t * (Real.exp (-(Real.pi * x * t)) : ℂ)) (Set.Ioi (-1)) := fun lam hlam =>
      (hasDerivAt_Ioi_tail G hGmeas (by positivity) hGbound hlam).differentiableAt.differentiableWithinAt
    refine hGdiff.congr fun x hx => ?_
    show iteratedDerivWithin m (fun x : ℝ => (∫ t in Set.Ioi (3 / 2 : ℝ),
        g t * (Real.exp (-(Real.pi * x * t)) : ℂ))) (Set.Ioi (-1)) x
      = ∫ t in Set.Ioi (3 / 2 : ℝ), G t * (Real.exp (-(Real.pi * x * t)) : ℂ)
    rw [iteratedDerivWithin_of_isOpen (n := m) (f := fun x : ℝ => (∫ t in Set.Ioi (3 / 2 : ℝ),
      g t * (Real.exp (-(Real.pi * x * t)) : ℂ))) isOpen_Ioi hx,
      iteratedDeriv_Ioi_tail g hmeas hC hM hb m x hx, hG]

theorem tangTailDeriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ m : ℕ, ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (x : ℝ),
      τ ∈ ctanRegion → 0 ≤ x →
      ‖iteratedDeriv m (tangTail ℓ d τ) x‖
        ≤ C * (1 + x) ^ (-N) := by
  intro m N hN
  obtain ⟨Ct, Mt, T₀, hCt, hMt, hT₀, htail⟩ := tangTailExpansion ℓ d hd
  obtain ⟨Kc, hKc0, hKc⟩ := exp_neg_le_rpow_neg N hN
  set C' : ℝ := Ct * 2 ^ Mt * Real.exp (Real.pi * T₀) with hC'
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  refine ⟨C' * Real.pi ^ m * max (∫ t in Set.Ioi (3 / 2 : ℝ),
      t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t))) 0 * Kc, by positivity,
    fun τ x hτ hx => ?_⟩
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  -- the amplitude bound for `K - Aexp`
  have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ C' * t ^ Mt * Real.exp (-(Real.pi * t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := lt_trans (by norm_num) ht
    have ht0 : 0 < t := by linarith
    have h1 := htail τ t hτcl (le_of_lt ht)
    have h2 : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
      have h := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + t)
        (by linarith : 1 + t ≤ 2 * t) hMt
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ t)] at h
    have h4 : Real.exp (-(Real.pi * (t - T₀))) = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h4] at h1
    calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := h1
      _ ≤ Ct * (2 ^ Mt * t ^ Mt) * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_left h2 hCt.le
      _ = C' * t ^ Mt * Real.exp (-(Real.pi * t)) := by rw [hC']; ring
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
      (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
    ((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      ((continuous_Aexp_tang ℓ d hd).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  -- identify `tangTail` with the standard tail integral
  have hfuneq : tangTail ℓ d τ = fun y : ℝ => ∫ t in Set.Ioi (3 / 2 : ℝ),
      (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [tangTail]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [tangGauss, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfuneq]
  have hstep := norm_iteratedDeriv_Ioi_tail_bound
    (fun t : ℝ => Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) hmeas hC'0 hMt hb m hx
  have hIle : (∫ t in Set.Ioi (3 / 2 : ℝ), t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t)))
      ≤ max (∫ t in Set.Ioi (3 / 2 : ℝ), t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t))) 0 :=
    le_max_left _ _
  have hexp : Real.exp (-(Real.pi * (3 / 2) * x)) ≤ Kc * (1 + x) ^ (-N) := by
    have h1 : Real.exp (-(Real.pi * x)) ≤ Kc * (1 + x) ^ (-N) := hKc x hx
    have h2 : Real.exp (-(Real.pi * (3 / 2) * x)) ≤ Real.exp (-(Real.pi * x)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hx]
    exact le_trans h2 h1
  refine le_trans hstep ?_
  have hI0 : (0 : ℝ) ≤ max (∫ t in Set.Ioi (3 / 2 : ℝ),
      t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t))) 0 := le_max_right _ _
  calc C' * Real.pi ^ m * (∫ t in Set.Ioi (3 / 2 : ℝ), t ^ (Mt + (m : ℝ))
        * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * (3 / 2) * x))
      ≤ C' * Real.pi ^ m * max (∫ t in Set.Ioi (3 / 2 : ℝ),
          t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t))) 0
          * (Kc * (1 + x) ^ (-N)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hIle (by positivity)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = C' * Real.pi ^ m * max (∫ t in Set.Ioi (3 / 2 : ℝ),
          t ^ (Mt + (m : ℝ)) * Real.exp (-(Real.pi * t))) 0 * Kc * (1 + x) ^ (-N) := by ring

end Work.HFN.HalfFunnel
