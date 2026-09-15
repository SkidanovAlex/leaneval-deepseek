import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.multilinear_intervalIntegral_apply

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter Metric
open scoped Interval

/-- Differentiation under the integral sign for interval integrals: for a family
`f : E → ℝ → G` of `C^1` functions in the first variable, continuously depending on the
integration variable, the Fréchet derivative of `y ↦ ∫ s in a..b, f y s` is the integral of
the derivative. -/
theorem hasFDerivAt_intervalIntegral_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : E → ℝ → G} {f' : E → ℝ → E →L[ℝ] G} {a b : ℝ} {x : E}
    (hf : Continuous (Function.uncurry f))
    (hf' : Continuous (Function.uncurry f'))
    (h_diff : ∀ y s, HasFDerivAt (fun y => f y s) (f' y s) y) :
    HasFDerivAt (fun y => ∫ s in a..b, f y s) (∫ s in a..b, f' x s) x := by
  have hcont : Continuous fun p : ℝ × E => ‖f' p.2 p.1‖ :=
    (hf'.comp continuous_swap).norm
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
      hcont.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (s := ball x 1) (bound := fun _ => C) (ball_mem_nhds x one_pos)
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards with y
    exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht y hy
    have hp : (t, y) ∈ uIcc a b ×ˢ closedBall x 1 :=
      ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hy⟩
    simpa using hC (t, y) hp
  · filter_upwards with t ht y hy
    exact h_diff y t

/-- One-dimensional differentiation under the integral sign for real-valued integrands. -/
lemma hasDerivAt_intervalIntegral_of_continuous
    {f : ℝ → ℝ → ℝ} {f' : ℝ → ℝ → ℝ} {a b : ℝ} {t₀ : ℝ}
    (hf : Continuous (Function.uncurry f))
    (hf' : Continuous (Function.uncurry f'))
    (h_diff : ∀ t s, HasDerivAt (fun t => f t s) (f' t s) t) :
    HasDerivAt (fun t => ∫ s in a..b, f t s) (∫ s in a..b, f' t₀ s) t₀ := by
  have hcont : Continuous fun p : ℝ × ℝ => ‖f' p.1 p.2‖ := hf'.norm
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
      hcont.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := ball t₀ 1) (bound := fun _ => C) (x₀ := t₀) (ball_mem_nhds t₀ one_pos)
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards with t
    exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hf'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht x hx
    have hp : (x, t) ∈ closedBall t₀ 1 ×ˢ uIcc a b :=
      ⟨ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
    simpa using hC (x, t) hp
  · filter_upwards with t ht x hx
    exact h_diff x t

/-- Applying the currying linear equivalence to a continuous multilinear map is `curryLeft`. -/
lemma curryLeftEquiv_apply_eq_curryLeft {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) G) :
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G T = T.curryLeft := by
  ext v m
  rw [continuousMultilinearCurryLeftEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]

lemma comp_smul_one {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : E →L[ℝ] G) (s : ℝ) :
    A ∘SL (s • (1 : E →L[ℝ] E)) = s • A := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self, map_smul]

/-- The Fréchet derivative of `y ↦ D^k F (s • y)` is `s • curryLeft (D^{k+1} F (s y))`. -/
lemma hasFDerivAt_iteratedFDeriv_comp_const_smul
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {k : ℕ} (hF : ContDiff ℝ (k+1) F) (s : ℝ) (y : E) :
    HasFDerivAt (fun y => iteratedFDeriv ℝ k F (s • y))
      (s • continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G
        (iteratedFDeriv ℝ (k+1) F (s • y))) y := by
  have houter : HasFDerivAt (fun z => iteratedFDeriv ℝ k F z)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G
        (iteratedFDeriv ℝ (k+1) F (s • y))) (s • y) := by
    have hd : Differentiable ℝ (fun z => iteratedFDeriv ℝ k F z) :=
      hF.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
    have hh : HasFDerivAt (fun z => iteratedFDeriv ℝ k F z)
        (fderiv ℝ (fun z => iteratedFDeriv ℝ k F z) (s • y)) (s • y) :=
      (hd.differentiableAt (x := s • y)).hasFDerivAt
    rwa [fderiv_iteratedFDeriv, Function.comp_apply] at hh
  have hinner : HasFDerivAt (fun y : E => s • y) (s • (1 : E →L[ℝ] E)) y :=
    (hasFDerivAt_id y).const_smul s
  have h1 := houter.comp y hinner
  rwa [comp_smul_one] at h1

set_option maxHeartbeats 4000000 in
theorem iteratedFDeriv_intervalIntegral_comp_smul {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (φ : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hF : ContDiff ℝ n F) (hφ : Continuous φ)
    (x : EuclideanSpace ℝ (Fin d)) (m : Fin n → EuclideanSpace ℝ (Fin d)) :
    (iteratedFDeriv ℝ n (fun y => ∫ s in a..b, F (s • y) * φ s) x) m
      = ∫ s in a..b, (φ s * s ^ n) * (iteratedFDeriv ℝ n F (s • x)) m := by
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∫ s in a..b, F (s • y) * φ s
  have hcont_joint : ∀ (j : ℕ), (j : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) →
      Continuous (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
        (φ p.2 * p.2 ^ j) • iteratedFDeriv ℝ j F (p.2 • p.1)) := by
    intro j hj
    have hD : Continuous (fun z : EuclideanSpace ℝ (Fin d) => iteratedFDeriv ℝ j F z) :=
      (hF.of_le hj).continuous_iteratedFDeriv le_rfl
    exact ((hφ.comp continuous_snd).mul (continuous_snd.pow j)).smul
      (hD.comp (continuous_snd.smul continuous_fst))
  have hcont_joint' : ∀ (j : ℕ), ((j+1 : ℕ) : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) →
      Continuous (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
        (φ p.2 * p.2 ^ j) • (p.2 • continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (j+1) => EuclideanSpace ℝ (Fin d)) ℝ
          (iteratedFDeriv ℝ (j+1) F (p.2 • p.1)))) := by
    intro j hj
    have hD : Continuous (fun z : EuclideanSpace ℝ (Fin d) =>
        continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (j+1) => EuclideanSpace ℝ (Fin d)) ℝ
          (iteratedFDeriv ℝ (j+1) F z)) :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j+1) => EuclideanSpace ℝ (Fin d)) ℝ).continuous.comp
        ((hF.of_le hj).continuous_iteratedFDeriv (le_refl _))
    exact ((hφ.comp continuous_snd).mul (continuous_snd.pow j)).smul
      (continuous_snd.smul (hD.comp (continuous_snd.smul continuous_fst)))
  have hInt : ∀ (j : ℕ) (hj : (j : WithTop ℕ∞) ≤ (n : WithTop ℕ∞))
      (y : EuclideanSpace ℝ (Fin d)),
      IntervalIntegrable (fun s : ℝ => (φ s * s ^ j) • iteratedFDeriv ℝ j F (s • y))
        volume a b :=
    fun j hj y =>
      (hcont_joint j hj |>.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  have main : ∀ k, k ≤ n → ∀ (y : EuclideanSpace ℝ (Fin d)) (v : Fin k → EuclideanSpace ℝ (Fin d)),
      (iteratedFDeriv ℝ k g y) v
        = (∫ s in a..b, (φ s * s ^ k) • (iteratedFDeriv ℝ k F (s • y))) v := by
    intro k
    induction k with
    | zero =>
      intro hk y v
      change (∫ s in a..b, F (s • y) * φ s)
          = (∫ s in a..b, (φ s * s ^ 0) • (iteratedFDeriv ℝ 0 F (s • y))) v
      rw [multilinear_intervalIntegral_apply (hInt 0 (by simp : (0 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞)) y) v]
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [iteratedFDeriv_zero_apply, pow_zero, mul_one, smul_apply, smul_eq_mul]
      ring
    | succ k ih =>
      intro hk y v
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hkw : (k : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hk'
      have hkw1 : ((k+1 : ℕ) : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hk
      have hFk : ContDiff ℝ k F := hF.of_le hkw
      have hFk1 : ContDiff ℝ (k+1) F := hF.of_le hkw1
      have hfun : iteratedFDeriv ℝ k g = fun y' =>
          ∫ s in a..b, (φ s * s ^ k) • (iteratedFDeriv ℝ k F (s • y')) := by
        funext y'
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih hk' y' w
      have hpt : ∀ (y' : EuclideanSpace ℝ (Fin d)) (s : ℝ),
          HasFDerivAt (fun y'' : EuclideanSpace ℝ (Fin d) =>
              (φ s * s ^ k) • (iteratedFDeriv ℝ k F (s • y'')))
            ((φ s * s ^ k) • (s • continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (k+1) => EuclideanSpace ℝ (Fin d)) ℝ
              (iteratedFDeriv ℝ (k+1) F (s • y')))) y' :=
        fun y' s => (hasFDerivAt_iteratedFDeriv_comp_const_smul hFk1 s y').const_smul (φ s * s ^ k)
      have hGk :=
        hasFDerivAt_intervalIntegral_of_continuous (a := a) (b := b) (x := y) (hcont_joint k hkw) (hcont_joint' k hkw1) hpt
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) y := by
        rw [hfun]
        exact hGk.differentiableAt
      rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hdiff]
      -- relate `fderiv` to a one-dimensional derivative
      have hΦd : DifferentiableAt ℝ (fun y' : EuclideanSpace ℝ (Fin d) =>
          (iteratedFDeriv ℝ k g y') (Fin.tail v)) y :=
        (ContinuousLinearMap.differentiableAt (ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ (Fin.tail v))).comp y hdiff
      have hcurve : HasDerivAt (fun t : ℝ => y + t • (v 0)) (v 0) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t • (v 0)) (v 0) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const (v 0)
        simpa using h1.const_add y
      have hΦ2 : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin d) =>
            (iteratedFDeriv ℝ k g y') (Fin.tail v))
          (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) =>
            (iteratedFDeriv ℝ k g y') (Fin.tail v)) y) (y + (0 : ℝ) • (v 0)) := by
        simpa using hΦd.hasFDerivAt
      have hstep : HasDerivAt (fun t : ℝ =>
            (iteratedFDeriv ℝ k g (y + t • (v 0))) (Fin.tail v))
          ((fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) =>
            (iteratedFDeriv ℝ k g y') (Fin.tail v)) y) (v 0)) 0 :=
        HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => y + t • (v 0)) (f' := v 0) (x := (0 : ℝ)) hΦ2 hcurve
      have hderiv_eq : (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin d) =>
            (iteratedFDeriv ℝ k g y') (Fin.tail v)) y) (v 0)
          = deriv (fun t : ℝ => (iteratedFDeriv ℝ k g (y + t • (v 0))) (Fin.tail v)) 0 :=
        hstep.deriv.symm
      rw [hderiv_eq]
      have hcongr : (fun t : ℝ => (iteratedFDeriv ℝ k g (y + t • (v 0))) (Fin.tail v))
          = fun t : ℝ => ∫ s in a..b,
              (φ s * s ^ k) * (iteratedFDeriv ℝ k F (s • (y + t • (v 0)))) (Fin.tail v) := by
        funext t
        rw [hfun]
        rw [multilinear_intervalIntegral_apply (hInt k hkw (y + t • (v 0))) (Fin.tail v)]
        apply intervalIntegral.integral_congr
        intro s hs
        simp only [smul_apply, smul_eq_mul]
      rw [hcongr]
      -- pointwise derivative in the parameter `t`
      have hpt5 : ∀ (t : ℝ) (s : ℝ),
          HasDerivAt (fun t' : ℝ =>
              (φ s * s ^ k) * (iteratedFDeriv ℝ k F (s • (y + t' • (v 0)))) (Fin.tail v))
            ((φ s * s ^ (k+1)) * (iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))) v) t := by
        intro t s
        have hz : HasDerivAt (fun t' : ℝ => s • (y + t' • (v 0))) (s • (v 0)) t := by
          have h1 : HasDerivAt (fun t' : ℝ => t' • (s • (v 0))) (s • (v 0)) t := by
            simpa using (hasDerivAt_id t).smul_const (s • (v 0))
          have h2 := h1.const_add (s • y)
          simpa [smul_add, smul_smul, mul_comm, add_comm, add_left_comm, add_assoc] using h2
        have hDd : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) (s • (y + t • (v 0))) :=
          (hFk1.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt (x := s • (y + t • (v 0)))
        have hD : HasFDerivAt (iteratedFDeriv ℝ k F)
            ((iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))).curryLeft)
            (s • (y + t • (v 0))) := by
          have h := hDd.hasFDerivAt
          rw [fderiv_iteratedFDeriv, Function.comp_apply, curryLeftEquiv_apply_eq_curryLeft] at h
          exact h
        have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) =>
              (iteratedFDeriv ℝ k F z) (Fin.tail v))
            ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ
                (Fin.tail v)) ∘SL
              (iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))).curryLeft)
            (s • (y + t • (v 0))) :=
          (ContinuousLinearMap.hasFDerivAt (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ (Fin.tail v))).comp
            (s • (y + t • (v 0))) hD
        have h1 : HasDerivAt (fun t' : ℝ =>
              (iteratedFDeriv ℝ k F (s • (y + t' • (v 0)))) (Fin.tail v))
            (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ
                (Fin.tail v)) ∘SL
              (iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))).curryLeft) (s • (v 0))) t :=
          HasFDerivAt.comp_hasDerivAt (f := fun t' : ℝ => s • (y + t' • (v 0))) (f' := s • (v 0)) (x := t) hc hz
        have hval : ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ
                (Fin.tail v)) ∘SL
              (iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))).curryLeft) (s • (v 0))
            = s * ((iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))) v) := by
          simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply,
            map_smul, ContinuousMultilinearMap.curryLeft_apply, smul_eq_mul]
          rw [Fin.cons_self_tail]
        rw [hval] at h1
        have h2 := h1.const_mul (φ s * s ^ k)
        exact h2.congr_deriv (by rw [pow_succ]; ring)
      have hFF_cont : Continuous (Function.uncurry (fun t : ℝ => fun s : ℝ =>
          (φ s * s ^ k) * (iteratedFDeriv ℝ k F (s • (y + t • (v 0)))) (Fin.tail v))) := by
        have hD : Continuous (fun z : EuclideanSpace ℝ (Fin d) => iteratedFDeriv ℝ k F z) :=
          hFk.continuous_iteratedFDeriv le_rfl
        have hz : Continuous (fun p : ℝ × ℝ => p.2 • (y + p.1 • (v 0))) :=
          continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))
        have hsc : Continuous (fun p : ℝ × ℝ => φ p.2 * p.2 ^ k) :=
          (hφ.comp continuous_snd).mul (continuous_snd.pow k)
        exact hsc.mul (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d))
          ℝ (Fin.tail v)).continuous).comp (hD.comp hz))
      have hFF'_cont : Continuous (Function.uncurry (fun t : ℝ => fun s : ℝ =>
          (φ s * s ^ (k+1)) * (iteratedFDeriv ℝ (k+1) F (s • (y + t • (v 0)))) v)) := by
        have hD : Continuous (fun z : EuclideanSpace ℝ (Fin d) => iteratedFDeriv ℝ (k+1) F z) :=
          hFk1.continuous_iteratedFDeriv le_rfl
        have hz : Continuous (fun p : ℝ × ℝ => p.2 • (y + p.1 • (v 0))) :=
          continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))
        have hsc : Continuous (fun p : ℝ × ℝ => φ p.2 * p.2 ^ (k+1)) :=
          (hφ.comp continuous_snd).mul (continuous_snd.pow (k+1))
        exact hsc.mul (((ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin (k+1) => EuclideanSpace ℝ (Fin d)) ℝ v).continuous).comp (hD.comp hz))
      have hstep := hasDerivAt_intervalIntegral_of_continuous (a := a) (b := b) (t₀ := 0) hFF_cont hFF'_cont hpt5
      rw [hstep.deriv]
      rw [show y + (0 : ℝ) • (v 0) = y from by simp]
      rw [multilinear_intervalIntegral_apply (hInt (k+1) hkw1 y) v]
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [smul_apply, smul_eq_mul]
  have hmain := main n le_rfl x m
  rw [hmain]
  rw [multilinear_intervalIntegral_apply (hInt n le_rfl x) m]
  apply intervalIntegral.integral_congr
  intro s hs
  simp [smul_apply, smul_eq_mul]

end Commons.Analysis.Calculus