import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.Analysis.Complex.twisted_inversion_regularized
import Submission.Commons.Analysis.Complex.lapX_regularized_bound_neg

namespace Commons.NumberTheory.DirichletCharacter

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators

/-- Continuity and integrability of the `f(0)`-regularized twisted Laplace kernel
`τ ↦ ∫_0^{x₀} e^{-((s-(α+iτ))L)t} f t dt - f 0/((s-(α+iτ))L)` on the line `Re = α > s.re`. -/
theorem laplace_transform_twisted_regularized_cont_integrable {x₀ B : ℝ} (hx₀ : 0 < x₀)
    (hB : 0 ≤ B) {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα : s.re < α) :
    Continuous (fun τ : ℝ => (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) ∧
      MeasureTheory.Integrable (fun τ : ℝ => (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hLpos : 0 < L := by linarith
  have hdne : (s.re - α) ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  set Z : ℝ → ℂ := fun τ => (s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ) with hZdef
  have hZre : ∀ τ : ℝ, (Z τ).re = (s.re - α) * L := by
    intro τ
    rw [hZdef]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hZre_neg : ∀ τ : ℝ, (Z τ).re < 0 := by
    intro τ; rw [hZre τ]; exact mul_neg_of_neg_of_pos (by linarith) hLpos
  have hZne : ∀ τ : ℝ, Z τ ≠ 0 := by
    intro τ h
    have := hZre_neg τ
    rw [h] at this; simp at this
  have hZcont : Continuous Z := by rw [hZdef]; fun_prop
  -- rewrite the goal function in terms of `Z`
  have hgoal : (fun τ : ℝ => (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)))
      = fun τ : ℝ => (∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t : ℂ))) * f t) - f 0 / Z τ := by
    funext τ; rw [hZdef]
  rw [hgoal]
  -- continuity of the inner integral
  have hclamp_mem : ∀ t : ℝ, max 0 (min t x₀) ∈ Set.Icc (0:ℝ) x₀ :=
    fun t => ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩
  have hcongr : (fun τ : ℝ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t:ℂ))) * f t)
      = fun τ : ℝ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t:ℂ))) * f (max 0 (min t x₀)) := by
    funext τ
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx₀.le] at ht
    dsimp only
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have huncurry : Continuous (Function.uncurry (fun (τ : ℝ) (t : ℝ) =>
      Complex.exp (-(Z τ * (t:ℂ))) * f (max 0 (min t x₀)))) := by
    have h1 : Continuous (fun p : ℝ × ℝ => Z p.1 * ((p.2 : ℝ) : ℂ)) :=
      (hZcont.comp continuous_fst).mul (Complex.continuous_ofReal.comp continuous_snd)
    have h2 : Continuous (fun p : ℝ × ℝ => Complex.exp (-(Z p.1 * ((p.2:ℝ):ℂ)))) :=
      Complex.continuous_exp.comp h1.neg
    have h3 : Continuous (fun p : ℝ × ℝ => f (max 0 (min p.2 x₀))) :=
      (hcont.comp_continuous (by fun_prop) hclamp_mem).comp continuous_snd
    exact h2.mul h3
  have hIker : Continuous (fun τ : ℝ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t:ℂ))) * f t) := by
    rw [hcongr]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huncurry 0 x₀
  have hΦcont : Continuous (fun τ : ℝ =>
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t:ℂ))) * f t) - f 0 / Z τ) :=
    hIker.sub (continuous_const.div hZcont hZne)
  -- norm identity for `Z`
  have hZnorm : ∀ τ : ℝ, ‖Z τ‖^2 = L^2 * ((s.re - α)^2 + (τ - s.im)^2) := by
    intro τ
    have hsq : ‖s - ((α:ℂ) + (τ:ℂ)*Complex.I)‖^2 = (s.re - α)^2 + (s.im - τ)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, sub_zero]
      ring
    rw [hZdef, norm_mul, mul_pow, Complex.norm_of_nonneg hLpos.le, hsq]
    ring
  -- the pointwise bound
  set C : ℝ := 3 * B * x₀ * Real.exp (-((s.re - α) * L) * x₀)
      + ‖f 0‖ * (Real.exp (-((s.re - α) * L) * x₀) + 1) / x₀ with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hbound : ∀ τ : ℝ, ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(Z τ * (t:ℂ))) * f t) - f 0 / Z τ‖
      ≤ C / ((s.re - α)^2 + (τ - s.im)^2) := by
    intro τ
    have h := Commons.Analysis.Complex.lapX_regularized_bound_neg hx₀ hB hcont hf2 hBnd hvan
      (z := Z τ) (hZre_neg τ)
    rw [hZre τ] at h
    have hDpos : 0 < (s.re - α)^2 + (τ - s.im)^2 := by positivity
    refine h.trans ?_
    rw [hZnorm τ]
    exact div_le_div_of_nonneg_left hCnn hDpos (by nlinarith [hDpos, hL2])
  -- integrability of the dominating function
  have hIntegrable : Integrable (fun τ : ℝ => C / ((s.re - α)^2 + (τ - s.im)^2)) := by
    have hbase : Integrable (fun u : ℝ => (C / (s.re - α)^2) * (1 + u^2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    have hkey : (fun τ : ℝ => C / ((s.re - α)^2 + (τ - s.im)^2))
        = fun τ : ℝ => (C / (s.re - α)^2) * (1 + ((τ - s.im)/(s.re - α))^2)⁻¹ := by
      funext τ
      rw [div_pow]
      have h1 : (s.re - α)^2 + (τ - s.im)^2
          = (s.re - α)^2 * (1 + (τ - s.im)^2 / (s.re - α)^2) := by
        rw [mul_add, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hdne)]
      rw [h1, div_mul_eq_div_div, div_eq_mul_inv]
    rw [hkey]
    exact (hbase.comp_div hdne).comp_sub_right s.im
  exact ⟨hΦcont, Integrable.mono' hIntegrable hΦcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)⟩

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators

/-- The `α`-line (flipped) identity for the smoothed von Mangoldt sum with the
`f(0)`-regularized kernel: for `1 < α` and `s.re < α`,
`Σ_n Λ(n)χ(n) n^{-s} f(log n / L) = -(L/2π) ∫_τ (L'/L)(χ, α+iτ) Φ(α+iτ) dτ`
where `Φ u = ∫_0^{x₀} e^{-(s-u)Lt} f t dt - f 0/((s-u)L)`. -/
theorem smoothed_vonMangoldt_eq_line_regularized {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hασ : s.re < α) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
        f (Real.log n / L))
      = -(L / (2 * (Real.pi : ℂ))) * ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I) *
          ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
            - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hLpos : 0 < L := by linarith
  set G : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) with hGdef
  set Φ : ℝ → ℂ := fun τ => (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) with hΦdef
  have hlog : ∀ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I)
      = - LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) := by
    intro τ
    have h1 : 1 < (((α : ℂ) + (τ : ℂ) * Complex.I)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hα1
    exact LFunction_logDeriv_eq_neg_LSeries_vonMangoldt (N := N) χ h1
  have hsumm : ∀ z : ℂ, 1 < z.re → Summable (fun n : ℕ => LSeries.term G z n) := by
    intro z hz
    have h1 : LSeriesSummable
        (fun n : ℕ => (χ (n : ZMod N) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) z :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hz
    have h2 : LSeriesSummable G z :=
      (LSeriesSummable_congr (f := G)
        (g := fun n : ℕ => (χ (n : ZMod N) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) z
        (fun {n} _ => by simp only [hGdef]; ring)).mpr h1
    exact h2
  have hIcont : Continuous Φ := by
    rw [hΦdef]
    exact (laplace_transform_twisted_regularized_cont_integrable hx₀ hB hcont hf2 hBnd hvan hL hασ).1
  have hIint : Integrable Φ := by
    rw [hΦdef]
    exact (laplace_transform_twisted_regularized_cont_integrable hx₀ hB hcont hf2 hBnd hvan hL hασ).2
  have hbd : ∀ m : ℕ, ∀ τ : ℝ,
      ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ‖
        ≤ ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖Φ τ‖ := by
    intro m τ
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [LSeries.term_def, ↓reduceIte, zero_mul, norm_zero]
      exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) (norm_nonneg _)
    · have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have hnorm : ‖(m : ℂ) ^ ((α : ℂ) + (τ : ℂ) * Complex.I)‖ = (m : ℝ) ^ α := by
        have h := Complex.norm_cpow_eq_rpow_re_of_pos hmpos ((α : ℂ) + (τ : ℂ) * Complex.I)
        simp only [Complex.ofReal_natCast] at h
        simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] using h
      have hGnorm : ‖G m‖ ≤ (ArithmeticFunction.vonMangoldt m : ℝ) := by
        rw [hGdef]
        simp only [norm_mul]
        have h1 : ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖
            = ArithmeticFunction.vonMangoldt m := by
          simp [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [h1]
        calc ArithmeticFunction.vonMangoldt m * ‖(χ (m : ZMod N) : ℂ)‖
            ≤ ArithmeticFunction.vonMangoldt m * 1 :=
              mul_le_mul_of_nonneg_left (norm_char_nat_le_one χ m)
                ArithmeticFunction.vonMangoldt_nonneg
          _ = ArithmeticFunction.vonMangoldt m := by ring
      rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.mp hm), norm_mul, norm_div, hnorm]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hGnorm (by positivity))
        (norm_nonneg _)
  have hFint : ∀ m : ℕ, Integrable (fun τ : ℝ =>
      LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ) := by
    intro m
    have hcont_term : AEStronglyMeasurable
        (fun τ : ℝ => LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m) volume := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa only [LSeries.term_def, ↓reduceIte] using
          (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0:ℂ)) volume)
      · have hsp : (m : ℂ) ∈ Complex.slitPlane :=
          Complex.natCast_mem_slitPlane.mpr (Nat.pos_iff_ne_zero.mp hm)
        have hcont : Continuous (fun τ : ℝ => (m : ℂ) ^ ((α : ℂ) + (τ : ℂ) * Complex.I)) :=
          continuous_const.cpow (by fun_prop) (fun _ => hsp)
        have hmne : (m : ℂ) ≠ 0 := by
          simp only [Ne, Nat.cast_eq_zero]; exact Nat.pos_iff_ne_zero.mp hm
        have hne : ∀ τ : ℝ, (m : ℂ) ^ ((α : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := fun τ =>
          Complex.cpow_ne_zero_iff.mpr (Or.inl hmne)
        have heq : (fun τ : ℝ => LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m)
            = fun τ : ℝ => G m * ((m : ℂ) ^ ((α : ℂ) + (τ : ℂ) * Complex.I))⁻¹ := by
          funext τ
          rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.mp hm), div_eq_mul_inv]
        rw [heq]
        exact ((hcont.inv₀ hne).const_mul (G m)).aestronglyMeasurable
    refine Integrable.mono'
      (g := fun τ : ℝ => ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖Φ τ‖)
      (hIint.norm.const_mul _) (hcont_term.mul hIcont.aestronglyMeasurable) ?_
    filter_upwards with τ
    exact hbd m τ
  have hFsum : Summable (fun m : ℕ => ∫ τ : ℝ,
      ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ‖) := by
    have hbd2 : ∀ m : ℕ, ∫ τ : ℝ, ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ‖
        ≤ ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ∫ τ : ℝ, ‖Φ τ‖ := by
      intro m
      calc ∫ τ : ℝ, ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ‖
          ≤ ∫ τ : ℝ, ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖Φ τ‖ :=
            integral_mono_ae (hFint m).norm (hIint.norm.const_mul _)
              (Filter.Eventually.of_forall (hbd m))
        _ = ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ∫ τ : ℝ, ‖Φ τ‖ :=
            integral_const_mul _ _
    exact Summable.of_nonneg_of_le (fun m => integral_nonneg (fun τ => norm_nonneg _)) hbd2
      (Summable.mul_right _ (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hα1))
  have hHas := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hswap : (∫ τ : ℝ, LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ τ)
      = ∑' m : ℕ, ∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ := by
    rw [hHas.tsum_eq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with τ
    have hs' : 1 < ((α : ℂ) + (τ : ℂ) * Complex.I).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hα1
    show LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ τ
        = ∑' m : ℕ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ
    rw [LSeries]
    exact (Summable.tsum_mul_right (Φ τ) (hsumm _ hs')).symm
  have hper : ∀ m : ℕ, (∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ)
      = (2 * (Real.pi : ℂ) / (L : ℂ)) * ((ArithmeticFunction.vonMangoldt m : ℂ)
          * (χ (m : ZMod N) : ℂ) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
    intro m
    rcases lt_or_ge m 2 with hm | hm
    · interval_cases m
      · have h0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
        simp only [LSeries.term_def, ↓reduceIte, zero_mul, MeasureTheory.integral_zero, h0]
        simp
      · have h1 : ArithmeticFunction.vonMangoldt 1 = 0 :=
          ArithmeticFunction.vonMangoldt_apply_one
        simp only [LSeries.term_def, if_neg (by norm_num : ¬ ((1:ℕ) = 0)), hGdef,
          ArithmeticFunction.vonMangoldt_apply_one]
        simp
    · have hR3 := Commons.Analysis.Complex.twisted_inversion_regularized (f := f) (x₀ := x₀) hx₀ hB hcont hf2 hBnd hvan
        hL (s := s) (α := α) hασ (m := m) hm
      have hR3' : (∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * Φ τ)
          = (2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L) := by
        simpa only [hΦdef] using hR3
      have hterm : ∀ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ
          = G m * ((m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * Φ τ) := by
        intro τ
        have hmpos : 0 < m := by omega
        rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.mp hmpos), div_eq_mul_inv,
          ← Complex.cpow_neg (m : ℂ) ((α : ℂ) + (τ : ℂ) * Complex.I)]
        ring
      calc (∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * Φ τ)
          = ∫ τ : ℝ, G m * ((m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * Φ τ) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with τ
            exact hterm τ
        _ = G m * ∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * Φ τ :=
            integral_const_mul _ _
        _ = G m * ((2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
            rw [hR3']
        _ = (2 * (Real.pi : ℂ) / (L : ℂ)) * ((ArithmeticFunction.vonMangoldt m : ℂ)
              * (χ (m : ZMod N) : ℂ) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
            rw [hGdef]; ring
  have hgoal_eq : (∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ τ)
      = - ∫ τ : ℝ, LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ τ := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with τ
    rw [hlog τ]; ring
  rw [hgoal_eq, hswap, tsum_congr hper, tsum_mul_left]
  set S : ℂ := ∑' x : ℕ, (ArithmeticFunction.vonMangoldt x : ℂ) * (χ (x : ZMod N) : ℂ)
      * (x : ℂ) ^ (-s) * f (Real.log x / L) with hSdef
  have hconst : -(L / (2 * (Real.pi : ℂ))) * (-(2 * (Real.pi : ℂ) / (L : ℂ))) = 1 := by
    have h1 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hLpos)
    have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [← neg_mul, ← mul_assoc, hconst, one_mul, hSdef]
  apply tsum_congr
  intro n
  rw [div_eq_mul_inv, ← Complex.cpow_neg (n : ℂ) s]

end Commons.NumberTheory.DirichletCharacter