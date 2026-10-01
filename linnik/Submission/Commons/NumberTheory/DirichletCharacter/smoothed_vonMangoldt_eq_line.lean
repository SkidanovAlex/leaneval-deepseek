import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.Analysis.Complex.laplace_transform_twisted_continuous_integrable
import Submission.Commons.Analysis.Complex.laplace_inversion_twisted

namespace Commons.NumberTheory.DirichletCharacter

open MeasureTheory

theorem smoothed_vonMangoldt_eq_line {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : 1 < s.re)
    {α : ℝ} (hα1 : 1 < α) (hασ : α < s.re) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
        f (Real.log n / L))
      = (L / (2 * (Real.pi : ℂ))) * ∫ τ : ℝ,
          (- logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I)) *
            (∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t) := by
  have hLpos : 0 < L := by linarith
  -- ==== abbreviations ====
  set G : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) with hGdef
  set I : ℝ → ℂ := fun τ => ∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t with hIdef
  -- ==== pointwise log-derivative identity ====
  have hlog : ∀ τ : ℝ, -logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I)
      = LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) := by
    intro τ
    have h1 : 1 < (((α : ℂ) + (τ : ℂ) * Complex.I)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hα1
    have h2 := LFunction_logDeriv_eq_neg_LSeries_vonMangoldt (N := N) χ h1
    rw [h2, neg_neg]
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
  -- ==== the inner integral is continuous and integrable ====
  have hIcont : Continuous I := by
    rw [hIdef]
    exact (Commons.Analysis.Complex.laplace_transform_twisted_continuous_integrable
      hx₀ hB hcont hf2 hBnd hvan hf0 hL hs hασ).1
  have hIint : Integrable I := by
    rw [hIdef]
    exact (Commons.Analysis.Complex.laplace_transform_twisted_continuous_integrable
      hx₀ hB hcont hf2 hBnd hvan hf0 hL hs hασ).2
  -- ==== pointwise bound for the summand ====
  have hbd : ∀ m : ℕ, ∀ τ : ℝ,
      ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ‖
        ≤ ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖I τ‖ := by
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
  -- ==== integrability of each summand ====
  have hFint : ∀ m : ℕ, Integrable (fun τ : ℝ =>
      LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ) := by
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
      (g := fun τ : ℝ => ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖I τ‖)
      (hIint.norm.const_mul _) (hcont_term.mul hIcont.aestronglyMeasurable) ?_
    filter_upwards with τ
    exact hbd m τ
  -- ==== summability of the integrals ====
  have hFsum : Summable (fun m : ℕ => ∫ τ : ℝ,
      ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ‖) := by
    have hbd2 : ∀ m : ℕ, ∫ τ : ℝ, ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ‖
        ≤ ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ∫ τ : ℝ, ‖I τ‖ := by
      intro m
      calc ∫ τ : ℝ, ‖LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ‖
          ≤ ∫ τ : ℝ, ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ‖I τ‖ :=
            integral_mono_ae (hFint m).norm (hIint.norm.const_mul _)
              (Filter.Eventually.of_forall (hbd m))
        _ = ((ArithmeticFunction.vonMangoldt m : ℝ) / ((m : ℝ) ^ α)) * ∫ τ : ℝ, ‖I τ‖ :=
            integral_const_mul _ _
    exact Summable.of_nonneg_of_le (fun m => integral_nonneg (fun τ => norm_nonneg _)) hbd2
      (Summable.mul_right _ (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hα1))
  have hHas := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hswap : (∫ τ : ℝ, LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) * I τ)
      = ∑' m : ℕ, ∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ := by
    rw [hHas.tsum_eq]
    apply integral_congr_ae
    filter_upwards with τ
    have hs' : 1 < ((α : ℂ) + (τ : ℂ) * Complex.I).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hα1
    show LSeries G ((α : ℂ) + (τ : ℂ) * Complex.I) * I τ
        = ∑' m : ℕ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ
    rw [LSeries]
    exact (Summable.tsum_mul_right (I τ) (hsumm _ hs')).symm
  -- ==== per-term evaluation ====
  have hper : ∀ m : ℕ, (∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ)
      = (2 * (Real.pi : ℂ) / (L : ℂ)) * ((ArithmeticFunction.vonMangoldt m : ℂ)
          * (χ (m : ZMod N) : ℂ) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
    intro m
    rcases lt_or_ge m 2 with hm | hm
    · interval_cases m
      · have h0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
        simp only [LSeries.term_def, ↓reduceIte, zero_mul, integral_zero, h0]
        simp
      · have h1 : ArithmeticFunction.vonMangoldt 1 = 0 :=
          ArithmeticFunction.vonMangoldt_apply_one
        simp only [LSeries.term_def, if_neg (by norm_num : ¬ ((1:ℕ) = 0)), hGdef,
          ArithmeticFunction.vonMangoldt_apply_one]
        simp
    · have hR3 := Commons.Analysis.Complex.laplace_inversion_twisted
        (f := f) (x₀ := x₀) hx₀ hB hcont hf2 hBnd hvan hf0 hL hs hα1 hασ hm
      have hR3' : (∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * I τ)
          = (2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L) := by
        rw [hIdef]
        exact hR3
      have hterm : ∀ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ
          = G m * ((m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * I τ) := by
        intro τ
        have hmpos : 0 < m := by omega
        rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.mp hmpos), div_eq_mul_inv,
          ← Complex.cpow_neg (m : ℂ) ((α : ℂ) + (τ : ℂ) * Complex.I)]
        ring
      calc (∫ τ : ℝ, LSeries.term G ((α : ℂ) + (τ : ℂ) * Complex.I) m * I τ)
          = ∫ τ : ℝ, G m * ((m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * I τ) := by
            apply integral_congr_ae
            filter_upwards with τ
            exact hterm τ
        _ = G m * ∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) * I τ :=
            integral_const_mul _ _
        _ = G m * ((2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
            rw [hR3']
        _ = (2 * (Real.pi : ℂ) / (L : ℂ)) * ((ArithmeticFunction.vonMangoldt m : ℂ)
              * (χ (m : ZMod N) : ℂ) * (m : ℂ) ^ (-s) * f (Real.log m / L)) := by
            rw [hGdef]; ring
  -- ==== assemble ====
  simp only [hlog]
  rw [hswap, tsum_congr hper, tsum_mul_left]
  have hLne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hLpos)
  have hconst : (L / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ) / (L : ℂ)) = 1 := by
    field_simp
  rw [← mul_assoc, hconst, one_mul]
  apply tsum_congr
  intro n
  rw [div_eq_mul_inv, ← Complex.cpow_neg (n : ℂ) s]

end Commons.NumberTheory.DirichletCharacter
