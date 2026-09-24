import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

set_option autoImplicit false

open MeasureTheory

open scoped BigOperators

namespace Commons.Analysis.DirichletPolynomial

/-- For `x > 0` and real `y`, the complex power `x ^ (I * y)` equals
`exp (I * (y * log x))`. -/
private lemma cpow_I_eq_exp (x y : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ (Complex.I * (y : ℂ))
      = Complex.exp (Complex.I * ((y : ℂ) * ((Real.log x : ℝ) : ℂ))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
  congr 1
  ring

theorem dual_integral_mean_value :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (R : ℕ) (t : Fin R → ℝ) (c : Fin R → ℂ),
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      ‖∫ x in (N : ℝ)..(2 * (N : ℝ)), ‖∑ i, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2‖ ≤
        C * (N : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
  obtain ⟨C₀, hC₀pos, hMV⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨2 * (Real.log 2 + C₀), ?_, ?_⟩
  · have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro N hN R t c hsep
  -- N > 0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h2Npos : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hNpos (by linarith)
  -- the two integrands
  let F : ℝ → ℂ := fun u => ∑ i, c i * Complex.exp (Complex.I * ((t i : ℂ) * (u : ℂ)))
  let G : ℝ → ℝ := fun u => ‖F u‖ ^ 2
  let H : ℝ → ℝ := fun x => ‖∑ i, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2
  have hGnonneg : ∀ u, 0 ≤ G u := by intro u; dsimp only [G]; positivity
  have hHnonneg : ∀ u, 0 ≤ H u := by intro u; dsimp only [H]; positivity
  -- G is continuous
  have hGcont : Continuous G := by
    dsimp only [G, F]
    fun_prop
  -- pointwise identity on the positive half-line
  have hHF : ∀ x : ℝ, 0 < x → H x = G (Real.log x) := by
    intro x hx
    have hsum : (∑ i, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))) = F (Real.log x) := by
      dsimp only [F]
      apply Finset.sum_congr rfl
      intro i _
      rw [cpow_I_eq_exp x (t i) hx]
    dsimp only [H, G]
    rw [hsum]
  have hHcont : ContinuousOn H (Set.Ioi 0) := by
    have hcomp : ContinuousOn (fun x => G (Real.log x)) (Set.Ioi 0) :=
      hGcont.comp_continuousOn (Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hx))
    exact hcomp.congr (fun x hx => hHF x hx)
  -- substitution x = exp u
  have himg : Real.exp '' Set.uIcc (Real.log (N : ℝ)) (Real.log (2 * (N : ℝ))) ⊆ Set.Ioi 0 := by
    rintro y ⟨x, hx, rfl⟩
    exact Real.exp_pos x
  have hsub := intervalIntegral.integral_comp_mul_deriv'
      (a := Real.log (N : ℝ)) (b := Real.log (2 * (N : ℝ)))
      (f := Real.exp) (f' := Real.exp) (g := H)
      (fun x _ => Real.hasDerivAt_exp x)
      Real.continuous_exp.continuousOn
      (hHcont.mono himg)
  have hsubst : (∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * Real.exp x)
      = ∫ x in (N : ℝ)..(2 * (N : ℝ)), H x := by
    have hlhs : (∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))),
          (H ∘ Real.exp) x * Real.exp x)
        = ∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * Real.exp x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Function.comp_apply]
      rw [hHF (Real.exp x) (Real.exp_pos x), Real.log_exp]
    rw [hlhs] at hsub
    rw [Real.exp_log hNpos, Real.exp_log h2Npos] at hsub
    exact hsub
  -- weight bound exp u ≤ 2N on the interval
  have hExpLe : ∀ x ∈ Set.Icc (Real.log (N : ℝ)) (Real.log (2 * (N : ℝ))),
      Real.exp x ≤ 2 * (N : ℝ) := by
    intro x hx
    calc Real.exp x ≤ Real.exp (Real.log (2 * (N : ℝ))) := Real.exp_le_exp.mpr hx.2
      _ = 2 * (N : ℝ) := Real.exp_log h2Npos
  have hint1 : IntervalIntegrable (fun x => G x * Real.exp x) volume
      (Real.log (N : ℝ)) (Real.log (2 * (N : ℝ))) :=
    ((hGcont.mul Real.continuous_exp).intervalIntegrable _ _)
  have hint2 : IntervalIntegrable (fun x => G x * (2 * (N : ℝ))) volume
      (Real.log (N : ℝ)) (Real.log (2 * (N : ℝ))) :=
    ((hGcont.mul continuous_const).intervalIntegrable _ _)
  have hmono : (∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * Real.exp x)
      ≤ ∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * (2 * (N : ℝ)) := by
    apply intervalIntegral.integral_mono_on hlog_le hint1 hint2
    intro x hx
    exact mul_le_mul_of_nonneg_left (hExpLe x hx) (hGnonneg x)
  -- the harmonic-analysis bound
  have hMVapp : (∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x)
      ≤ (Real.log (2 * (N : ℝ)) - Real.log (N : ℝ) + C₀) * (∑ i, ‖c i‖ ^ 2) := by
    have hs := hMV 1 one_pos R t c hsep (Real.log (N : ℝ)) (Real.log (2 * (N : ℝ))) hlog_le
    simpa only [G, F, div_one] using hs
  have hlogdiff : Real.log (2 * (N : ℝ)) - Real.log (N : ℝ) = Real.log 2 := by
    rw [Real.log_mul (by norm_num) hN0]
    ring
  have hfinal : (∫ x in (N : ℝ)..(2 * (N : ℝ)), H x)
      ≤ (2 * (Real.log 2 + C₀)) * (N : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    rw [← hsubst]
    calc (∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * Real.exp x)
        ≤ ∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x * (2 * (N : ℝ)) := hmono
      _ = (2 * (N : ℝ)) * ∫ x in (Real.log (N : ℝ))..(Real.log (2 * (N : ℝ))), G x := by
            rw [intervalIntegral.integral_mul_const]; ring
      _ ≤ (2 * (N : ℝ)) * ((Real.log (2 * (N : ℝ)) - Real.log (N : ℝ) + C₀)
              * (∑ i, ‖c i‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_left hMVapp (by linarith)
      _ = (2 * (Real.log 2 + C₀)) * (N : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
            rw [hlogdiff]; ring
  change ‖∫ x in (N : ℝ)..(2 * (N : ℝ)), H x‖ ≤ (2 * (Real.log 2 + C₀)) * (N : ℝ) * ∑ i, ‖c i‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall (by linarith) hHnonneg)]
  exact hfinal

end Commons.Analysis.DirichletPolynomial
