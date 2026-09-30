import Mathlib
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

open Commons.NumberTheory.Zeta
  (sigmaLine perronLog exp_cpow_ofReal_pos div_cpow_ofReal_div
   sigmaLine_continuous sigmaLine_ne_zero sigmaLine_norm_ge
   perronSummand_norm_le perronSummand_continuous)

/-- Truncated Perron-series expansion for a general coefficient sequence `v` with `v 0 = 0`,
under the absolute-convergence hypothesis `Σ ‖v n‖ (x/n)^σ < ∞` (`1 < σ`).  This is the
general-sequence version of `Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq`. -/
theorem perronSeries_sum_eq (v : ℕ → ℂ) (hv0 : v 0 = 0) (x : ℝ) (hx : 0 < x)
    (σ T : ℝ) (hσ : 1 < σ)
    (hsum : Summable (fun n : ℕ => ‖v n‖ * (x / (n : ℝ)) ^ σ)) :
    (1 / (2 * Real.pi)) *
        (∫ (t : ℝ) in -T..T,
          (LSeries v (((σ : ℂ) + Complex.I * (t : ℂ)))) *
            (x : ℂ) ^ (((σ : ℂ) + Complex.I * (t : ℂ))) /
            (((σ : ℂ) + Complex.I * (t : ℂ))))
      = ∑' n : ℕ,
          v n * (1 / (2 * Real.pi)) *
            (∫ (t : ℝ) in -T..T,
              Complex.exp ((((σ : ℂ) + Complex.I * (t : ℂ))) *
                (Complex.log (((x / (n : ℝ) : ℝ) : ℂ)))) /
              (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  let s : ℝ → ℂ := fun t => sigmaLine σ t
  change c * (∫ t in -T..T,
        (LSeries v (s t)) * (x : ℂ) ^ (s t) / (s t))
      = ∑' n : ℕ, v n * c * (∫ t in -T..T,
          Complex.exp (s t * (Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))) / (s t))
  have hσ0 : 0 < σ := by linarith
  have hσn0 : σ ≠ 0 := ne_of_gt hσ0
  have hscont : Continuous s := by
    simpa [s] using (sigmaLine_continuous σ)
  have hsnz : ∀ t : ℝ, s t ≠ 0 := by
    intro t
    simpa [s] using (sigmaLine_ne_zero σ hσn0 t)
  let logz : ℕ → ℂ := fun n : ℕ => perronLog x n
  let Ffun : ℕ → ℝ → ℂ := fun n t => (c * v n) * Complex.exp (s t * logz n) / s t
  let f : ℝ → ℂ := fun t => LSeries v (s t) * (x : ℂ) ^ (s t) / s t
  -- per-term identity: Dirichlet-series term = v n · exp(s·log(x/n)) / s
  have hper : ∀ (n : ℕ) (hn : n ≠ 0) (t : ℝ),
      LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t = v n * Complex.exp (s t * logz n) / s t := by
    intro n hn t
    have hs : ((x / (n : ℝ)) : ℝ) > 0 := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    calc
      LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t
          = (v n / (n : ℂ) ^ (s t)) * (x : ℂ) ^ (s t) / s t := by
              rw [LSeries.term_of_ne_zero hn]
      _ = v n * (((x : ℂ) ^ (s t) / ((n : ℂ) ^ (s t)))) / s t := by
              rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = v n * (((x : ℂ) ^ (s t) / (((n : ℝ) : ℂ) ^ (s t)))) / s t := by rfl
      _ = v n * ((((x / (n : ℝ)) : ℝ) : ℂ) ^ (s t)) / s t := by
              rw [div_cpow_ofReal_div x (n : ℝ) hx.le (by positivity) (s t)]
      _ = v n * Complex.exp (s t * logz n) / s t := by
              rw [exp_cpow_ofReal_pos (x / (n : ℝ)) hs]
              rfl
  -- multiply the (absolutely summable) series of terms by the constant x^s / s
  have htsum : ∀ t : ℝ,
      (∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t) =
        LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by
    intro t
    calc
      (∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t)
          = ∑' n : ℕ, LSeries.term v (s t) n * ((x : ℂ) ^ (s t) / s t) := by
              refine tsum_congr ?_
              intro n
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
      _ = (∑' n : ℕ, LSeries.term v (s t) n) * ((x : ℂ) ^ (s t) / s t) := tsum_mul_right
      _ = (∑' n : ℕ, LSeries.term v (s t) n) * (x : ℂ) ^ (s t) / s t := by
              rw [div_eq_mul_inv]
              ring
      _ = LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by rfl
  -- the per-term sum equals the L-series times x^s / s
  have hmid : ∀ t : ℝ,
      (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t) =
        LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by
    intro t
    calc
      (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t)
          = ∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t := by
              refine tsum_congr ?_
              intro n
              by_cases hn : n = 0
              · subst n
                simp [hv0, LSeries.term_zero]
              · exact (hper n hn t).symm
      _ = LSeries v (s t) * (x : ℂ) ^ (s t) / s t := htsum t
  -- pointwise equality of the summed integrands
  have hpt : ∀ t : ℝ, (∑' n : ℕ, Ffun n t) = c * f t := by
    intro t
    calc
      (∑' n : ℕ, Ffun n t) = ∑' n : ℕ, c * (v n * Complex.exp (s t * logz n) / s t) := by
          refine tsum_congr ?_
          intro n
          dsimp [Ffun]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = c * (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t) := tsum_mul_left
      _ = c * f t := by
          dsimp [f]
          rw [hmid t]
  -- pointwise upper bound of the summands
  have hpt_bound : ∀ (n : ℕ) (t : ℝ), ‖Ffun n t‖ ≤
      ‖c‖ * ‖v n‖ * ((x / (n : ℝ)) ^ σ) / σ := by
    intro n t
    by_cases hn : n = 0
    · subst n
      simp [Ffun, hv0]
    · calc
        ‖Ffun n t‖ ≤ ‖c * v n‖ * ((x / (n : ℝ)) ^ σ) / σ := by
            dsimp [Ffun]
            exact perronSummand_norm_le x σ hx hσ (c * v n) n hn t
        _ = ‖c‖ * ‖v n‖ * ((x / (n : ℝ)) ^ σ) / σ := by
            rw [norm_mul]
  have hFC_cont : ∀ n : ℕ, Continuous (fun t : ℝ => Ffun n t) := by
    intro n
    dsimp [Ffun]
    exact perronSummand_continuous (c * v n) (logz n) hscont hsnz
  let FC : ℕ → C(ℝ, ℂ) := fun n => ContinuousMap.mk (fun t : ℝ => Ffun n t) (hFC_cont n)
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (-T) T, isCompact_uIcc⟩
  let b : ℕ → ℝ := fun n : ℕ =>
      ‖c‖ * ‖v n‖ * ((x / (n : ℝ)) ^ σ) / σ
  have hb_nonneg : ∀ n : ℕ, 0 ≤ b n := by
    intro n
    dsimp [b]
    have h1 : 0 ≤ (x / (n : ℝ)) ^ σ :=
      Real.rpow_nonneg (div_nonneg (le_of_lt hx) (by positivity : 0 ≤ (n : ℝ))) σ
    have hnum : 0 ≤ ‖c‖ * ‖v n‖ * ((x / (n : ℝ)) ^ σ) := by positivity
    exact div_nonneg hnum (le_of_lt hσ0)
  have hsum_b : Summable b := by
    have hb' : Summable (fun n : ℕ => (‖c‖ / σ) * (‖v n‖ * ((x / (n : ℝ)) ^ σ))) :=
      Summable.mul_left (‖c‖ / σ) hsum
    exact (summable_congr (fun n => by dsimp [b]; ring)).mpr hb'
  have hsup : ∀ n : ℕ, ‖(FC n).restrict K‖ ≤ b n := by
    intro n
    rw [ContinuousMap.norm_le (f := (FC n).restrict K) (C := b n) (hb_nonneg n)]
    intro y
    change ‖Ffun n (y : ℝ)‖ ≤ b n
    exact hpt_bound n (y : ℝ)
  have hFC_sum : Summable (fun n : ℕ => ‖(FC n).restrict K‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsup hsum_b
  -- interchange sum and interval integral
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (f := FC) hFC_sum
  -- termwise: the integral of the summand equals the RHS summand
  have hterm : ∀ n : ℕ,
      (∫ t in -T..T, Ffun n t) =
        v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
    intro n
    calc
      (∫ t in -T..T, Ffun n t)
          = ∫ t in -T..T, (c * v n) * (Complex.exp (s t * logz n) / s t) := by
              apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
              funext t
              dsimp [Ffun]
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
      _ = (c * v n) * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
              rw [intervalIntegral.integral_const_mul]
      _ = v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by ring
  -- assemble
  calc
    c * (∫ t in -T..T, f t) = ∫ t in -T..T, c * f t := by
        exact (intervalIntegral.integral_const_mul c f).symm
    _ = ∫ t in -T..T, (∑' n : ℕ, Ffun n t) := by
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        exact (hpt t).symm
    _ = ∫ t in -T..T, (∑' n : ℕ, (FC n) t) := by
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        refine tsum_congr ?_
        intro n
        rfl
    _ = ∑' n : ℕ, (∫ t in -T..T, (FC n) t) := hswap.symm
    _ = ∑' n : ℕ, (∫ t in -T..T, Ffun n t) := by
        refine tsum_congr ?_
        intro n
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        rfl
    _ = ∑' n : ℕ, v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
        exact tsum_congr hterm

end Commons.NumberTheory.DirichletCharacter
