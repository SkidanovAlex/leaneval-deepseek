import Mathlib
import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound

namespace Commons.Analysis.Oscillatory

open MeasureTheory
open scoped Real Topology

/-- The oscillatory "pseudo-projection" `v_t(β) = ∫_0^1 e(-β t^d s^d) ds` satisfies
`|v_t(β)| ≤ C / (t β^{1/d})` (van der Corput) and `|v_t(β) - 1| ≤ C β t^d` (mean value
theorem). -/
theorem vt_oscillatory_integral (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t β : ℝ, 0 < t → 0 < β →
      (‖∫ s in (0 : ℝ)..1,
            Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)‖
          ≤ C / (t * β ^ ((1 : ℝ) / (d : ℝ)))) ∧
      (‖(∫ s in (0 : ℝ)..1,
            Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)) - 1‖
          ≤ C * t ^ d * β) := by
  obtain ⟨C1, hC1pos, hC1⟩ := van_der_corput_bound d hd
  refine ⟨max C1 1, lt_max_of_lt_left hC1pos, ?_⟩
  intro t β ht hb
  -- The two denominators we shall juggle
  have hden_pos : 0 < t * β ^ ((1:ℝ)/(d:ℝ)) :=
    mul_pos ht (Real.rpow_pos_of_pos hb _)
  -- `(β t^d)^{1/d} = t β^{1/d}`
  have hpow : (β * t ^ d) ^ ((1:ℝ)/(d:ℝ)) = t * β ^ ((1:ℝ)/(d:ℝ)) := by
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    rw [Real.mul_rpow (le_of_lt hb) (pow_nonneg (le_of_lt ht) d)]
    have htd : (t ^ d : ℝ) = t ^ (d:ℝ) := (Real.rpow_natCast t d).symm
    rw [htd, ← Real.rpow_mul (le_of_lt ht)]
    have hdr : (d:ℝ) * ((1:ℝ)/(d:ℝ)) = 1 := by field_simp
    rw [hdr, Real.rpow_one, mul_comm]
  -- The monomial phase `φ(s) = -β t^d s^d`
  set φ : ℝ → ℝ := fun s => -(β * t ^ d * s ^ d) with hφdef
  have hcont : ContDiffOn ℝ d φ (Set.Icc 0 1) := by rw [hφdef]; fun_prop
  have hderiv_eq : ∀ x : ℝ, iteratedDeriv d φ x = -((β * t ^ d) * (d.descFactorial d : ℝ)) := by
    intro x
    rw [hφdef]
    rw [iteratedDeriv_fun_neg]
    rw [iteratedDeriv_const_mul_field]
    rw [show iteratedDeriv d (fun s : ℝ => s ^ d) x = (d.descFactorial d : ℝ) from by
      rw [iteratedDeriv_pow, Nat.sub_self, pow_zero, mul_one]]
  -- `d.descFactorial d = d!` is at least `1`
  have hfac : (1:ℝ) ≤ (d.descFactorial d : ℝ) := by
    rw [Nat.descFactorial_self]
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos d))
  -- so `|φ^{(d)}| = β t^d · d! ≥ β t^d` everywhere
  have hlow : ∀ x ∈ Set.Icc (0:ℝ) 1, β * t ^ d ≤ |iteratedDeriv d φ x| := by
    intro x hx
    rw [hderiv_eq x]
    have hp : 0 < β * t ^ d := by positivity
    have hy : 0 ≤ (d.descFactorial d : ℝ) := by positivity
    rw [abs_neg, abs_mul, abs_of_pos hp, abs_of_nonneg hy]
    nlinarith [hfac, hp]
  -- van der Corput with `lam = β t^d`
  have hvc : ‖∫ s in (0:ℝ)..1, Complex.exp (Complex.I * (φ s : ℂ))‖
      ≤ C1 / (β * t ^ d) ^ ((1:ℝ)/(d:ℝ)) := by
    refine hC1 (a := 0) (b := 1) (φ := φ) (lam := β * t ^ d) (by norm_num) ?_ hcont hlow
    positivity
  -- identify the given integrand with `exp(I φ)`
  have hcong : (∫ s in (0:ℝ)..1, Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I))
      = ∫ s in (0:ℝ)..1, Complex.exp (Complex.I * (φ s : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have harg : ((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I = Complex.I * (φ s : ℂ) := by
      rw [hφdef]; ring
    change Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (Complex.I * (φ s : ℂ))
    rw [harg]
  have hA : ‖∫ s in (0:ℝ)..1, Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)‖
      ≤ max C1 1 / (t * β ^ ((1:ℝ)/(d:ℝ))) := by
    rw [hcong]
    rw [hpow] at hvc
    exact le_trans hvc (div_le_div_of_nonneg_right (le_max_left C1 1) (le_of_lt hden_pos))
  have hB : ‖(∫ s in (0:ℝ)..1, Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)) - 1‖
      ≤ max C1 1 * t ^ d * β := by
    set E : ℝ → ℂ := fun s => Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I) with hEdef
    have hEcont : Continuous E := by rw [hEdef]; fun_prop
    have hEint : IntervalIntegrable E volume (0:ℝ) 1 := hEcont.intervalIntegrable 0 1
    have hone : (∫ s in (0:ℝ)..1, (1:ℂ)) = 1 := by
      rw [intervalIntegral.integral_const]; simp
    have hsub : (∫ s in (0:ℝ)..1, E s) - 1 = ∫ s in (0:ℝ)..1, (E s - 1) := by
      rw [intervalIntegral.integral_sub hEint intervalIntegrable_const, hone]
    -- pointwise mean value bound `|e^{iθ} - 1| ≤ |θ|`
    have hbdd : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0:ℝ) 1 → ‖E s - 1‖ ≤ β * t ^ d := by
      apply Filter.Eventually.of_forall
      intro s hs
      have hs0 : 0 ≤ s := le_of_lt hs.1
      have hsd : s ^ d ≤ 1 := pow_le_one₀ hs0 hs.2
      have hst : 0 ≤ β * t ^ d * s ^ d := by positivity
      have h1 : ‖E s - 1‖ ≤ β * t ^ d * s ^ d := by
        rw [hEdef]
        have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(β * t ^ d * s ^ d))
        calc ‖Complex.exp (((-(β * t ^ d * s ^ d) : ℝ) : ℂ) * Complex.I) - 1‖
            = ‖Complex.exp (Complex.I * ((-(β * t ^ d * s ^ d) : ℝ) : ℂ)) - 1‖ := by
                congr 1; rw [mul_comm]
          _ ≤ |-(β * t ^ d * s ^ d)| := by simpa [Real.norm_eq_abs] using h
          _ = β * t ^ d * s ^ d := by rw [abs_neg, abs_of_nonneg hst]
      have h2 : 0 ≤ β * t ^ d := by positivity
      nlinarith [h1, hsd, h2]
    have hkey : ‖∫ s in (0:ℝ)..1, (E s - 1)‖ ≤ β * t ^ d := by
      have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := 1)
        (f := fun s => E s - 1) (g := fun _ => β * t ^ d) (by norm_num) hbdd
        (continuous_const.intervalIntegrable 0 1)
      simpa using h
    have hfin : β * t ^ d ≤ max C1 1 * t ^ d * β := by
      have h1 : (1:ℝ) ≤ max C1 1 := le_max_right C1 1
      have ht0 : (0:ℝ) ≤ t ^ d := pow_nonneg (le_of_lt ht) d
      have hb0 : (0:ℝ) ≤ β := le_of_lt hb
      calc β * t ^ d = 1 * t ^ d * β := by ring
        _ ≤ max C1 1 * t ^ d * β :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 ht0) hb0
    rw [hsub]
    exact le_trans hkey hfin
  exact ⟨hA, hB⟩

end Commons.Analysis.Oscillatory
