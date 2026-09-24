import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive
import Submission.Commons.Analysis.Asymptotics.eventual_exp_neg_sqrt_log_div_log_modulus_le

open Filter Finset
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

noncomputable section

/-- **Siegel–Walfisz for primitive non-principal characters in the full power range.**

For every `A > 0` and every `C > 0`, eventually for every modulus `q ≤ (log x)^C` and every
primitive non-principal Dirichlet character `χ` modulo `q`,

`‖∑_{n ≤ x} Λ(n) χ(n)‖ ≤ x / (log x)^A`.

This follows from the uniform twisted von Mangoldt bound
`psiChi_uniform_bound_primitive C` (valid for moduli up to `(log x)^C`) together with the fact that
`exp (-c √(log x / log (q+2)))` decays faster than any power of `log x` uniformly for
`q ≤ (log x)^C` (`eventual_exp_neg_sqrt_log_div_log_modulus_le`). -/
theorem siegel_walfisz_chi_range :
    ∀ A C : ℝ, 0 < A → 0 < C →
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (x : ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ n ∈ Finset.range (x + 1),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
          (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A C hA hC
  obtain ⟨c, Cb, hc, hCb, x₀, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive C hC
  -- Choose the exponent used in the uniform zero-free input, at least `C` so that it
  -- dominates the range of moduli, and strictly larger than `A / 2` so that the
  -- exponential decay beats `x / (log x)^A`.
  set A₀ : ℝ := max C ((A + 1) / 2) with hA₀def
  have hA₀C : C ≤ A₀ := le_max_left _ _
  have hA₀pos : 0 < A₀ := lt_of_lt_of_le hC hA₀C
  have hA1 : A + 1 ≤ 2 * A₀ := by
    have h := le_max_right C ((A + 1) / 2)
    linarith
  obtain ⟨x₁, _hx₁, habs⟩ :=
    Commons.Analysis.Asymptotics.eventual_exp_neg_sqrt_log_div_log_modulus_le
      A₀ (2 * c) hA₀pos (by linarith)
  have hEv1 : ∀ᶠ x : ℕ in Filter.atTop, max x₀ x₁ ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (max x₀ x₁))
  have hEv2 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  have hEv3 : ∀ᶠ x : ℕ in Filter.atTop, Cb ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop Cb)
  filter_upwards [hEv1, hEv2, hEv3] with x hx1 hx2 hx3
  intro q _ hq χ hχprim hχ1ne
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hL1 : 1 ≤ L := hx2
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hCbLe : Cb ≤ L := hx3
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  -- The modulus range, transported to `L`
  have hqleC : (q : ℝ) ≤ L ^ C := by
    have hfl : ((⌊L ^ C⌋₊ : ℕ) : ℝ) ≤ L ^ C := Nat.floor_le (Real.rpow_nonneg hLnn C)
    have h2 : (q : ℝ) ≤ ((⌊L ^ C⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq
    linarith
  have hqleA₀ : (q : ℝ) ≤ L ^ A₀ :=
    le_trans hqleC (Real.rpow_le_rpow_of_exponent_le hL1 hA₀C)
  -- The twisted von Mangoldt bound
  have hmain := hbound (x : ℝ) (le_trans (le_max_left x₀ x₁) hx1) q χ hχ1ne hχprim hqleC
  -- The exponential decay beats every power of `log x`
  have hexp : Real.exp (-(c * Real.sqrt (L / Real.log ((q : ℝ) + 2)))) ≤ 1 / L ^ (2 * A₀) := by
    have h := habs (x : ℝ) (le_trans (le_max_right x₀ x₁) hx1) q hqleA₀
    have harg : -((2 * c) / 2) * Real.sqrt (L / Real.log ((q : ℝ) + 2))
        = -(c * Real.sqrt (L / Real.log ((q : ℝ) + 2))) := by ring
    rwa [harg] at h
  -- Reindex the target sum
  have hbridge : (∑ n ∈ Finset.range (x + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 ⌊(x : ℝ)⌋₊,
          χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    rw [Nat.floor_natCast]
    have hf0 : ((ArithmeticFunction.vonMangoldt 0 : ℝ) : ℂ) * χ ((0 : ℕ) : ZMod q) = 0 := by
      simp
    rw [Finset.range_eq_Ico]
    rw [show Finset.Ico 0 (x + 1) = insert 0 (Finset.Icc 1 x) by
        ext n; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.sum_insert (by simp [Finset.mem_Icc]), hf0, zero_add]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hbridge]
  -- Arithmetic: absorb the constant `Cb` into `L ^ (2 A₀ - A)`
  have hpow : Cb * L ^ A ≤ L ^ (2 * A₀) := by
    have h1 : Cb * L ^ A ≤ L * L ^ A :=
      mul_le_mul_of_nonneg_right hCbLe (Real.rpow_nonneg hLnn A)
    have h2 : L * L ^ A ≤ L ^ (2 * A₀) := by
      have h3 : L ≤ L ^ (2 * A₀ - A) := by
        have h4 := Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 2 * A₀ - A by linarith)
        simpa using h4
      have h5 : L * L ^ A ≤ L ^ (2 * A₀ - A) * L ^ A :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hLnn A)
      have h6 : L ^ (2 * A₀ - A) * L ^ A = L ^ (2 * A₀) := by
        rw [← Real.rpow_add hLpos (2 * A₀ - A) A]
        congr 1
        ring
      linarith [h5, h6.le, h6.ge]
    linarith
  have hfin : Cb * (x : ℝ) * (1 / L ^ (2 * A₀)) ≤ (x : ℝ) / L ^ A := by
    have hL2A0pos : 0 < L ^ (2 * A₀) := Real.rpow_pos_of_pos hLpos _
    have hLApos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos _
    rw [show Cb * (x : ℝ) * (1 / L ^ (2 * A₀)) = Cb * (x : ℝ) / L ^ (2 * A₀) by ring]
    rw [div_le_div_iff₀ hL2A0pos hLApos]
    calc Cb * (x : ℝ) * L ^ A = (Cb * L ^ A) * (x : ℝ) := by ring
      _ ≤ L ^ (2 * A₀) * (x : ℝ) := mul_le_mul_of_nonneg_right hpow hxnn
      _ = (x : ℝ) * L ^ (2 * A₀) := by ring
  calc ‖∑ n ∈ Finset.Icc 1 ⌊(x : ℝ)⌋₊,
          χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ Cb * (x : ℝ) * Real.exp (-(c * Real.sqrt (L / Real.log ((q : ℝ) + 2)))) := hmain
    _ ≤ Cb * (x : ℝ) * (1 / L ^ (2 * A₀)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (x : ℝ) / L ^ A := hfin

end

end Commons.NumberTheory.BombieriVinogradov
