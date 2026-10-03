/-
# `Submission.Work.FIArea6Hecke.R.Sharp.Chi4LSeriesOffAxisLogDerivReBound`

The **off-axis logarithmic-derivative bound for the `L`-series of `χ₄`** (the quadratic
character modulo `4`, here called `axisChi4`):

  `-Re(L'/L)(σ + iτ) ≤ C·(log(2 + |τ|) + 1)`   for `1 < σ ≤ 2` and every real `τ`,

with an absolute constant `C > 0`.

The proof splits the strip `1 < σ ≤ 2` at `σ = 5/4`:

* on `1 < σ ≤ 5/4` the `L`-series of `χ₄` is the `L`-function of the primitive character
  `chi4C : DirichletCharacter ℂ 4`, and the uniform regular bound
  `LFunction_logDeriv_re_regular_uniform` (proved in `Submission.Commons`, from the Hadamard
  partial fractions of the completed `L`-function and the vertical digamma bound) gives
  `-Re(L'/L) ≤ 8(log 4 + log(2+|τ|) + 1)`;
* on `5/4 ≤ σ ≤ 2` the trivial von Mangoldt-series bound
  `logDeriv_LFunction_norm_le_of_one_lt_re`, `‖L'/L‖ ≤ 1/(σ-1) + C ≤ 4 + C`, suffices, and it
  needs neither primitivity nor non-triviality.

Since `log (2 + |τ|) ≥ 0` on the whole range, both are absorbed by `C·(log(2+|τ|) + 1)`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Hecke.R.Sharp

open Complex
open scoped Topology BigOperators

noncomputable section

/-! ## Primitivity of the character `chi4C : DirichletCharacter ℂ 4` -/

/-- `χ₄` takes the value `-1` at `3`. -/
private lemma chi4C_apply_three : chi4C (3 : ZMod 4) = -1 := by
  have h : ZMod.χ₄ (3 : ZMod 4) = (-1 : ℤ) := by decide
  simp only [chi4C, MulChar.ringHomComp_apply, h]
  norm_num

/-- The character `chi4C` (the quadratic character modulo `4` with values in `ℂ`) is primitive:
it is nontrivial and does not factor through the reduction `ZMod 4 → ZMod 2`, because it takes
the value `-1` at `3 = -1`. -/
private lemma chi4C_isPrimitive_local : chi4C.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : chi4C.conductor ∣ 4 := DirichletCharacter.conductor_dvd_level chi4C
  have hne1 : chi4C.conductor ≠ 1 := by
    intro h
    have : chi4C = (1 : DirichletCharacter ℂ 4) :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h
    exact chi4C_ne_one this
  have hne2 : chi4C.conductor ≠ 2 := by
    intro h
    have hfac : DirichletCharacter.FactorsThrough chi4C 2 := by
      rw [← h]; exact DirichletCharacter.conductor_mem_conductorSet chi4C
    obtain ⟨hd, χ₀, hχ⟩ := hfac
    have h1 : (DirichletCharacter.changeLevel hd χ₀) ((3 : ℤ) : ZMod 4)
        = χ₀ ((3 : ℤ) : ZMod 2) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ₀) hd (by norm_num)
    have h2 : χ₀ (((3 : ℤ)) : ZMod 2) = (1 : ℂ) := by
      have : (((3 : ℤ)) : ZMod 2) = 1 := by decide
      rw [this, MulChar.map_one]
    have h3 : chi4C (3 : ZMod 4) = 1 := by
      rw [hχ]; exact h1.trans h2
    rw [chi4C_apply_three] at h3
    norm_num at h3
  obtain ⟨n, hn, hc⟩ : ∃ n ≤ 2, chi4C.conductor = 2 ^ n :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num)).mp (by simpa using hdvd)
  interval_cases n
  · exact absurd hc hne1
  · exact absurd hc hne2
  · rw [hc]; norm_num

/-! ## Transfer of the logarithmic derivative to the entire `L`-function -/

/-- On `Re s > 1` the logarithmic derivative of the naive `L`-series of `χ₄` is that of the
entire Dirichlet `L`-function `chi4C.LFunction`. -/
private lemma logDeriv_LSeries_axisChi4_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    logDeriv (LSeries Work.FIArea6Hecke.R.axisChi4) s = logDeriv chi4C.LFunction s := by
  have hd : deriv (LSeries Work.FIArea6Hecke.R.axisChi4) s = deriv chi4C.LFunction s := by
    rw [← Work.FIArea6Hecke.R.LSeries_chi4C_eq]
    exact (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi4C hs).symm
  rw [logDeriv_apply, logDeriv_apply, hd, Work.FIArea6Hecke.R.LSeries_axisChi4_eq_LFunction hs]

/-! ## The main bound -/

theorem Chi4LSeriesOffAxisLogDerivReBound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / LSeries Work.FIArea6Hecke.R.axisChi4 ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ C * (Real.log (2 + |τ|) + 1) := by
  obtain ⟨Cn, hCnpos, hn⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
  refine ⟨max 26 (4 + Cn), lt_max_iff.mpr (Or.inl (by norm_num)), ?_⟩
  intro σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : 1 < s.re := by rw [hsdef]; simp; exact hσ1
  have hkey : (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) s
      / LSeries Work.FIArea6Hecke.R.axisChi4 s).re
      = (-logDeriv (chi4C.LFunction) s).re := by
    rw [neg_div, ← logDeriv_apply (LSeries Work.FIArea6Hecke.R.axisChi4) s,
        logDeriv_LSeries_axisChi4_eq_LFunction hsre]
  rw [hkey]
  have hlogpos : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hL1 : (1 : ℝ) ≤ Real.log (2 + |τ|) + 1 := by linarith
  have hss : s = (σ : ℂ) + Complex.I * (τ : ℂ) := by rw [hsdef]; ring
  have hm : 26 ≤ max 26 (4 + Cn) := le_max_left _ _
  have hm2 : 4 + Cn ≤ max 26 (4 + Cn) := le_max_right _ _
  by_cases hle : σ ≤ 5 / 4
  · have h1 := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_re_regular_uniform
      chi4C chi4C_ne_one chi4C_isPrimitive_local σ τ hσ1 hle
    have h1' : (-logDeriv (chi4C.LFunction) s).re
        ≤ 8 * (Real.log 4 + Real.log (2 + |τ|) + 1) := by
      rw [hss]
      simpa using h1
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      have h2 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        ring
      linarith
    calc (-logDeriv (chi4C.LFunction) s).re
        ≤ 8 * (Real.log 4 + Real.log (2 + |τ|) + 1) := h1'
      _ ≤ max 26 (4 + Cn) * (Real.log (2 + |τ|) + 1) := by
          nlinarith [hlog4, hlogpos, hm]
  · push Not at hle
    have h2 := hn 4 chi4C s hsre
    have hsr : s.re = σ := by rw [hsdef]; simp
    have h5 : 1 / (s.re - 1) ≤ 4 := by
      rw [hsr]
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2' : (-logDeriv (chi4C.LFunction) s).re ≤ 4 + Cn := by
      have h3 : (-logDeriv (chi4C.LFunction) s).re ≤ ‖logDeriv (chi4C.LFunction) s‖ := by
        have := Complex.re_le_norm (-(logDeriv (chi4C.LFunction) s))
        rwa [norm_neg] at this
      linarith
    calc (-logDeriv (chi4C.LFunction) s).re ≤ 4 + Cn := h2'
      _ ≤ max 26 (4 + Cn) * (Real.log (2 + |τ|) + 1) := by
          nlinarith [hm2, hL1, hCnpos.le]

end

end Work.FIArea6Hecke.R.Sharp
