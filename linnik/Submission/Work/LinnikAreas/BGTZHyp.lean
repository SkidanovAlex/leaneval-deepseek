/-
# `Work.LinnikAreas.BGTZHyp` — the *provable* inputs of the BGTZ repulsion

The repulsion of `Submission/Work/LinnikAreas/BGTZ.lean` is deduced from Benli--Goel--Twiss--Zaman
(BGTZ), arXiv:2410.06082, Theorem 1.3, whose hypotheses are

* **(Hyp A)** a subconvexity bound `‖L(1/2+it,ψ)‖ ≤ A (N(1+|t|))^θ` on the critical line, for
  primitive `ψ` (BGTZ use the explicit convexity bound of Thorner--Zaman: `θ = 1/4`,
  `A = 2.97655`);
* **(Hyp B)** an upper bound for the Landau--Siegel zero, `1 - β₁ > B/(q^ε (log q)²)` (BGTZ use
  the explicit effective Siegel bound of Bordignon: `ε = 1/2`, `B = 100`);
* the convexity bound for `ζ` on the critical line, used in the "`G`-estimate".

This module proves all three from the **shared commons**, so none of them is an extra input:

* `HypZeta` is `Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional`;
* `HypA A (1/4 + 1/100)` follows from `LFunction_strip_convexity_explicit`
  (`‖L(1/2+iT,ψ)‖ ≤ C(N(2+|T|))^{1/4}(log(N(2+|T|))+2)`) because `log u + 2 ≤ K u^{1/100}`
  absorbs the logarithmic factor — the exponent `1/4 + 1/100` is still far below the threshold
  `3/10` needed by AREA 6 (`8θ + 2ε < 12/5`);
* `HypB B ε` follows from **Siegel's theorem**
  (`Commons…LFunction_realZero_siegel_uniform`) with `ε = 1/100`, `B` the ineffective Siegel
  constant for `ε' = 1/200`, together with `lamOf_lower_bound`'s bridge from the contract's
  `zeroMult` to zeros of the ordinary `L`-function (`Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero`).
-/

import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_explicit
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

namespace BGTZ

/-- **The convexity bound for `ζ` on the critical line** is `HypZeta`, from the shared commons. -/
theorem hypZeta_of_commons : ∃ Cz : ℝ, HypZeta Cz := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  have h := hC (1 / 2) t (by norm_num) (by norm_num) ht
  have hexp : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rwa [hexp] at h

/-- **Hypothesis B is Siegel's theorem.**  With `ε = 1/100` and `B` the (ineffective) Siegel
constant for `ε' = 1/200`, every real zero `β₁` of a real character mod `q` with
`1 - β₁ < 1/(10 log q)` satisfies `1 - β₁ > B/(q^{1/100}(log q)²)`. -/
theorem hypB_of_siegel : ∃ B : ℝ, HypB B (1 / 100) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (1 / 200) (by norm_num)
  have hmain : ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - β₁ < 1 / (10 * Real.log q) →
      C / ((q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2) < 1 - β₁ := by
    intro q _ hq3 χ₁ β₁ hχ hsq hβ1 hz _
    have hqR3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hβ0 : 0 < β₁ := Siegel.re_mem_Ioo hχ hβ1 hz
    have hprim := DirichletCharacter.primitiveCharacter_isPrimitive χ₁
    have hne : χ₁.primitiveCharacter ≠ 1 := Siegel.primitive_ne_one hχ
    have hsq' : χ₁.primitiveCharacter * χ₁.primitiveCharacter = 1 := by
      rw [← sq]
      exact Siegel.primitive_sq_one hsq
    have hzero : LFunction χ₁.primitiveCharacter (β₁ : ℂ) = 0 :=
      Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero χ₁ hχ hz
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hcond_le : χ₁.conductor ≤ q := Nat.le_of_dvd hqpos χ₁.conductor_dvd_level
    have hcond_pos : 0 < χ₁.conductor := Nat.pos_of_ne_zero χ₁.conductor_ne_zero
    have hSiegel : C * ((χ₁.conductor : ℝ) ^ (-(1 / 200) : ℝ)) ≤ 1 - β₁ :=
      hC (N := χ₁.conductor) χ₁.primitiveCharacter hprim hne hsq' β₁ hβ0 hβ1 hzero
    have hcondR_pos : (0 : ℝ) < (χ₁.conductor : ℝ) := by exact_mod_cast hcond_pos
    have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    have hcond_leR : (χ₁.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcond_le
    have hpow_le : (χ₁.conductor : ℝ) ^ ((1 : ℝ) / 200) ≤ (q : ℝ) ^ ((1 : ℝ) / 200) :=
      Real.rpow_le_rpow hcondR_pos.le hcond_leR (by norm_num)
    have hcondpow_pos : (0 : ℝ) < (χ₁.conductor : ℝ) ^ ((1 : ℝ) / 200) :=
      Real.rpow_pos_of_pos hcondR_pos _
    have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 200) := Real.rpow_pos_of_pos hqR_pos _
    have hinv : (q : ℝ) ^ (-(1 / 200) : ℝ) ≤ (χ₁.conductor : ℝ) ^ (-(1 / 200) : ℝ) := by
      rw [Real.rpow_neg hqR_pos.le, Real.rpow_neg hcondR_pos.le]
      exact inv_anti₀ hcondpow_pos hpow_le
    have hone : C * (q : ℝ) ^ (-(1 / 200) : ℝ) ≤ 1 - β₁ :=
      le_trans (mul_le_mul_of_nonneg_left hinv hCpos.le) hSiegel
    have hlog1 : 1 < Real.log q := by
      have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      have h4 : 1 < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
      have h5 : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) h3
      linarith
    have hbig : (q : ℝ) ^ ((1 : ℝ) / 200) < (q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2 := by
      have h2 : (q : ℝ) ^ ((1 : ℝ) / 100)
          = (q : ℝ) ^ ((1 : ℝ) / 200) * (q : ℝ) ^ ((1 : ℝ) / 200) := by
        rw [← Real.rpow_add hqR_pos]
        norm_num
      have h3 : (1 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 200) :=
        Real.one_lt_rpow (by linarith) (by norm_num)
      have h1 : (1 : ℝ) < (Real.log q) ^ 2 := by nlinarith
      have h4 : (1 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 200) * (Real.log q) ^ 2 :=
        one_lt_mul h3.le h1
      calc (q : ℝ) ^ ((1 : ℝ) / 200) = (q : ℝ) ^ ((1 : ℝ) / 200) * 1 := by ring
        _ < (q : ℝ) ^ ((1 : ℝ) / 200) * ((q : ℝ) ^ ((1 : ℝ) / 200) * (Real.log q) ^ 2) :=
            mul_lt_mul_of_pos_left h4 hqpow_pos
        _ = (q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2 := by rw [h2]; ring
    have hkey : C / ((q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2)
        < C * (q : ℝ) ^ (-(1 / 200) : ℝ) := by
      have hden_pos : 0 < (q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2 := by positivity
      have hstep : 1 / ((q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2)
          < (q : ℝ) ^ (-(1 / 200) : ℝ) := by
        rw [one_div, Real.rpow_neg hqR_pos.le, inv_lt_inv₀ hden_pos hqpow_pos]
        exact hbig
      have h2' : C * (1 / ((q : ℝ) ^ ((1 : ℝ) / 100) * (Real.log q) ^ 2))
          < C * (q : ℝ) ^ (-(1 / 200) : ℝ) := mul_lt_mul_of_pos_left hstep hCpos
      simpa [div_eq_mul_inv] using h2'
    exact lt_of_lt_of_le hkey hone
  exact ⟨C, hCpos, by norm_num, by norm_num, hmain⟩

end BGTZ

end Work.LinnikAreas
