import Mathlib
import Submission.Work.LinnikAreas.DhRepel.farZeroLambdaLower

namespace Work.LinnikAreas.DhRepel

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option linter.style.haveILetI false

noncomputable section

/-- **Wide off-axis repulsion.**  There is an absolute constant `c > 0` such that for every
sufficiently large modulus `q`, every non-principal character `χ` of level `q` and every zero `u`
of `L(s,χ)` whose imaginary part satisfies `1 ≤ |Im u| ≤ 10 log q` one has
`λ(u) = (1 - Re u) log q ≥ c`.

The proof is the classical de la Vallée Poussin zero-free region
`LFunction_zeroFree_offAxis_uniform` applied to the primitive character `ψ` inducing `χ`, which
gives `σ < 1 - c₁ / log (N (|t| + 2))` for every zero `σ + it` with `t ≠ 0`.  Here `N ≤ q` and
`|t| + 2 ≤ 10 log q + 2 ≤ q²` as soon as `q ≥ 10` (using `log q ≤ q - 1`), so that
`log (N (|t| + 2)) ≤ 3 log q` and the zero-free region gives `λ(u) ≥ c₁/3` with an absolute
constant; on the axis `t = 0` the Siegel zero prevents any such bound, which is exactly why the
hypothesis `1 ≤ |Im u|` is present. -/
theorem farZeroLambdaLowerWide : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
    1 ≤ |u.im| → |u.im| ≤ 10 * Real.log (q : ℝ) → c ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨c₁ / 3, by positivity, 10, ?_⟩
  intro q hq inst χ hχ u hz him1 himu
  -- the primitive character inducing `χ`
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hψne : χ.primitiveCharacter ≠ 1 := primitive_ne_one' hχ
  -- `u` is a zero of the ordinary `L`-function of `χ.primitiveCharacter`
  have hLz : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    LFunction_primitive_eq_zero χ hχ hz
  -- basic numerical facts about the modulus `q ≥ 10`
  have hqposN : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq10 : (10 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqposN
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  -- the imaginary part does not vanish
  have himne : u.im ≠ 0 := by
    intro h
    rw [h] at him1
    norm_num at him1
  -- the conductor lies between `1` and `q`
  have hN1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hNq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqposN χ.conductor_dvd_level
  -- `N (|t| + 2) ≤ q³`, because `|t| + 2 ≤ 10 log q + 2 ≤ q²`
  have harg : (χ.conductor : ℝ) * (|u.im| + 2) ≤ (q : ℝ) ^ 3 := by
    have h1 : |u.im| + 2 ≤ 10 * Real.log (q : ℝ) + 2 := by linarith [himu]
    have h2 : 10 * Real.log (q : ℝ) + 2 ≤ (q : ℝ) ^ 2 := by
      have h3 : Real.log (q : ℝ) ≤ (q : ℝ) - 1 := Real.log_le_sub_one_of_pos hqpos
      have h4 : (0 : ℝ) ≤ ((q : ℝ) - 10) * (q : ℝ) := mul_nonneg (by linarith) hqpos.le
      nlinarith [h3, h4]
    have h5 : (0 : ℝ) < |u.im| + 2 := by positivity
    calc (χ.conductor : ℝ) * (|u.im| + 2) ≤ (q : ℝ) * ((q : ℝ) ^ 2) :=
          mul_le_mul hNq (le_trans h1 h2) h5.le hqpos.le
      _ = (q : ℝ) ^ 3 := by ring
  have hlogt : Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ 3 * Real.log (q : ℝ) := by
    calc Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ Real.log ((q : ℝ) ^ 3) :=
          Real.log_le_log (by positivity) harg
      _ = 3 * Real.log (q : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hargpos : 0 < Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
    apply Real.log_pos
    nlinarith [hN1, abs_nonneg u.im]
  -- the zero-free region pushes `Re u` away from `1`
  have hkey : c₁ / (3 * Real.log (q : ℝ)) < 1 - u.re := by
    have hL0' : DirichletCharacter.LFunction χ.primitiveCharacter
        ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = 0 := by
      rw [Complex.re_add_im u]; exact hLz
    have hlt : u.re < 1 - c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
      by_contra hcon
      rw [not_lt] at hcon
      exact (hc₁ χ.primitiveCharacter hψprim hψne u.re u.im himne hcon) hL0'
    have hmono : c₁ / (3 * Real.log (q : ℝ))
        ≤ c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
      rw [div_le_div_iff₀ (by positivity) hargpos]
      nlinarith [hlogt, hc₁pos]
    linarith
  -- multiply by `log q > 0` and simplify
  rw [Work.LinnikContract.lamOf]
  have hmul : c₁ / (3 * Real.log (q : ℝ)) * Real.log (q : ℝ) = c₁ / 3 := by
    field_simp
  rw [← hmul]
  exact le_of_lt (mul_lt_mul_of_pos_right hkey hlogpos)

end

end Work.LinnikAreas.DhRepel
