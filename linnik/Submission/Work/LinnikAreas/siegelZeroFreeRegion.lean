import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

/-!
# The Siegel zero-free region

`Work.LinnikAreas.siegelZeroFreeRegion`: there is an absolute constant `c > 0` such that, for
every level `q`, every non-principal Dirichlet character `χ` modulo `q` and every zero `ρ` of
`L(s, χ)` (i.e. `zeroMult χ ρ ≠ 0`) with `|Im ρ| ≤ 1`, either `ρ` is a *real zero of a real
character* (`χ² = 1` and `Im ρ = 0`) or else `λ(ρ) = (1 - Re ρ) log q ≥ c`.

This is the classical uniform zero-free region, in the `λ`-normalisation used by the Linnik
contract (`λ = (1 - Re ρ) 𝓛`, `𝓛 = log q`): the exceptional case is *excluded by hypothesis*,
so the statement is a genuine zero-free region rather than Siegel's theorem.

The proof combines the two uniform zero-free regions of the commons library,

* `LFunction_zeroFree_uniform_realAxis` — `L(σ, χ) ≠ 0` for `σ ≥ 1 - c₀ / log (2N)`,
  for primitive `χ` mod `N` with `χ ≠ 1` and `χ² ≠ 1` (real zeros of real characters),
* `LFunction_zeroFree_offAxis_uniform` — `L(σ + it, χ) ≠ 0` for `σ ≥ 1 - c₁ / log (N (|t| + 2))`,
  `t ≠ 0`, for primitive `χ ≠ 1` (all other zeros),

transferred from the primitive character `χ.primitiveCharacter` inducing `χ` (which is what
`zeroMult` uses) to level `q`, using `conductor ∣ q` and `2 ≤ conductor` so that
`log q ≥ log (conductor)` and the constants survive.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas

set_option linter.style.haveILetI false

/-! ## Preparatory facts about the primitive character and the region -/

/-- The primitive character inducing a non-principal `χ` is non-principal. -/
private lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine hχ ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- The conductor of a non-principal character is at least `2`. -/
private lemma two_le_conductor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 2 ≤ χ.conductor := by
  have h0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have h1 : χ.conductor ≠ 1 := fun h =>
    hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h)
  omega

/-- A `zeroMult`-zero `ρ` is a zero of the completed `L`-function of the primitive
character inducing `χ`, and that zero lies in the critical strip. -/
private lemma re_mem_strip_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hχ : χ ≠ 1) (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hlt : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hz
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
    (primitiveCharacter_ne_one hχ) (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (apply_eq_zero_of_analyticOrderNatAt_ne_zero hlt)

/-- A `zeroMult`-zero `ρ` is a zero of the (ordinary) `L`-function of the primitive character
inducing `χ`. -/
private lemma LFunction_primitive_eq_zero_of_zeroMult {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) :
    @DirichletCharacter.LFunction χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter ρ = 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hstrip := re_mem_strip_of_zeroMult hχ hz
  have hlt : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hz
  have horder :=
    Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
      χ.primitiveCharacter (primitiveCharacter_ne_one hχ) hstrip.1 hstrip.2
  have hL : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) ρ ≠ 0 := by
    rw [horder]; exact hlt
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hL

/-- `χ² ≠ 1` passes to the primitive character: if `χ * χ ≠ 1` then the primitive character
inducing `χ` also has non-trivial square.  (`changeLevel` is a monoid homomorphism.) -/
private lemma primitiveCharacter_mul_self_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ * χ ≠ 1) : χ.primitiveCharacter * χ.primitiveCharacter ≠ 1 := by
  intro hc
  refine h ?_
  have hmap := congrArg (DirichletCharacter.changeLevel χ.conductor_dvd_level) hc
  simpa only [map_mul, map_one, DirichletCharacter.changeLevel_primitiveCharacter] using hmap

/-! ## The arithmetic of the two branches

Both branches produce a zero `ρ` with `1 - Re ρ > c / log (…)` for a positive constant `c`
and a logarithm of a quantity between `conductor` and `3 · conductor`; since
`2 ≤ conductor ≤ q`, the logarithm is at least `(1/3) log q` (up to the stated slack), and
`λ(ρ) = (1 - Re ρ) log q` is bounded below by `min c₀ c₁ / 3`. -/

/-- Real branch: `1 - Re ρ > c₀ / log (2d)` with `2 ≤ d ≤ q` implies
`min c₀ c₁ / 3 ≤ (1 - Re ρ) log q`. -/
private lemma arithReal {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {d q : ℕ}
    (hd : 2 ≤ d) (hdq : d ≤ q) {x : ℝ}
    (hlt : c₀ / Real.log (2 * (d : ℝ)) < x) :
    min c₀ c₁ / 3 ≤ x * Real.log q := by
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hlog2d : 0 < Real.log (2 * (d : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * d)
  have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos hd1
  have hx : 0 < x := lt_trans (div_pos hc₀ hlog2d) hlt
  have hlogq : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hdq)
  have hlog2dle : Real.log (2 * (d : ℝ)) ≤ 2 * Real.log (d : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h : Real.log 2 ≤ Real.log (d : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    linarith
  have hhalf : c₀ / 2 ≤ x * Real.log (d : ℝ) := by
    have h1 : c₀ / Real.log (2 * (d : ℝ)) * Real.log (d : ℝ)
        < x * Real.log (d : ℝ) := mul_lt_mul_of_pos_right hlt hlogd
    have h2 : c₀ / 2 ≤ c₀ / Real.log (2 * (d : ℝ)) * Real.log (d : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2d]
      have h3 := mul_le_mul_of_nonneg_left hlog2dle (show (0 : ℝ) ≤ c₀ / 2 by linarith)
      calc c₀ / 2 * Real.log (2 * (d : ℝ)) ≤ c₀ / 2 * (2 * Real.log (d : ℝ)) := h3
        _ = c₀ * Real.log (d : ℝ) := by ring
    linarith
  have hmin : min c₀ c₁ / 3 ≤ c₀ / 2 := by
    have h := min_le_left c₀ c₁
    linarith
  calc min c₀ c₁ / 3 ≤ c₀ / 2 := hmin
    _ ≤ x * Real.log (d : ℝ) := hhalf
    _ ≤ x * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlogq hx.le

/-- Complex branch: `1 - Re ρ > c₁ / log (d (|t| + 2))` with `2 ≤ d ≤ q` and `|t| ≤ 1` implies
`min c₀ c₁ / 3 ≤ (1 - Re ρ) log q`. -/
private lemma arithComplex {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {d q : ℕ}
    (hd : 2 ≤ d) (hdq : d ≤ q) {x t : ℝ} (ht : |t| ≤ 1)
    (hlt : c₁ / Real.log ((d : ℝ) * (|t| + 2)) < x) :
    min c₀ c₁ / 3 ≤ x * Real.log q := by
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hD1 : (1 : ℝ) < (d : ℝ) * (|t| + 2) := by
    have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
    nlinarith [hd1]
  have hDpos : 0 < (d : ℝ) * (|t| + 2) := by linarith
  have hlogD : 0 < Real.log ((d : ℝ) * (|t| + 2)) := Real.log_pos hD1
  have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos hd1
  have hx : 0 < x := lt_trans (div_pos hc₁ hlogD) hlt
  have hlogq : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hdq)
  have h3d : (d : ℝ) * (|t| + 2) ≤ 3 * (d : ℝ) := by
    have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
    nlinarith [ht]
  have hlog3d : Real.log ((d : ℝ) * (|t| + 2)) ≤ Real.log (3 * (d : ℝ)) :=
    Real.log_le_log hDpos h3d
  have hlog3 : Real.log (3 * (d : ℝ)) ≤ 3 * Real.log (d : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have h2 : Real.log 2 ≤ Real.log (d : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    have h3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith
  have hstep : c₁ / Real.log (3 * (d : ℝ)) < x := by
    have hinv : 1 / Real.log (3 * (d : ℝ)) ≤ 1 / Real.log ((d : ℝ) * (|t| + 2)) :=
      one_div_le_one_div_of_le hlogD hlog3d
    calc c₁ / Real.log (3 * (d : ℝ))
        = c₁ * (1 / Real.log (3 * (d : ℝ))) := by ring
      _ ≤ c₁ * (1 / Real.log ((d : ℝ) * (|t| + 2))) := mul_le_mul_of_nonneg_left hinv hc₁.le
      _ = c₁ / Real.log ((d : ℝ) * (|t| + 2)) := by ring
      _ < x := hlt
  have hthird : c₁ / 3 ≤ x * Real.log (d : ℝ) := by
    have hlog3pos : 0 < Real.log (3 * (d : ℝ)) := by
      apply Real.log_pos
      nlinarith [hd1]
    have h1 : c₁ / Real.log (3 * (d : ℝ)) * Real.log (d : ℝ) < x * Real.log (d : ℝ) :=
      mul_lt_mul_of_pos_right hstep hlogd
    have h2 : c₁ / 3 ≤ c₁ / Real.log (3 * (d : ℝ)) * Real.log (d : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog3pos]
      have h3 := mul_le_mul_of_nonneg_left hlog3 (show (0 : ℝ) ≤ c₁ / 3 by linarith)
      calc c₁ / 3 * Real.log (3 * (d : ℝ)) ≤ c₁ / 3 * (3 * Real.log (d : ℝ)) := h3
        _ = c₁ * Real.log (d : ℝ) := by ring
    linarith
  have hmin : min c₀ c₁ / 3 ≤ c₁ / 3 := by
    have h := min_le_right c₀ c₁
    linarith
  calc min c₀ c₁ / 3 ≤ c₁ / 3 := hmin
    _ ≤ x * Real.log (d : ℝ) := hthird
    _ ≤ x * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlogq hx.le

/-! ## The Siegel zero-free region -/

theorem siegelZeroFreeRegion : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → χ ≠ 1 →
    (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
    c ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨min c₀ c₁ / 3, by positivity, 1, ?_⟩
  intro q hq hqne χ ρ hz him hχ hexc
  haveI : NeZero q := hqne
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd2 : 2 ≤ χ.conductor := two_le_conductor hχ
  have hdq : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hL : @DirichletCharacter.LFunction χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter ρ = 0 := LFunction_primitive_eq_zero_of_zeroMult χ hχ hz
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hψne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have hlam : Work.LinnikContract.lamOf q ρ = (1 - ρ.re) * Real.log q := rfl
  rw [hlam]
  by_cases him0 : ρ.im = 0
  · -- real zero of a *complex* character: `χᵖʳⁱᵐ² ≠ 1` rules out the exceptional case
    have hχ2 : χ ^ 2 ≠ 1 := by
      rcases hexc with h | h
      · exact h
      · exact absurd him0 h
    have hψ2 : χ.primitiveCharacter * χ.primitiveCharacter ≠ 1 :=
      primitiveCharacter_mul_self_ne_one (by simpa only [pow_two] using hχ2)
    have hρeq : ρ = (ρ.re : ℂ) := by
      refine Complex.ext ?_ ?_ <;> simp [him0]
    have hzero : DirichletCharacter.LFunction χ.primitiveCharacter (ρ.re : ℂ) = 0 := by
      rw [← hρeq]; exact hL
    have hcon := hc₀ χ.conductor χ.primitiveCharacter hψprim hψne hψ2 ρ.re
    have hlt : c₀ / Real.log (2 * (χ.conductor : ℝ)) < 1 - ρ.re := by
      by_contra hle
      rw [not_lt] at hle
      exact hcon (by linarith) hzero
    exact arithReal hc₀pos hc₁pos hd2 hdq hlt
  · -- off-axis zero: the uniform off-axis zero-free region applies
    have hρeq : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
    have hzero : DirichletCharacter.LFunction χ.primitiveCharacter
        ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I) = 0 := by
      rw [← hρeq]; exact hL
    have hcon := hc₁ χ.primitiveCharacter hψprim hψne ρ.re ρ.im him0
    have hlt : c₁ / Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by
      by_contra hle
      rw [not_lt] at hle
      exact hcon (by linarith) hzero
    exact arithComplex hc₀pos hc₁pos hd2 hdq him hlt

end Work.LinnikAreas
