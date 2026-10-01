/-
# ZeroFreeTables/HB95plus/Main — the `h ≥ 5` half of HB Theorem 1, derivation core

This module contains the *derivation core* of the `h ≥ 5` case of Heath-Brown's Theorem 1
(the `h5plus` clause of `Work.ZeroFreeTables.HBTheorem1_complex`), in the shape in which the
target theorem consumes it:

    ∃ q₀, ∀ q ≥ q₀, ∀ [NeZero q] (χ₁ ρ₁), IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ →
      348/1000 ≤ lamOf q ρ₁ .

## The argument

For `χ₁` of order `h ≥ 5` the powers `χ₁, χ₁², χ₁³, χ₁⁴` are four *distinct non-principal*
characters, so the pointwise positivity `(3+10cos θ)²(9+10cos θ)² ≥ 0` applied to the unit
point `z = χ₁(n) n^{-iγ₁}` produces the five-term combination

  `0 ≤ 14379·K(β,χ₀) + 24480·K(β+iγ₁,χ₁) + 14900·K(β+2iγ₁,χ₁²) + 6000·K(β+3iγ₁,χ₁³)
        + 1250·K(β+4iγ₁,χ₁⁴)`,       (★)
  `K(s,χ) = Σ'_n Λ(n)·Re(χ(n)/n^s)·f(log n/L)`,

which is `ksum_trigPoly_nonneg` for the Chebyshev polynomial `(3+10x)²(9+10x)²` (see
`c95_hP` below).  Bounding the five terms by
* `K(β,χ₀) ≤ L·F(λ*) + f(0)εL` (`Ksum_principal_le`), with `L·(1-β) = λ*`,
* `K(β+iγ₁,χ₁) ≤ -L·F(λ₁-λ*) + f(0)(s+ε)L` (`Ksum_le_single_of_L52_phi`), retaining the zero
  `ρ₁` in the window,
* `K(β+ikγ₁,χ₁ᵏ) ≤ f(0)(s+ε)L` for `k = 2,3,4` (`Ksum_le_self_of_L52_phi`), dropping the
  window zeros — legitimate because by `IsMin1WideAt 10` every zero has `λ ≥ λ₁`, and dropping
  a term needs only `Re F ≥ 0`, which holds at arguments of non-negative real part
  (`TestFn.Fc_re_nonneg`),

and using `F(λ₁-λ*) ≥ F(1/2 - 1/4) = F(1/4)` (with `F` decreasing, `λ₁ ≤ 0.348`, `λ* = 0.8`),
one gets a contradiction unless `λ₁ ≥ 0.348`.  The two cases are
* **Case A** (`orderOf (χ₁ᵏ) ≤ log q` for `k ≤ 4`): the `L52Hyp` bound is available with
  `s = 1/8` (`L52Hyp_ord_le`); take `λ* = λ₁`, so `F(λ₁-λ*) = F(0) = 8/9` exactly and only
  `∫e^{λ₁t}f ≤ ∫e^{0.348t}f` is needed (margin `≈ 0.027` with the test function `tf72T (3/4)`).
* **Case B**: four `K`-sum bounds with `s = 1/6` in general; take `λ* = λ₁ + 1/4`.  The extra
  input `λ₂ ≥ 0.8` (every zero other than `ρ₁` has `λ ≥ 0.8`) comes from HB Lemma 6.2 —
  `Commons.NumberTheory.Linnik.lemma6_2_assembly`, applied to the pair `(ρ₁, ρ₂)` with `ρ₂`
  the `λ`-minimal other zero, again with `IsMin1WideAt 10` supplying the dropped zeros.
  Margin at `λ₁ = 0.348`: `≈ 0.005` (with `tf72T (3/4)`), and `≈ 0.018` for the `λ₂`-bound
  with `tf72T (17/20)`.

The *numerical* facts (the integrals of `e^{±ct}f` against `tf72f`) are the only analytic
inputs left; they are elementary (an explicit antiderivative plus `exp` bounds) and are
requested separately.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.lemma6_2_assembly

namespace Work.ZeroFreeTables

noncomputable section

open scoped BigOperators

/-! ## The positivity polynomial `(3+10x)²(9+10x)²` -/

/-- The coefficients of `(3+10x)²(9+10x)²` in the Chebyshev basis
(`T₀,T₁,T₂,T₃,T₄`) — HB (9.15). -/
def c95 : ℕ → ℝ := fun k =>
  if k = 0 then 14379 else if k = 1 then 24480 else if k = 2 then 14900
  else if k = 3 then 6000 else if k = 4 then 1250 else 0

theorem c95_nonneg (k : ℕ) : 0 ≤ c95 k := by
  unfold c95
  split_ifs <;> norm_num

theorem cheb_three (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (3:ℤ)).eval x = 4*x^3 - 3*x := by
  have h3 : Polynomial.Chebyshev.T ℝ (3:ℤ)
      = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (2:ℤ) - Polynomial.Chebyshev.T ℝ (1:ℤ) := by
    have h := Polynomial.Chebyshev.T_add_two (R := ℝ) (n := (1:ℤ))
    simpa only [show (1:ℤ)+2 = 3 from by norm_num, show (1:ℤ)+1 = 2 from by norm_num] using h
  simp only [h3, Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.T_two, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow]
  ring

theorem cheb_four (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (4:ℤ)).eval x = 8*x^4 - 8*x^2 + 1 := by
  have h4 : Polynomial.Chebyshev.T ℝ (4:ℤ)
      = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (3:ℤ) - Polynomial.Chebyshev.T ℝ (2:ℤ) := by
    have h := Polynomial.Chebyshev.T_add_two (R := ℝ) (n := (2:ℤ))
    simpa only [show (2:ℤ)+2 = 4 from by norm_num, show (2:ℤ)+1 = 3 from by norm_num] using h
  have h3eval : (Polynomial.Chebyshev.T ℝ (3:ℤ)).eval x = 4*x^3 - 3*x := cheb_three x
  simp only [h4, h3eval, Polynomial.Chebyshev.T_two, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
  ring

/-- **HB (9.15).** `(3+10x)²(9+10x)² = 14379 + 24480·T₁(x) + 14900·T₂(x) + 6000·T₃(x)
+ 1250·T₄(x)`, hence the five-term Chebyshev polynomial is non-negative on `[-1,1]`. -/
theorem c95_hP (x : ℝ) (_hx : x ∈ Set.Icc (-1:ℝ) 1) :
    0 ≤ ∑ k ∈ Finset.range 5, c95 k * (Polynomial.Chebyshev.T ℝ (k:ℤ)).eval x := by
  have h3eval : (Polynomial.Chebyshev.T ℝ (3:ℤ)).eval x = 4*x^3 - 3*x := cheb_three x
  have h4eval : (Polynomial.Chebyshev.T ℝ (4:ℤ)).eval x = 8*x^4 - 8*x^2 + 1 := cheb_four x
  have hval : (∑ k ∈ Finset.range 5, c95 k * (Polynomial.Chebyshev.T ℝ (k:ℤ)).eval x)
      = (3 + 10*x)^2 * (9 + 10*x)^2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, zero_add, c95]
    norm_num
    simp only [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one,
      Polynomial.Chebyshev.T_two, h3eval, h4eval, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
    ring
  rw [hval]
  positivity

/-! ## The derivation core (★) -/

/-- **The `h ≥ 5` combination (★), in abstract form.**  Given the five upper bounds for the
`K`-sums of `χ₀, χ₁, χ₁², χ₁³, χ₁⁴` at the points `β, β+iγ, β+2iγ, β+3iγ, β+4iγ`, the
combination `Σ_k c95 k · K(β+ikγ, χ₁ᵏ)` is bounded above by the same combination of the five
bounds.  No positivity of the bounds `Bd k` is needed (the coefficient function `c95` is
non-negative), so this is directly usable with the negative `k = 1` bound produced by
`Ksum_le_single_of_L52_phi`. -/
theorem main95_assembly {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ : ℝ} (hL : 0 < L) (hx₀ : 0 ≤ x₀) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (χ₁ : DirichletCharacter ℂ q) {Bd : ℕ → ℝ}
    (hB : ∀ k ∈ Finset.range 5,
      Ksum q f L ((β : ℂ) + (((k : ℝ) : ℂ) * (γ : ℂ)) * Complex.I) (χ₁ ^ k) ≤ Bd k) :
    0 ≤ ∑ k ∈ Finset.range 5, c95 k * Bd k := by
  have hpos := ksum_trigPoly_nonneg (q := q) (f := f) hf (x₀ := x₀) (L := L) (β := β)
    (γ := γ) hL hx₀ hsupp (d := 4) c95_hP χ₁
  exact le_trans hpos (Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_left (hB k hk) (c95_nonneg k))


/-! ## The numerical reductions

The two cases of the argument reduce to *explicit rational* inequalities in the values
`∫₀^{8/3} e^{±ct}·f(t)dt` of the test function `f = tf72f (3/4)`:

* **Case A** (`L52Hyp` with `s = 1/8`, `λ* = λ₁`, `F(0) = 8/9`, `f(0) = 4/5`): the
  contradiction is `14379·La(0.348) + (4/5)(14379ε + 46630(1/8+ε)) < 24480·(8/9)`, which
  holds as soon as `La(0.348) ≤ 1.19` (true value `1.14571`).
* **Case B** (`s = 1/6`, `λ* = 0.829`, `f(0) = 4/5`): the contradiction is
  `14379·La(0.829) − 24480·La(0.481) + (4/5)(14379ε + 46630(1/6+ε)) < 0`, which holds with
  the bounds `La(0.829) ≤ 1.70`, `La(0.481) ≥ 1.26` (true values `1.6900`, `1.2694`).
* **The `λ₂`-route** (`f = tf72f (17/20)`, `F(0) = 8/9`, `f(0) = 68/75`): from
  `lemma6_2_assembly` one has `F(λ₂-λ₁) ≤ La(λ₁) - 8/9 + (68/75)(1/2+4ε)`, so
  `λ₂ ≥ 0.829` follows once `La(0.348) ≤ 1.1105` and `F(0.481) ≥ 0.6749`
  (true values `1.110194`, `0.6784`).
-/

/-- **Case A arithmetic**: with `La(0.348) ≤ 1.18` the Case A contradiction is strict. -/
theorem caseA_arith {La348 : ℝ} (h : La348 ≤ 118/100) :
    14379 * La348 + (4/5) * (14379 * (1/1000) + 46630 * (1/8 + 1/1000))
      < 24480 * (8/9) := by
  nlinarith [h]

/-- **Case B arithmetic**: with `La(0.82) ≤ 1.706` and `La(0.472) ≥ 1.262` the Case B
contradiction (at `λ* = 0.82`) is strict. -/
theorem caseB_arith {A B : ℝ} (hA : A ≤ 1706/1000) (hB : (1262:ℝ)/1000 ≤ B) :
    14379 * A - 24480 * B + (4/5) * (14379 * (1/1000) + 46630 * (1/6 + 1/1000)) < 0 := by
  nlinarith [hA, hB]

/-- **The `λ₂`-route arithmetic**: with `La(0.348) ≤ 1.1105` the quantity
`La(λ₁) - 8/9 + (68/75)(1/2+4ε)` is at most `0.6786`, hence below the transform value
`F(0.472) ≥ 0.68`; since `F` is decreasing this yields `λ₂ - λ₁ ≥ 0.472`, i.e. `λ₂ ≥ 0.82`
when `λ₁ ≤ 0.348`. -/
theorem lam2_arith {La348 F472 : ℝ} (h1 : La348 ≤ 11105/10000)
    (h2 : (68:ℝ)/100 ≤ F472) :
    La348 - 8/9 + (68/75) * (1/2 + 4 * (1/1000)) ≤ F472 := by
  nlinarith [h1, h2]


/-! ## The numeric interface (what remains to be delegated/proved)

The five integrals below are all elementary (`∫ e^{±ct}·(cubic·quadratic)` over `[0, 8/3]`,
an explicit antiderivative plus a Taylor bound for `exp`), and the `caseA_arith`,
`caseB_arith`, `lam2_arith` reductions above consume exactly them. -/

/-- **The numeric inputs of the `h ≥ 5` argument** (test functions `tf72f (3/4)` for the main
inequality and `tf72f (17/20)` for the `λ₂`-bound).  True values, in order:
`1.14571, 1.70397, 1.26386, 1.11019, 0.68147`. -/
def TfNumericInputs : Prop :=
  (∫ t in (0:ℝ)..(8/3), Real.exp (((348:ℝ)/1000) * t) * tf72f ((3:ℝ)/4) t) ≤ (118:ℝ)/100
  ∧ (∫ t in (0:ℝ)..(8/3), Real.exp (((82:ℝ)/100) * t) * tf72f ((3:ℝ)/4) t) ≤ (1706:ℝ)/1000
  ∧ (1262:ℝ)/1000 ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (((472:ℝ)/1000) * t) * tf72f ((3:ℝ)/4) t
  ∧ (∫ t in (0:ℝ)..(8/3), Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t)
      ≤ (11105:ℝ)/10000
  ∧ (68:ℝ)/100 ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t

/-- The numerical inputs imply the three arithmetic contradictions used by the argument. -/
theorem tf_numeric_consequences (h : TfNumericInputs) :
    (14379 * (∫ t in (0:ℝ)..(8/3), Real.exp (((348:ℝ)/1000) * t) * tf72f ((3:ℝ)/4) t)
        + (4/5) * (14379 * (1/1000) + 46630 * (1/8 + 1/1000)) < 24480 * (8/9))
    ∧ (14379 * (∫ t in (0:ℝ)..(8/3), Real.exp (((82:ℝ)/100) * t) * tf72f ((3:ℝ)/4) t)
        - 24480 * (∫ t in (0:ℝ)..(8/3), Real.exp (((472:ℝ)/1000) * t) * tf72f ((3:ℝ)/4) t)
        + (4/5) * (14379 * (1/1000) + 46630 * (1/6 + 1/1000)) < 0)
    ∧ ((∫ t in (0:ℝ)..(8/3), Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t)
          - 8/9 + (68/75) * (1/2 + 4 * (1/1000))
        ≤ (∫ t in (0:ℝ)..(8/3), Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨caseA_arith h1, caseB_arith h2 h3, lam2_arith h4 h5⟩


/-! ## The minimality/window bridge

The `K`-sum lemmas drop the window zeros of a character, and `Ksum_le_self_of_L52_phi`
requires for that exactly that every window zero `u` has `u.re ≤ s.re`.  With the base point
`s = (1 - λ*/log q) + i·Im s` this is `λ* ≤ λ(u)`, which for a zero of the strip `|Im| ≤ 10`
follows from `IsMin1WideAt 10` together with the hypothesis `λ* ≤ λ₁` (Case A), or from the
second-minimum bound `λ₂ ≥ λ*` (Case B). -/

/-- A zero of `λ` at least `lam` has real part at most `1 - lam/log q`. -/
theorem re_le_one_sub_of_lam_le {q : ℕ} [NeZero q] {ρ : ℂ} {lam : ℝ}
    (hL : 0 < Real.log q) (h : lam ≤ Work.LinnikContract.lamOf q ρ) :
    ρ.re ≤ 1 - lam / Real.log q := by
  rw [Work.LinnikContract.lamOf] at h
  have h1 : lam / Real.log q ≤ 1 - ρ.re := by
    rw [div_le_iff₀ hL]; linarith
  linarith

/-- `IsMin1WideAt 10` gives `λ₁ ≤ λ(u)` for every zero `u` in the strip `|Im| ≤ 10`. -/
theorem lam_le_of_isMin1WideAt {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hm : IsMin1WideAt 10 χ₁ ρ₁) {χ : DirichletCharacter ℂ q} {u : ℂ}
    (hχ : χ ≠ 1) (hu : Work.LinnikContract.zeroMult χ u ≠ 0) (him : |u.im| ≤ 10) :
    Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u := hm.2 χ u hχ hu him

/-- **The window condition for the `K`-sum lemmas.**  If `λ* ≤ λ₁` and `u` is a zero of the
strip `|Im| ≤ 10`, then `u` lies to the left of the point with real part `1 - λ*/log q`. -/
theorem re_le_window_of_min {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hm : IsMin1WideAt 10 χ₁ ρ₁) (hL : 0 < Real.log q) {lam : ℝ}
    (hlam : lam ≤ Work.LinnikContract.lamOf q ρ₁) {χ : DirichletCharacter ℂ q} {u : ℂ}
    (hχ : χ ≠ 1) (hu : Work.LinnikContract.zeroMult χ u ≠ 0) (him : |u.im| ≤ 10) :
    u.re ≤ 1 - lam / Real.log q :=
  re_le_one_sub_of_lam_le hL (le_trans hlam (lam_le_of_isMin1WideAt hm hχ hu him))


/-- **Cancellation of a strictly decreasing transform.**  If `F` is strictly decreasing and
`F x ≤ B ≤ F y`, then `y ≤ x`.  This is the step that turns the `λ₂`-inequality
`F(λ₂-λ₁) ≤ B` (with `B ≤ F(0.472)` from `lam2_arith`) into `λ₂-λ₁ ≥ 0.472`. -/
theorem le_of_F_lt_of_le_F {F : ℝ → ℝ} (hmono : ∀ {a b : ℝ}, a < b → F b < F a) {x y B : ℝ}
    (h1 : F x ≤ B) (h2 : B ≤ F y) : y ≤ x := by
  by_contra h
  push_neg at h
  have h3 : F y < F x := hmono h
  linarith

end

end Work.ZeroFreeTables
