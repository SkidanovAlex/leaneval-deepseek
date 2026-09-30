import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series
import Submission.Work.BMF.intval_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

set_option linter.unusedVariables false

open Polynomial Finset

/-- **Iterated derivative of a dilation.**  `(d/dt)^l p(c·t) = c^l · p^{(l)}(c·t)`, as an
identity of polynomials.  (The `l`-fold iterate of `Polynomial.derivative`.) -/
theorem iterate_derivative_comp_C_mul_X (p : ℝ[X]) (c : ℝ) (l : ℕ) :
    (Polynomial.derivative^[l]) (p.comp (C c * X)) =
      C (c ^ l) * ((Polynomial.derivative^[l]) p).comp (C c * X) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Polynomial.derivative_C_mul, Polynomial.derivative_comp, Polynomial.derivative_C_mul_X]
    rw [← mul_assoc, ← C_mul, ← pow_succ]

/-- **Derivative of the binomial basis composed with a dilation.**  With `binP i = C(X,i)`,
`(d/dt)^l (C(b·t, i)) = (i!)⁻¹ b^l · (d/dt)^l (X(X-1)⋯(X-i+1)) (b·t)`. -/
theorem iterate_derivative_binP_comp (i l : ℕ) (b : ℝ) :
    (Polynomial.derivative^[l]) ((Work.BMF.binP i).comp (C b * X))
      = C ((i.factorial : ℝ)⁻¹ * b ^ l) *
          ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).comp (C b * X) := by
  rw [Work.BMF.binP, C_mul_comp, iterate_derivative_C_mul, iterate_derivative_comp_C_mul_X]
  rw [← mul_assoc, ← C_mul]

/-- **Clearing denominators for integer polynomials.**  If `T ∈ ℤ[X]` has degree `≤ N`, then for
every integer `z` and every positive natural `r`, the number `r^N · T(z/r)` is an integer. -/
theorem intPoly_eval_div_cast (T : ℤ[X]) (N : ℕ) (hT : T.natDegree ≤ N) (z : ℤ) (r : ℕ)
    (hr : 0 < r) :
    ∃ m : ℤ, (r : ℝ) ^ N * (T.map (Int.castRingHom ℝ)).eval ((z : ℝ) / (r : ℝ)) = (m : ℝ) := by
  refine ⟨∑ k ∈ Finset.range (T.natDegree + 1), T.coeff k * z ^ k * (r : ℤ) ^ (N - k), ?_⟩
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have key : (T.map (Int.castRingHom ℝ)).eval ((z : ℝ) / (r : ℝ))
      = ∑ i ∈ Finset.range (T.natDegree + 1), (T.coeff i : ℝ) * ((z : ℝ) / (r : ℝ)) ^ i := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    simp
  rw [key, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hiN : i ≤ N := le_trans (Nat.le_of_lt_succ hi) hT
  rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow, Int.cast_natCast]
  rw [div_pow, div_eq_mul_inv, pow_sub₀ (r : ℝ) hr0 hiN]
  ring

/-- **The lattice of derivatives** (MRTTZ Lemma `dte` + the good-quadruple structure).
If `γ` has degree `≤ k` and is integer-valued on the lattice `(q/Q)ℤ`, then its `l`-th derivative
at every integer point lies in `(Q^l/(k! q^k))ℤ`: `γ^{(l)}(n)·k! q^k/Q^l ∈ ℤ`.

Route: apply `Work.BMF.newton_series` to `X ↦ γ((q/Q)·X)` (integer-valued on `ℤ`, degree `≤ k`) to
get `γ(t) = Σ_{i≤k} c_i C(tQ/q, i)` with `c_i ∈ ℤ`.  Then use
`(d/dt)^l (p.comp (C c * X)) = C (c^l) * ((d/dt)^l p).comp (C c * X)` (iterated
`Polynomial.derivative_comp`), write `B_i = Work.BMF.binP i` and note `i! * (d/dt)^l B_i` has
integer coefficients (because `i! * B_i = descPochhammer ℝ i ∈ ℤ[X]` and derivatives preserve
integer coefficients) and degree `≤ i - l`; evaluating the resulting integer combination at
`t = n` produces `k! q^k/Q^l · γ^{(l)}(n) ∈ ℤ` since `p ≤ i - l` makes all exponents of `q`
non-negative and `i! ∣ k!`. -/
theorem lattice_deriv {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {q Q : ℕ} (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    {γ : Polynomial ℝ} (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn ((q : ℝ) / (Q : ℝ)) γ)
    (n : ℤ) :
    ∃ m : ℤ, ((k.factorial : ℝ) * (q : ℝ) ^ k / (Q : ℝ) ^ l) *
      ((Polynomial.derivative^[l]) γ).eval (n : ℝ) = m := by
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hQne : (Q : ℝ) ≠ 0 := by positivity
  set a : ℝ := (q : ℝ) / (Q : ℝ) with ha
  set b : ℝ := (Q : ℝ) / (q : ℝ) with hb
  have hab : a * b = 1 := by rw [ha, hb]; field_simp
  -- The dilated polynomial `φ(t) = γ(aq·t)` is integer-valued on `ℤ` of degree `≤ k`.
  set φ : ℝ[X] := γ.comp (C a * X) with hφ
  have hφint : Work.BMF.IntegralOn 1 φ := by
    intro m
    obtain ⟨j, hj⟩ := hint m
    refine ⟨j, ?_⟩
    show φ.eval (1 * (m : ℝ)) = (j : ℝ)
    rw [one_mul, hφ, Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, ha]
    exact hj
  have hφdeg : φ.natDegree ≤ k := by
    rw [hφ]
    calc (γ.comp (C a * X)).natDegree
        ≤ γ.natDegree * (C a * X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ k * 1 := by
            gcongr
            rw [C_mul_X_eq_monomial]
            exact natDegree_monomial_le a
      _ = k := mul_one k
  obtain ⟨c, hc⟩ := Work.BMF.newton_series k φ hφint hφdeg
  -- `γ` itself is the corresponding combination of dilated binomial polynomials.
  have hcomp : (C a * X).comp (C b * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, hab, C_1, one_mul]
  have hγ : γ = ∑ i ∈ Finset.range (k + 1),
      C ((c i : ℝ)) * (Work.BMF.binP i).comp (C b * X) := by
    have h1 : φ.comp (C b * X) = γ := by
      show (γ.comp (C a * X)).comp (C b * X) = γ
      rw [comp_assoc, hcomp, comp_X]
    rw [← h1, hc]
    simp only [Polynomial.sum_comp, Polynomial.C_mul_comp]
  -- Differentiate `l` times.
  have hderiv : (Polynomial.derivative^[l]) γ
      = ∑ i ∈ Finset.range (k + 1), C ((c i : ℝ)) *
          (C ((i.factorial : ℝ)⁻¹ * b ^ l) *
            ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).comp (C b * X)) := by
    rw [hγ, iterate_derivative_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [iterate_derivative_C_mul, iterate_derivative_binP_comp]
  have hgeval : ((Polynomial.derivative^[l]) γ).eval (n : ℝ)
      = ∑ i ∈ Finset.range (k + 1), (c i : ℝ) * ((i.factorial : ℝ)⁻¹ * b ^ l) *
          ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).eval (b * (n : ℝ)) := by
    rw [hderiv, eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
    ring
  -- `descPochhammer ℝ i` and its derivatives are the images of the integer polynomials.
  have hS : ∀ i, (Polynomial.derivative^[l]) (descPochhammer ℝ i)
      = ((Polynomial.derivative^[l]) (descPochhammer ℤ i)).map (Int.castRingHom ℝ) := by
    intro i
    rw [← descPochhammer_map (Int.castRingHom ℝ) i, iterate_derivative_map]
  have hfac : (q : ℝ) ^ k / (Q : ℝ) ^ l * b ^ l = (q : ℝ) ^ (k - l) := by
    rw [hb, div_pow, pow_sub₀ (q : ℝ) hqne hlk]
    field_simp
  -- Each summand multiplied by `q^(k-l)` is an integer.
  have hMi : ∀ i, i ≤ k → ∃ m : ℤ, (q : ℝ) ^ (k - l) *
      ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).eval (b * (n : ℝ)) = (m : ℝ) := by
    intro i hik
    have hdeg_i : ((Polynomial.derivative^[l]) (descPochhammer ℤ i)).natDegree ≤ k - l := by
      calc ((Polynomial.derivative^[l]) (descPochhammer ℤ i)).natDegree
          ≤ (descPochhammer ℤ i).natDegree - l := Polynomial.natDegree_iterate_derivative _ _
        _ = i - l := by rw [descPochhammer_natDegree]
        _ ≤ k - l := Nat.sub_le_sub_right hik l
    obtain ⟨m, hm⟩ := intPoly_eval_div_cast ((Polynomial.derivative^[l]) (descPochhammer ℤ i))
      (k - l) hdeg_i (n * (Q : ℤ)) q (by omega)
    refine ⟨m, ?_⟩
    have harg : b * (n : ℝ) = ((n * (Q : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
      rw [hb]; push_cast; ring
    rw [hS i, harg]
    exact hm
  classical
  let M : ℕ → ℤ := fun i => if h : i ≤ k then Classical.choose (hMi i h) else 0
  have hM : ∀ i (h : i ≤ k), (q : ℝ) ^ (k - l) *
      ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).eval (b * (n : ℝ)) = (M i : ℝ) := by
    intro i h
    have hMval : M i = Classical.choose (hMi i h) := by
      simp only [M]
      exact dite_eq_left h
    rw [hMval]
    exact Classical.choose_spec (hMi i h)
  refine ⟨∑ i ∈ Finset.range (k + 1), c i * ((k.factorial / i.factorial : ℕ) : ℤ) * M i, ?_⟩
  have hmain : ((k.factorial : ℝ) * (q : ℝ) ^ k / (Q : ℝ) ^ l) *
        ((Polynomial.derivative^[l]) γ).eval (n : ℝ)
      = ∑ i ∈ Finset.range (k + 1), (c i : ℝ) * ((k.factorial / i.factorial : ℕ) : ℝ) *
          ((q : ℝ) ^ (k - l) *
            ((Polynomial.derivative^[l]) (descPochhammer ℝ i)).eval (b * (n : ℝ))) := by
    rw [hgeval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp hi
    have hdiv : ((k.factorial / i.factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) / (i.factorial : ℝ) :=
      Nat.cast_div (Nat.factorial_dvd_factorial hik) (by positivity)
    rw [hdiv, ← hfac]
    ring
  rw [hmain, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  rw [hM i hik, Int.cast_mul, Int.cast_mul, Int.cast_natCast]

end Work.N8
