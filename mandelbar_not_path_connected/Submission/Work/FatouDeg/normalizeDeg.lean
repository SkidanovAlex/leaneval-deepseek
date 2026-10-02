import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.MultiPetal.normalizeParabolic
import Submission.Work.FatouDeg.Petal.fatouCoordSec3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg

/-!
# Degenerate normal form of a parabolic polynomial germ

Route (this is a deliberate adaptation of `Work.MultiPetal.normalizeParabolic`, whose conclusion is
`∀ z, F z = c * N_{m,G}(z/c)` with `4 ≤ m` **and** the extra hypothesis `iteratedDeriv 3 F 0 = 0`;
here the fixed point is an arbitrary `z₀` and the third derivative is not assumed to vanish, so
`3 ≤ m` is all one can get):

1. `P̃ := Polynomial.taylor z₀ P - Polynomial.C z₀` where `P` is a polynomial with `F = P.eval`
   (from `hF`).  Its evaluation is `P̃.eval w = F (z₀ + w) - z₀`.
2. `P̃.eval 0 = 0` (`hfix`); `P̃.coeff 1 = 1` — `Polynomial.taylor_coeff_one` turns this into
   `P.derivative.eval z₀ = 1`, which is `h1` through `Polynomial.hasDerivAt`;
   `P̃.coeff 2 = 0` — `Polynomial.taylor_coeff` (n = 2) turns this into
   `(Polynomial.hasseDeriv 2 P).eval z₀ = 0`, and `Polynomial.factorial_smul_hasseDeriv` (k = 2)
   gives `2 * (hasseDeriv 2 P) = P.derivative.derivative`, whose evaluation at `z₀` is
   `iteratedDeriv 2 F z₀ = 0` by `h2` (`iteratedDeriv 2 P.eval = deriv (P.derivative.eval)`, as in
   `normalizeParabolic`'s `key2`).  So `2 * P̃.coeff 2 = 0`, hence `P̃.coeff 2 = 0` (char 0).
3. `2 ≤ P̃.natDegree` from `Polynomial.natDegree_taylor` + `Polynomial.natDegree_sub_C` + `hF`.
4. Run `Work.MultiPetal.normalizeParabolic`'s argument on the coefficient data
   `coeff 0 = 0`, `coeff 1 = 1`, `coeff 2 = 0`, `natDegree ≥ 2` WITHOUT the third derivative:
   `S := P̃ - X ≠ 0` (else `P̃ = X`, so `F` is the identity on a translation, contradicting
   `natDegree ≥ 2`), `S.coeff d = 0` for `d < 3`, so `m := S.natTrailingDegree ≥ 3`, and then the
   scaling block is verbatim (`hm4` becomes `hm3`; `le_natTrailingDegree` supplies `3 ≤ m`).
5. `P̃.eval w = c * N_{m,G}(w/c)` gives `F (z₀ + c * u) = z₀ + c * N_{m,G} u` by substituting
   `w = c * u`.
-/

open Polynomial

/-- **Degenerate normal form at a parabolic fixed point.**  A polynomial map `F` of degree `≥ 2`
with `F z₀ = z₀`, `deriv F z₀ = 1` and vanishing second derivative at `z₀` is, in the chart
`z = z₀ + c w`, of the normal form `w ↦ w - w^m + w^(m+1) G(w)` for some exponent `m ≥ 3`,
some `c ≠ 0` and some polynomial `G`.  No hypothesis on the third derivative is needed. -/
theorem normalizeDeg (F : ℂ → ℂ) (z₀ : ℂ)
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F)
    (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ = 0) :
    ∃ (m : ℕ) (c : ℂ) (G : Polynomial ℂ), 3 ≤ m ∧ c ≠ 0 ∧
      ∀ w : ℂ, F (z₀ + c * w) = z₀ + c * (Polynomial.X - Polynomial.X ^ m
        + Polynomial.X ^ (m + 1) * G).eval w := by
  obtain ⟨P, hPdeg, hFP⟩ := hF
  have hF_eq : F = fun z => P.eval z := funext hFP
  -- The derivative of `P.eval` is `P.derivative.eval`, and similarly one order higher.
  have hder : deriv (fun z => P.eval z) = fun z => P.derivative.eval z := by
    funext z; exact (Polynomial.hasDerivAt P z).deriv
  have hder2 : deriv (fun z => P.derivative.eval z) = fun z => P.derivative.derivative.eval z := by
    funext z; exact (Polynomial.hasDerivAt P.derivative z).deriv
  -- The translation of `P` to the fixed point `z₀`, with its constant term removed.
  set Pt : Polynomial ℂ := Polynomial.taylor z₀ P - Polynomial.C z₀ with hPt
  have hPtEval : ∀ w : ℂ, Pt.eval w = F (z₀ + w) - z₀ := by
    intro w
    rw [hPt]
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.taylor_eval]
    rw [add_comm w z₀, ← hFP]
  -- The three low-order coefficients of `Pt`.
  have hc0 : Pt.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hPtEval]
    simp [hfix]
  have hc1 : Pt.coeff 1 = 1 := by
    rw [hPt, Polynomial.coeff_sub, Polynomial.taylor_coeff_one, Polynomial.coeff_C,
      ite_eq_right (show ¬ ((1:ℕ) = 0) by norm_num), sub_zero]
    rw [← (Polynomial.hasDerivAt P z₀).deriv, ← hF_eq]
    exact h1
  have key2 : iteratedDeriv 2 (fun z => P.eval z) = deriv (fun z => P.derivative.eval z) := by
    rw [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hder]
  have hdd : P.derivative.derivative.eval z₀ = 0 := by
    have h2' := h2
    rw [hF_eq] at h2'
    rw [key2] at h2'
    rw [show deriv (fun z => P.derivative.eval z) z₀ = P.derivative.derivative.eval z₀
      from congrFun hder2 z₀] at h2'
    exact h2'
  have hc2 : Pt.coeff 2 = 0 := by
    rw [hPt, Polynomial.coeff_sub, Polynomial.taylor_coeff, Polynomial.coeff_C,
      ite_eq_right (show ¬ ((2:ℕ) = 0) by norm_num), sub_zero]
    -- `2 * (hasseDeriv 2 P).eval z₀ = P.derivative.derivative.eval z₀ = 0`.
    have hh : (2 : ℕ) • Polynomial.hasseDeriv 2 P = P.derivative.derivative :=
      congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) 2) P
    have hh2 : (2 : ℂ) * (Polynomial.hasseDeriv 2 P).eval z₀ = 0 := by
      have ht := congrArg (fun q : Polynomial ℂ => q.eval z₀) hh
      rw [Polynomial.eval_smul] at ht
      rw [hdd] at ht
      simpa using ht
    rcases mul_eq_zero.mp hh2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  -- `Pt` still has degree at least two.
  have hPdeg' : 2 ≤ Pt.natDegree := by
    rw [hPt, Polynomial.natDegree_sub_C, Polynomial.natDegree_taylor]
    exact hPdeg
  -- `S = Pt - X` is the higher-order part of `Pt`.
  set S : Polynomial ℂ := Pt - Polynomial.X with hS
  have hS_ne : S ≠ 0 := by
    intro hzero
    have hPX : Pt = Polynomial.X := by
      have h0 : Pt - Polynomial.X = 0 := by rw [← hS]; exact hzero
      exact sub_eq_zero.mp h0
    have : Pt.natDegree = 1 := by rw [hPX]; simp
    omega
  have hScoeff : ∀ d < 3, S.coeff d = 0 := by
    intro d hd
    interval_cases d
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc0]; norm_num
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc1]; norm_num
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc2]; norm_num
  -- `m` is the order of the lowest non-trivial term, `a` its coefficient.
  set m : ℕ := S.natTrailingDegree with hm
  have hm3 : 3 ≤ m := by
    rw [hm]; exact Polynomial.le_natTrailingDegree hS_ne hScoeff
  have ha_ne : S.coeff m ≠ 0 := by
    rw [hm]; exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hS_ne
  set a : ℂ := S.coeff m with ha
  have ha0 : a ≠ 0 := by rw [ha]; exact ha_ne
  have ha_P : Pt.coeff m = a := by
    rw [ha]
    have hthis : S.coeff m = Pt.coeff m := by
      rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X,
        ite_eq_right (by omega : ¬ (1 = m)), sub_zero]
    rw [hthis]
  have hsmall : ∀ d < m, Pt.coeff d = (if 1 = d then 1 else 0) := by
    intro d hd
    have h0 : S.coeff d = 0 := by
      rw [hm] at hd
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
    rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X] at h0
    exact sub_eq_zero.mp h0
  -- Scale factor `c` making the `m`-th coefficient of the rescaled polynomial equal to `-1`.
  obtain ⟨c, hc_pow⟩ : ∃ c : ℂ, c ^ (m - 1) = -1 / a :=
    IsAlgClosed.exists_pow_nat_eq (-1/a) (by omega : 0 < m - 1)
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_pow (by omega : m - 1 ≠ 0)] at hc_pow
    exact (div_ne_zero (by norm_num) ha0) hc_pow.symm
  have hca : a * c^(m-1) = -1 := by
    rw [hc_pow]; field_simp
  -- The rescaled polynomial minus its normal form is divisible by `X ^ (m+1)`.
  have hdiv : Polynomial.X^(m+1) ∣
      (Polynomial.C c⁻¹ * Pt.comp (Polynomial.C c * Polynomial.X) - Polynomial.X
        + Polynomial.X^m) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X, Polynomial.coeff_X_pow]
    by_cases hdm : d = m
    · rw [hdm, ite_eq_right (by omega : ¬ (1 = m)), ite_eq_left rfl, ha_P]
      have hcm : c⁻¹ * c^m = c^(m-1) := by
        have h1 : 1 ≤ m := by omega
        have h := pow_sub₀ c hc_ne h1
        rw [pow_one] at h
        rw [h, mul_comm]
      have hmain : c⁻¹ * (a * c^m) = -1 := by
        rw [← mul_assoc, mul_comm c⁻¹ a, mul_assoc, hcm, hca]
      rw [hmain]; ring
    · have hdm' : d < m := by omega
      rw [ite_eq_right (by omega : ¬ (d = m)), hsmall d hdm']
      by_cases hd1 : (1:ℕ) = d
      · rw [ite_eq_left hd1, ← hd1, one_mul, pow_one, inv_mul_cancel₀ hc_ne]
        ring
      · rw [ite_eq_right hd1]
        simp
  obtain ⟨G, hGL⟩ := hdiv
  refine ⟨m, c, G, hm3, hc_ne, ?_⟩
  intro u
  have hkey : Pt.eval (c * u) = c * (u - u^m + u^(m+1) * G.eval u) := by
    have hLeval : (Polynomial.C c⁻¹ * Pt.comp (Polynomial.C c * Polynomial.X) - Polynomial.X + Polynomial.X^m).eval u
        = c⁻¹ * Pt.eval (c * u) - u + u^m := by
      simp [Polynomial.eval_comp]
    have hGeval : (Polynomial.X^(m+1) * G).eval u = u^(m+1) * G.eval u := by simp
    have h1 : c⁻¹ * Pt.eval (c*u) - u + u^m = u^(m+1) * G.eval u := by
      have hh := hLeval
      rw [hGL, hGeval] at hh
      exact hh.symm
    have h2 : c⁻¹ * Pt.eval (c*u) = u^(m+1) * G.eval u + u - u^m := by
      linear_combination h1
    have h3 := congrArg (fun t => c * t) h2
    rw [mul_sub, mul_add, ← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul] at h3
    rw [h3]; ring
  have hin := hPtEval (c * u)
  rw [hkey] at hin
  have hQeval : (Polynomial.X - Polynomial.X^m + Polynomial.X^(m+1)*G).eval u
      = u - u^m + u^(m+1)*G.eval u := by simp
  rw [hQeval, hin]
  ring

end Work.FatouDeg
