import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial

namespace Work.MultiPetal

/-- Normalization of a parabolic polynomial fixed point: a polynomial `F` over `ℂ` of degree
at least `2` with `F 0 = 0`, `F' 0 = 1` and vanishing second and third derivatives at `0`
can be put in the normal form `z ↦ c · (w - w^m + w^{m+1} G(w))` with `w = z / c`, `m ≥ 4`
and `c ≠ 0`. -/
theorem normalizeParabolic (F : ℂ → ℂ)
    (hF : ∃ P : Polynomial ℂ, 2 ≤ P.natDegree ∧ ∀ z : ℂ, F z = P.eval z)
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1)
    (h2 : iteratedDeriv 2 F 0 = 0) (h3 : iteratedDeriv 3 F 0 = 0) :
    ∃ (m : ℕ) (c : ℂ) (G : Polynomial ℂ),
      4 ≤ m ∧ c ≠ 0 ∧
      ∀ z : ℂ, F z = c * (Polynomial.X - Polynomial.X ^ m
        + Polynomial.X ^ (m + 1) * G).eval (z / c) := by
  obtain ⟨P, hPdeg, hFP⟩ := hF
  have hF_eq : F = fun z => P.eval z := funext hFP
  -- relation between iterated derivatives of `F` and iterated formal derivatives of `P`
  have hder : deriv (fun z => P.eval z) = fun z => P.derivative.eval z := by
    funext z; exact (Polynomial.hasDerivAt P z).deriv
  have hder2 : deriv (fun z => P.derivative.eval z) = fun z => P.derivative.derivative.eval z := by
    funext z; exact (Polynomial.hasDerivAt P.derivative z).deriv
  have hder3 : deriv (fun z => P.derivative.derivative.eval z) =
      fun z => P.derivative.derivative.derivative.eval z := by
    funext z; exact (Polynomial.hasDerivAt P.derivative.derivative z).deriv
  -- low order coefficients of `P`
  have hc0 : P.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [hF_eq] using h0
  have hc1 : P.coeff 1 = 1 := by
    have h := h1
    rw [hF_eq, hder] at h
    change P.derivative.eval 0 = 1 at h
    rw [← Polynomial.coeff_zero_eq_eval_zero P.derivative] at h
    rw [Polynomial.coeff_derivative] at h
    simpa using h
  have key2 : iteratedDeriv 2 (fun z => P.eval z) = deriv (fun z => P.derivative.eval z) := by
    rw [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hder]
  have key3 : iteratedDeriv 3 (fun z => P.eval z) =
      deriv (fun z => P.derivative.derivative.eval z) := by
    rw [show (3:ℕ) = 2+1 from rfl, iteratedDeriv_succ, key2, hder2]
  have hc2 : P.coeff 2 = 0 := by
    have h := h2
    rw [hF_eq, key2, hder2] at h
    change P.derivative.derivative.eval 0 = 0 at h
    rw [← Polynomial.coeff_zero_eq_eval_zero (P.derivative.derivative)] at h
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative] at h
    norm_num at h
    exact h
  have hc3 : P.coeff 3 = 0 := by
    have h := h3
    rw [hF_eq, key3, hder3] at h
    change P.derivative.derivative.derivative.eval 0 = 0 at h
    rw [← Polynomial.coeff_zero_eq_eval_zero (P.derivative.derivative.derivative)] at h
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_derivative] at h
    norm_num at h
    exact h
  have hPne : P ≠ 0 := by
    intro h; rw [h] at hPdeg; simp at hPdeg
  -- `P` has degree at least `4`
  have hPdeg4 : 4 ≤ P.natDegree := by
    by_contra hcon
    rw [not_le] at hcon
    have hcoeff : P.coeff P.natDegree = 0 := by
      rcases (by omega : P.natDegree = 2 ∨ P.natDegree = 3) with h | h
      · rw [h]; exact hc2
      · rw [h]; exact hc3
    have hne : P.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    exact hne hcoeff
  -- `S = P - X` is the "higher order part" of `P`
  set S : Polynomial ℂ := P - Polynomial.X with hS
  have hS_ne : S ≠ 0 := by
    intro hzero
    have hthis : S.coeff P.natDegree = 0 := by rw [hzero]; simp
    rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X] at hthis
    rw [ite_eq_right (by omega : ¬ (1 = P.natDegree))] at hthis
    have hne : P.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    exact hne (sub_eq_zero.mp hthis)
  have hScoeff : ∀ d < 4, S.coeff d = 0 := by
    intro d hd
    interval_cases d
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc0]; norm_num
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc1]; norm_num
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc2]; norm_num
    · rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, hc3]; norm_num
  -- `m` is the order of the lowest non-trivial term, `a` its coefficient
  set m : ℕ := S.natTrailingDegree with hm
  have hm4 : 4 ≤ m := by
    rw [hm]; exact Polynomial.le_natTrailingDegree hS_ne hScoeff
  have ha_ne : S.coeff m ≠ 0 := by
    rw [hm]; exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hS_ne
  set a : ℂ := S.coeff m with ha
  have ha0 : a ≠ 0 := by rw [ha]; exact ha_ne
  have ha_P : P.coeff m = a := by
    rw [ha]
    rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X, ite_eq_right (by omega : ¬ (1 = m))]
    ring
  have hsmall : ∀ d < m, P.coeff d = (if 1 = d then 1 else 0) := by
    intro d hd
    have h1 : S.coeff d = 0 := by
      rw [hm] at hd
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
    rw [hS, Polynomial.coeff_sub, Polynomial.coeff_X] at h1
    exact sub_eq_zero.mp h1
  -- scale factor `c` making the `m`-th coefficient equal to `-1`
  obtain ⟨c, hc_pow⟩ : ∃ c : ℂ, c ^ (m - 1) = -1 / a :=
    IsAlgClosed.exists_pow_nat_eq (-1/a) (by omega : 0 < m - 1)
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_pow (by omega : m - 1 ≠ 0)] at hc_pow
    exact (div_ne_zero (by norm_num) ha0) hc_pow.symm
  have hca : a * c^(m-1) = -1 := by
    rw [hc_pow]; field_simp
  -- the rescaled polynomial minus its normal form is divisible by `X ^ (m+1)`
  have hdiv : Polynomial.X^(m+1) ∣
      (Polynomial.C c⁻¹ * P.comp (Polynomial.C c * Polynomial.X) - Polynomial.X
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
  refine ⟨m, c, G, hm4, hc_ne, ?_⟩
  intro z
  set w : ℂ := z / c with hw
  have hwz : c * w = z := by rw [hw]; field_simp
  have hLeval : (C c⁻¹ * P.comp (C c * X) - X + X^m).eval w
      = c⁻¹ * P.eval (c * w) - w + w^m := by
    simp [Polynomial.eval_comp]
  have hGeval : (X^(m+1) * G).eval w = w^(m+1) * G.eval w := by simp
  have h1 : c⁻¹ * P.eval (c*w) - w + w^m = w^(m+1) * G.eval w := by
    have hh := hLeval
    rw [hGL, hGeval] at hh
    exact hh.symm
  have hkey : P.eval (c*w) = c * (w - w^m + w^(m+1) * G.eval w) := by
    have h2 : c⁻¹ * P.eval (c*w) = w^(m+1) * G.eval w + w - w^m := by
      linear_combination h1
    have h3 := congrArg (fun t => c * t) h2
    rw [mul_sub, mul_add, ← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul] at h3
    rw [h3]; ring
  have hQeval : (X - X^m + X^(m+1)*G).eval w = w - w^m + w^(m+1)*G.eval w := by simp
  rw [hFP z, ← hwz, hkey, hQeval]

end Work.MultiPetal
