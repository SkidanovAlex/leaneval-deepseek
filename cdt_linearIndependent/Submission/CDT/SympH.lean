import Mathlib

/-!
# The symmetrization of `H(x)` (CDT §"The symmetrization of H(x)")

In the proof of Theorem `mainA` of Calegari–Dimitrov–Tang (arXiv:2408.15403),
after Proposition `functionsH` produces the holonomic `G`-function `H(x)`
from a hypothetical rational relation among `1, ζ(2), L(2,χ₋₃)`,
§"The symmetrization of H(x)" replaces it by the **symmetrized** function

```lean
G(y) = Sym⁺H(x) := H(x) + H(x/(x−1))    (a power series in  y)
```

in the symmetrization coordinate `y = x²/(x−1) = x + x/(x−1)`.  The map
`x ↦ φ(x) = x/(x−1)` is an *order-two Möbius involution*; `x` and `φ(x)`
are the two roots of the quadratic `T² − y·T + y = 0`, and the difference
`w := x − φ(x)` satisfies `w² = y² − 4y`.

This module formalises the *algebraic core* of that section — the formal
power-series identities that any later statement (the descent of
`φ`-invariant series to `ℚ[[y]]`, the `ℤ`-integrality and the order-4 ODE
of `G_A(y) = Sym⁺H_A`, the denominator-type lemma `Gdenominatortype`)
sits on:

* `sympPhi = X·(X−1)⁻¹` (the involution), `sympY = X·sympPhi`, `sympW`;
* `sympPhi_mul_sub_one` : `φ·(X−1) = X`;
* `symp_x_add_phi`/`symp_x_mul_phi` : `X + φ = y`, `X·φ = y` (so `y` is
  simultaneously the sum and the product of the two roots `X`, `φ`);
* the unit facts `symp_phi_minus_one_mul_sub_one` : `(φ−1)·(X−1) = 1`
  (and its commuted form);
* the quadratic `symp_quadratic` : `X² − y·X + y = 0` and
  `symp_w_sq` : `w² = y² − 4y`;
* **`symp_phi_involutive`** : `φ∘φ = X` and **`symp_y_invariant`** :
  `y∘φ = y` (substitution of formal power series);
* **`symp_symm_invariant`** : for any `H`, the symmetrized combination
  `H + H∘φ` is invariant under `x ↦ φ(x)`.

The descent of `φ`-invariant series to `ℚ[[y]]` — which defines
`Sym⁺H` — is **DONE** in `Submission.CDT.SympDescent` (module
`SympDescent`): there `symp_descent` proves that every `φ`-invariant
series is a unique power series in `y`, and `sympSym H` (= `Sym⁺H`) is the
unique series with `(Sym⁺H)∘y = H + H∘φ` (`sympSym_subst`).

**DONE in `SympDescent`/`SympZagier`**: the `ℤ`-coefficient refinement of
the descent (`IntSeries`, `sympDescCoeff_int`, `sympSym_int`, giving
`G_A(y) = Sym⁺H_A ∈ ℤ[[y]]` — `sympSym_HA_IntSeries`), the descent's
coefficient recursion (`sympDescCoeff`, `sympDescCoeff_eq_sign`) and the
verification of the paper's defG display
`G_A(y) = 2 − 27y + 1014y² − 49536y³ + …` (`sympSym_HA_coeff_zero/one/
two/three`, module `Submission.CDT.SympZagier`).

**The order-4 ODE of `G_A(y) = Sym⁺H_A` (paper eq. (explicitode))** is
targeted in module `Submission.CDT.SympExplicitode`: the multipliers
`c₀..c₄` (expanded from the paper's factored display), the operator
`GA_odeLHS = Σᵢ cᵢ·G_A^(i)`, and the **first coefficient block**
(`GA_odeLHS_coeff_zero/one/two`: the coefficient equations of degrees
`0,1,2` vanish, using the verified `g₀..g₃`); the full identity
`GA_odeLHS = 0` needs the whole descent sequence (creative telescoping or
the `x ↦ y` push-forward of `HA_ode`) — next layer.  Still ahead also:
the denominator-type lemma `Gdenominatortype`.  (The `P_n(y) = xⁿ + φⁿ`
polynomials `P_n = y·P_{n−1} − y·P_{n−2}`, paper eq. (polysym), are DONE
in `SympDescent`: `sympP`, `sympP_succ_succ`, `sympP_invariant`.)

All declarations are fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

open PowerSeries

/-- `φ = X/(X−1)`: the power series of the Möbius map `x ↦ x/(x−1)`
(an order-two involution of the punctured line, `φ = −X−X²−…`) -/
def sympPhi : PowerSeries ℚ := X * ((X : PowerSeries ℚ) - 1)⁻¹

/-- the symmetrization coordinate `y = x²/(x−1) = x·φ(x)` -/
def sympY : PowerSeries ℚ := X * sympPhi

/-- the difference `w = x − φ(x)`, whose square is a series in `y` -/
def sympW : PowerSeries ℚ := X - sympPhi

/-- `sympPhi` may be substituted into power series (zero constant term) -/
lemma sympPhi_hasSubst : PowerSeries.HasSubst sympPhi := by
  unfold sympPhi
  rw [← pow_one X]
  exact PowerSeries.HasSubst.mul_left (PowerSeries.HasSubst.X_pow (n := 1) (by norm_num))

/-- `sympY` may be substituted into power series (zero constant term) -/
lemma sympY_hasSubst : PowerSeries.HasSubst sympY := by
  unfold sympY
  rw [← pow_one X]
  exact PowerSeries.HasSubst.mul_left (PowerSeries.HasSubst.X_pow (n := 1) (by norm_num))

/-- the constant term of `X−1` is nonzero (it is invertible as a series) -/
lemma symp_sub_one_constant_ne : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) ≠ 0 := by
  have h : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) = -1 := by
    rw [map_sub]
    rw [PowerSeries.constantCoeff_X]
    norm_num
  rw [h]
  norm_num

/-- `φ·(X−1) = X` -/
lemma sympPhi_mul_sub_one : sympPhi * ((X : PowerSeries ℚ) - 1) = X := by
  unfold sympPhi
  rw [mul_assoc]
  rw [PowerSeries.inv_mul_cancel ((X : PowerSeries ℚ) - 1) symp_sub_one_constant_ne]
  rw [mul_one]

/-- `(X−1)·φ = X` -/
lemma symp_sub_one_mul_phi : ((X : PowerSeries ℚ) - 1) * sympPhi = X := by
  calc
    ((X : PowerSeries ℚ) - 1) * sympPhi = sympPhi * ((X : PowerSeries ℚ) - 1) := by ring
    _ = X := sympPhi_mul_sub_one

/-- `X·φ = y` (definitional) -/
lemma symp_x_mul_phi : X * sympPhi = sympY := rfl

/-- `X + φ = y` (the symmetrization coordinate) -/
lemma symp_x_add_phi : X + sympPhi = sympY := by
  have hcc : ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ = 1 := by
    rw [PowerSeries.mul_inv_cancel ((X : PowerSeries ℚ) - 1) symp_sub_one_constant_ne]
  have h : (X + sympPhi) * ((X : PowerSeries ℚ) - 1) = sympY * ((X : PowerSeries ℚ) - 1) := by
    calc
      (X + sympPhi) * ((X : PowerSeries ℚ) - 1) = X * ((X : PowerSeries ℚ) - 1) + sympPhi * ((X : PowerSeries ℚ) - 1) := by ring
      _ = X * ((X : PowerSeries ℚ) - 1) + X := by rw [sympPhi_mul_sub_one]
      _ = X * X := by ring
      _ = sympY * ((X : PowerSeries ℚ) - 1) := by
            unfold sympY
            rw [mul_assoc]
            rw [sympPhi_mul_sub_one]
  have hc : (X + sympPhi) * (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹) =
      sympY * (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹) := by
    calc
      (X + sympPhi) * (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹)
          = ((X + sympPhi) * ((X : PowerSeries ℚ) - 1)) * ((X : PowerSeries ℚ) - 1)⁻¹ := by ring
      _ = (sympY * ((X : PowerSeries ℚ) - 1)) * ((X : PowerSeries ℚ) - 1)⁻¹ := by rw [h]
      _ = sympY * (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹) := by ring
  rw [hcc] at hc
  simpa using hc

/-- `(φ−1)·(X−1) = 1` — `φ − 1` inverts `X − 1` -/
lemma symp_phi_minus_one_mul_sub_one :
    (sympPhi - 1) * ((X : PowerSeries ℚ) - 1) = 1 := by
  calc
    (sympPhi - 1) * ((X : PowerSeries ℚ) - 1)
        = sympPhi * ((X : PowerSeries ℚ) - 1) - 1 * ((X : PowerSeries ℚ) - 1) := by ring
    _ = X - ((X : PowerSeries ℚ) - 1) := by rw [sympPhi_mul_sub_one, one_mul]
    _ = 1 := by ring

/-- `(X−1)·(φ−1) = 1` (commuted form) -/
lemma symp_sub_one_mul_phi_minus_one :
    ((X : PowerSeries ℚ) - 1) * (sympPhi - 1) = 1 := by
  rw [mul_comm]
  exact symp_phi_minus_one_mul_sub_one

/-- the quadratic relation: `X² − y·X + y = 0` (the two roots of
`T² − y·T + y` are `X` and `φ(X)`) -/
lemma symp_quadratic : X ^ 2 - sympY * X + sympY = 0 := by
  -- substitute y = X + φ:
  rw [← symp_x_add_phi]
  have h_sub : sympPhi * X - sympPhi = X := by
    have h := sympPhi_mul_sub_one
    -- φ·(X−1) = φX − φ:
    rw [mul_sub, mul_one] at h
    exact h
  have hφ' : sympPhi * X - sympPhi - X = 0 := by
    calc
      sympPhi * X - sympPhi - X = X - X := by rw [h_sub]
      _ = 0 := by ring
  calc
    X ^ 2 - (X + sympPhi) * X + (X + sympPhi) = -(sympPhi * X - sympPhi - X) := by ring
    _ = 0 := by rw [hφ']; norm_num

/-- `w² = y² − 4y` where `w = X − φ` -/
lemma symp_w_sq : sympW ^ 2 = sympY ^ 2 - 4 * sympY := by
  have h : (X - sympPhi) ^ 2 = (X + sympPhi) ^ 2 - 4 * (X * sympPhi) := by ring
  rw [symp_x_add_phi] at h
  rw [symp_x_mul_phi] at h
  simpa [sympW] using h

/-- `φ∘φ = X` (the involution is of order two) -/
lemma symp_phi_involutive : sympPhi.subst sympPhi = X := by
  have hφ : PowerSeries.HasSubst sympPhi := sympPhi_hasSubst
  -- U := φ∘φ.  From the identity (X−1)·φ = X, substitute φ:
  have hU : (sympPhi - 1) * (sympPhi.subst sympPhi) = sympPhi := by
    have h := symp_sub_one_mul_phi   -- (X−1)·φ = X
    have hs := congrArg (fun z : PowerSeries ℚ => z.subst sympPhi) h
    rw [PowerSeries.subst_mul hφ] at hs
    rw [PowerSeries.subst_sub hφ] at hs
    rw [PowerSeries.subst_X hφ] at hs
    have h1 : ((1 : PowerSeries ℚ).subst sympPhi) = 1 := by
      rw [← PowerSeries.coe_substAlgHom hφ]
      simp
    rw [h1] at hs
    simpa [mul_sub, sub_eq_add_neg] using hs
  -- multiply on the left by (X−1): (X−1)·(φ−1)·U = (X−1)·φ = X; and (X−1)·(φ−1) = 1:
  have hL : ((X : PowerSeries ℚ) - 1) * ((sympPhi - 1) * (sympPhi.subst sympPhi)) =
      ((X : PowerSeries ℚ) - 1) * sympPhi := by
    rw [hU]
  rw [← mul_assoc] at hL
  rw [symp_sub_one_mul_phi_minus_one] at hL
  have hR : ((X : PowerSeries ℚ) - 1) * sympPhi = X := symp_sub_one_mul_phi
  rw [hR] at hL
  simpa using hL

/-- `y∘φ = y` (the symmetrization coordinate is invariant under the
involution) -/
lemma symp_y_invariant : sympY.subst sympPhi = sympY := by
  have hφ : PowerSeries.HasSubst sympPhi := sympPhi_hasSubst
  calc
    sympY.subst sympPhi = (X * sympPhi).subst sympPhi := by rw [symp_x_mul_phi]
    _ = X.subst sympPhi * sympPhi.subst sympPhi := by rw [PowerSeries.subst_mul hφ]
    _ = sympPhi * X := by rw [PowerSeries.subst_X hφ, symp_phi_involutive]
    _ = X * sympPhi := by ring
    _ = sympY := by rw [symp_x_mul_phi]

/-- for any series `H`, the symmetrized combination `H + H∘φ` is invariant
under substituting `φ` for `X` -/
lemma symp_symm_invariant (H : PowerSeries ℚ) :
    (H + H.subst sympPhi).subst sympPhi = H + H.subst sympPhi := by
  have hφ : PowerSeries.HasSubst sympPhi := sympPhi_hasSubst
  calc
    (H + H.subst sympPhi).subst sympPhi
        = subst sympPhi H + subst sympPhi (H.subst sympPhi) := by
          rw [PowerSeries.subst_add hφ]
    _ = subst sympPhi H + H := by
          congr 1
          have hc := PowerSeries.subst_comp_subst_apply (R := ℚ) hφ hφ H
          -- hc : subst φ (subst φ H) = subst (subst φ φ) H:
          rw [hc]
          rw [symp_phi_involutive]
          exact PowerSeries.X_subst H
    _ = H + H.subst sympPhi := by rw [add_comm]
