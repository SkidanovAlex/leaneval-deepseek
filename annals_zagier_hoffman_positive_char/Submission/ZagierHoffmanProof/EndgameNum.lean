import Submission.ZagierHoffmanProof.EndgameA0
import Submission.ZagierHoffmanProof.TwRows
import Submission.ZagierHoffmanProof.HDatum

/-!
# SESSION 360 — the integral numerator `num''` of `Ξ = P·Z/Q` (`PLAN.md` §«SESSION 360» §1.1)

From the two rows of the two-term datum

* **(R)** `Q·σ(Z) = σQ·W^w·(Q·A₁·H_w + Z + Y)`,
* **(A)** `Y·P = A₂·(C(θ^q) - X^q)·Q`   (`P := X^q - X`),

we produce the **rational `σ`-recursion**

  `Ξ := P·Z/Q`,   **`σ Ξ = W^w·(Ξ + N)`**,   `N := P·A₁·H_w - A₂·(X^q - C(θ^q)) ∈ ambA F 0[X]`,

and then the **integral numerator** `num''` with

  **`σ(num'') = W^w·(num'' + N·D'')`**,   `D'' ∈ F_q[X] ∖ {0}`,   `Ξ = num''/D''`,

whose `θ`-integrality `num'' ∈ ambA F 0[X]` follows from
`KuanLin.coeff_mem_ambA_zero_of_kuanLin` (`EndgameIntegral.lean`), and whose `θ`-degree identity
`q·deg_θ(num'') = w·q + deg_θ(num'' + N·D'')` is the input of
`EndgameA0.dvd_pred_of_theta_degree`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. `σ`-fixedness of `X^q - X` and of `A₁, A₂ ∈ F_q[X]` -/

/-- `σ` fixes `P = X^q - X`. -/
lemma polyTwist_one_X_pow_sub_X :
    polyTwist (q := Nat.card F) 1
        (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F))
      = (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) := by
  rw [polyTwist_sub, polyTwist_pow, polyTwist_X]

/-- A polynomial with `ambF F`-coefficients is `σ`-fixed. -/
lemma polyTwist_one_eq_self_of_coeff_mem_ambF {A : Polynomial (Ambient F)}
    (hA : ∀ n, A.coeff n ∈ ambF F) : polyTwist (q := Nat.card F) 1 A = A :=
  polyTwist_one_fixed F A hA

/-! ## §2. The `σ`-recursion for `Ξ = P·Z/Q` -/

/-- ★★★ **The `σ`-recursion for `Ξ = P·Z/Q`.**  Multiplying **(R)** by `P = X^q - X` and
substituting `P·Y = -A₂·(X^q - C(θ^q))·Q` (from **(A)**) gives

  `Q·σ(P·Z) = σQ·W^w·(P·Z + N·Q)`,   `N := P·(A₁·H_w) - A₂·(X^q - C(θ^q))`. -/
theorem sigma_recursion_of_rows {w : ℕ} {A₁ A₂ Q Z Y : Polynomial (Ambient F)}
    (hR : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Q * (A₁ * ambH F w) + Z + Y))
    (hA : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    Q * polyTwist (q := Nat.card F) 1
        ((Polynomial.X ^ Nat.card F - Polynomial.X) * Z)
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * ((Polynomial.X ^ Nat.card F - Polynomial.X) * Z
           + ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
              - A₂ * (Polynomial.X ^ Nat.card F
                  - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q) := by
  rw [polyTwist_mul, polyTwist_one_X_pow_sub_X]
  have hstep : Q * ((Polynomial.X ^ Nat.card F - Polynomial.X) * polyTwist (q := Nat.card F) 1 Z)
      = (Polynomial.X ^ Nat.card F - Polynomial.X)
        * (Q * polyTwist (q := Nat.card F) 1 Z) := by ring
  rw [hstep, hR]
  have hPY : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = -(A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
    rw [hA]; ring
  have hPY' : (Polynomial.X ^ Nat.card F - Polynomial.X) * Y
      = -(A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
    rw [mul_comm]; exact hPY
  have hinner : (Polynomial.X ^ Nat.card F - Polynomial.X) * (Q * (A₁ * ambH F w) + Z + Y)
      = (Polynomial.X ^ Nat.card F - Polynomial.X) * Z
        + ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
           - A₂ * (Polynomial.X ^ Nat.card F
              - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
    rw [mul_add, mul_add, hPY']; ring
  have hre : (Polynomial.X ^ Nat.card F - Polynomial.X)
      * (polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
          * (Q * (A₁ * ambH F w) + Z + Y))
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * ((Polynomial.X ^ Nat.card F - Polynomial.X)
            * (Q * (A₁ * ambH F w) + Z + Y)) := by ring
  rw [hre, hinner]

/-! ## §3. The coprime decomposition and the integral numerator

`PLAN.md` §«SESSION 360» §1.1.  Three generic lemmas (no `Ambient F`) plus the ambient assembly. -/

/-- ★★★ **Coprime decomposition of a fraction of polynomials** (pure algebra): for `q ≠ 0` there are
`a, b` with `b ≠ 0`, `IsCoprime a b` and `p·b = q·a` — i.e. `p/q = a/b` in lowest terms.  The proof
goes through `RatFunc.num`/`denom`, whose coprimality is already in Mathlib
(`RatFunc.isCoprime_num_denom`); this avoids the (catastrophically slow) `EuclideanDomain.gcd` route
on `Polynomial K`. -/
theorem exists_coprime_decomp {K : Type*} [Field K] (p q : Polynomial K) (hq : q ≠ 0) :
    ∃ a b : Polynomial K, b ≠ 0 ∧ IsCoprime a b ∧ p * b = q * a := by
  set a := RatFunc.num (RatFunc.mk p q) with ha
  set b := RatFunc.denom (RatFunc.mk p q) with hb
  have hb0 : b ≠ 0 := RatFunc.denom_ne_zero _
  have hnum : ((a : Polynomial K) : RatFunc K) / ((b : Polynomial K) : RatFunc K)
      = ((p : Polynomial K) : RatFunc K) / ((q : Polynomial K) : RatFunc K) :=
    (RatFunc.num_div_denom _).trans (RatFunc.mk_eq_div p q)
  have hbn : ((b : Polynomial K) : RatFunc K) ≠ 0 := by
    simpa using fun h => hb0 ((IsFractionRing.injective (Polynomial K) (RatFunc K)) h)
  have hqn : ((q : Polynomial K) : RatFunc K) ≠ 0 := by
    simpa using fun h => hq ((IsFractionRing.injective (Polynomial K) (RatFunc K)) h)
  have hcross : ((a : Polynomial K) : RatFunc K) * ((q : Polynomial K) : RatFunc K)
      = ((p : Polynomial K) : RatFunc K) * ((b : Polynomial K) : RatFunc K) :=
    (div_eq_div_iff hbn hqn).mp hnum
  refine ⟨a, b, hb0, ?_, ?_⟩
  · rw [ha, hb]; exact RatFunc.isCoprime_num_denom _
  · refine IsFractionRing.injective (Polynomial K) (RatFunc K) ?_
    push_cast
    exact hcross.symm.trans (mul_comm _ _)

/-- ★★★★ **Generic: the `σ`-fixed denominator and the cleaned numerator.**  If `num/D` is reduced and
`σ(num)·D = Λ^w·(num + N·D)·σD`, then after multiplying both by `(lc D)^{-1}` the denominator is
literally `σ`-fixed and the recursion reads `σ(num) = Λ^w·(num + N·D)`. -/
theorem exists_fixed_den_and_numerator {K : Type*} [Field K] (f : K →+* K)
    (hf : Function.Injective f) {num D Lam N : Polynomial K} {w : ℕ}
    (hD : D ≠ 0) (hnum : num ≠ 0) (hcop : IsCoprime num D)
    (h : num.map f * D = Lam ^ w * (num + N * D) * D.map f) :
    ∃ num' D' : Polynomial K, D' ≠ 0 ∧ D'.map f = D' ∧ num' ≠ 0 ∧
      num'.map f = Lam ^ w * (num' + N * D') := by
  obtain ⟨c, _hc0, hc⟩ := den_map_scalar_of_recursion f hf hD hcop h
  have hu : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have hfu : f D.leadingCoeff ≠ 0 := fun h0 => hu (hf (by rw [h0, map_zero]))
  have hlead : f D.leadingCoeff = c * D.leadingCoeff := by
    have h1 := congrArg Polynomial.leadingCoeff hc
    simpa only [Polynomial.leadingCoeff_map, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C] using h1
  have hkey : f (D.leadingCoeff)⁻¹ * c * D.leadingCoeff = 1 := by
    have h3 : c * D.leadingCoeff = f D.leadingCoeff := hlead.symm
    rw [map_inv₀, mul_assoc, h3, inv_mul_cancel₀ hfu]
  have hval : f (D.leadingCoeff)⁻¹ * c = (D.leadingCoeff)⁻¹ :=
    mul_right_cancel₀ hu (by rw [hkey, inv_mul_cancel₀ hu])
  have hDmul : Polynomial.C D.leadingCoeff * (Polynomial.C (D.leadingCoeff)⁻¹ * D) = D := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hu, Polynomial.C_1, one_mul]
  have hnum_eq : num + N * D
      = Polynomial.C D.leadingCoeff * (Polynomial.C (D.leadingCoeff)⁻¹ * num
          + N * (Polynomial.C (D.leadingCoeff)⁻¹ * D)) := by
    rw [mul_add]
    congr 1
    · rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hu, Polynomial.C_1, one_mul]
    · calc N * D
          = N * (Polynomial.C D.leadingCoeff * (Polynomial.C (D.leadingCoeff)⁻¹ * D)) := by
            rw [hDmul]
        _ = Polynomial.C D.leadingCoeff * (N * (Polynomial.C (D.leadingCoeff)⁻¹ * D)) := by
            ring
  have hsig : num.map f = Polynomial.C c * Lam ^ w * (num + N * D) := by
    have h4 : num.map f * D = (Polynomial.C c * Lam ^ w * (num + N * D)) * D := by
      rw [h, hc]; ring
    exact mul_right_cancel₀ hD h4
  have hCmul : Polynomial.C (f (D.leadingCoeff)⁻¹) * Polynomial.C c * Polynomial.C D.leadingCoeff
      = Polynomial.C (f (D.leadingCoeff)⁻¹ * c * D.leadingCoeff) := by
    rw [Polynomial.C_mul, Polynomial.C_mul]
  refine ⟨Polynomial.C (D.leadingCoeff)⁻¹ * num, Polynomial.C (D.leadingCoeff)⁻¹ * D,
    mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hu)) hD, ?_, ?_, ?_⟩
  · rw [Polynomial.map_mul, Polynomial.map_C, hc, ← mul_assoc, ← Polynomial.C_mul, hval]
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hu)) hnum
  · rw [Polynomial.map_mul, Polynomial.map_C, hsig, hnum_eq]
    rw [show Polynomial.C (f (D.leadingCoeff)⁻¹) * (Polynomial.C c * Lam ^ w
          * (Polynomial.C D.leadingCoeff * (Polynomial.C (D.leadingCoeff)⁻¹ * num
              + N * (Polynomial.C (D.leadingCoeff)⁻¹ * D))))
        = (Polynomial.C (f (D.leadingCoeff)⁻¹) * Polynomial.C c * Polynomial.C D.leadingCoeff)
          * (Lam ^ w * (Polynomial.C (D.leadingCoeff)⁻¹ * num
              + N * (Polynomial.C (D.leadingCoeff)⁻¹ * D))) from by ring, hCmul, hkey,
      Polynomial.C_1, one_mul]

/-- ★★★ **Generic: the coprime `num/D` recursion.**  From `Q·σ(P·Z) = σQ·Λ^w·(P·Z + N·Q)` with
`Q ≠ 0`, `P·Z ≠ 0` one produces `num, D` with `IsCoprime num D`, `num ≠ 0`, `D ≠ 0` and
`σ(num)·D = Λ^w·(num + N·D)·σ(D)`. -/
theorem gcd_recursion {K : Type*} [Field K] (f : K →+* K) (hf : Function.Injective f)
    {P Z Q N Lam : Polynomial K} {w : ℕ} (hQ : Q ≠ 0) (hPZ : P * Z ≠ 0)
    (hrow : Q * (P * Z).map f = Q.map f * Lam ^ w * (P * Z + N * Q)) :
    ∃ num D : Polynomial K, D ≠ 0 ∧ num ≠ 0 ∧ IsCoprime num D ∧
      num.map f * D = Lam ^ w * (num + N * D) * D.map f := by
  classical
  obtain ⟨a, b, hb0, hcop, hcross⟩ := exists_coprime_decomp Q (P * Z) hPZ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcross
    rcases mul_eq_zero.mp hcross with h | h
    · exact hQ h
    · exact hb0 h
  have hnum0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcross
    rcases mul_eq_zero.mp hcross.symm with h | h
    · exact hPZ h
    · exact ha0 h
  have hσQ : Q.map f ≠ 0 := fun h0 => hQ ((Polynomial.map_eq_zero_iff hf).mp h0)
  have h1 : Q.map f * b.map f = (P * Z).map f * a.map f := by
    have h := congrArg (Polynomial.map f) hcross
    rwa [Polynomial.map_mul, Polynomial.map_mul] at h
  have h2 : b.map f * Q.map f * Q = Q.map f * (Lam ^ w * (P * Z + N * Q)) * a.map f := by
    have haa : b.map f * Q.map f = (P * Z).map f * a.map f := by
      rw [mul_comm (b.map f) (Polynomial.map f Q), h1]
    rw [haa, show (P * Z).map f * a.map f * Q = (Q * (P * Z).map f) * a.map f from by ring, hrow]
    ring
  have h3 : b.map f * Q = Lam ^ w * (P * Z + N * Q) * a.map f := by
    have h2' : b.map f * Q * Q.map f = (Lam ^ w * (P * Z + N * Q) * a.map f) * Q.map f := by
      rw [show b.map f * Q * Q.map f = b.map f * Q.map f * Q from by ring, h2]
      ring
    exact mul_right_cancel₀ hσQ h2'
  have h4 : b.map f * a * Q = (Lam ^ w * (b + N * a) * a.map f) * Q := by
    rw [show b.map f * a * Q = (b.map f * Q) * a from by ring, h3]
    rw [show Lam ^ w * (P * Z + N * Q) * a.map f * a
        = Lam ^ w * ((P * Z) * a + N * Q * a) * a.map f from by ring, ← hcross]
    ring
  exact ⟨b, a, ha0, hnum0, hcop.symm, mul_right_cancel₀ hQ h4⟩

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★★ **The integral numerator of `Ξ = P·Z/Q`** (`PLAN.md` §«SESSION 360» §1.1):

  `σ(num) = W^w·(num + N·D)`,   `D ∈ F_q[X] ∖ {0}`,   `num ≠ 0`. -/
theorem exists_integral_recursion {P Z Q N : Polynomial (Ambient F)} {w : ℕ}
    (hQ : Q ≠ 0) (hPZ : P * Z ≠ 0)
    (hrow : Q * polyTwist (q := Nat.card F) 1 (P * Z)
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (P * Z + N * Q)) :
    ∃ num D : Polynomial (Ambient F), D ≠ 0 ∧ (∀ n, D.coeff n ∈ ambF F) ∧ num ≠ 0 ∧
      polyTwist (q := Nat.card F) 1 num
        = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D) := by
  obtain ⟨num, D, hD0, hnum0, hcop, hrec⟩ :=
    gcd_recursion (f := frobPowHom (q := Nat.card F) 1) (frobPowHom_injective (F := F) 1)
      (Lam := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) hQ hPZ hrow
  obtain ⟨num', D', hD'0, hD'fix, hnum'0, hrec'⟩ :=
    exists_fixed_den_and_numerator (f := frobPowHom (q := Nat.card F) 1)
      (frobPowHom_injective (F := F) 1) hD0 hnum0 hcop hrec
  exact ⟨num', D', hD'0, (polyTwist_one_eq_self_iff (F := F) D').mp hD'fix, hnum'0, hrec'⟩

end ZagierHoffmanPositiveChar
