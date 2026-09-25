import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.Analysis.Nonarchimedean.val_pow_sub_one_le_exp_neg

namespace NK.UchidaKummer.Approximation

open scoped WithZero

/-! ## Valuation bookkeeping on `ℤᵐ⁰`

Two elementary facts used repeatedly below: `exp (-n) < 1` for `n ≥ 1`, and the
"unit criterion" `v x = 1` whenever `v (x - 1) < 1`. -/

theorem pow_eq_val_exp_neg_lt_one {n : ℕ} (hn : 1 ≤ n) :
    (WithZero.exp (-(n : ℤ)) : Zstar0) < 1 := by
  have h : WithZero.exp (-(n : ℤ)) < WithZero.exp (0 : ℤ) := by
    rw [WithZero.exp_lt_exp]; omega
  simpa using h

theorem pow_eq_val_eq_one_of_val_sub_one_lt_one {F : Type*} [Field F]
    (vv : Valuation F Zstar0) {x : F} (h : vv (x - 1) < 1) : vv x = 1 := by
  have h' := Valuation.map_add_eq_of_lt_left vv (x := (1 : F)) (y := x - 1) (by simpa using h)
  rwa [show (1 : F) + (x - 1) = x by ring, Valuation.map_one] at h'

/-- **The `ℓ`-adic logarithm base case, with a general exponent `e`.**

Let `vv : Valuation F ℤᵐ⁰` be a valuation, `p` a prime with `vv p = exp (-e)`, and let
`exp`, `log` be mutually inverse on the ball `vv ≤ exp (-M)` with the usual additive
identities.  Then every `u` with `vv (u - 1) ≤ exp (-(M + e))` is a `p`-th power of an
element `y` with `vv (y - 1) ≤ exp (-1)`.

This is `Commons.NumberTheory.NumberField.Completion.powQuotRat_base` with the exponents
generalised from `vv p = exp (-1)` to `vv p = exp (-e)`. -/
theorem pow_eq_powQuotRat_base_gen {F : Type*} [Field F] (vv : Valuation F Zstar0)
    (p M e : ℕ) (hp : p.Prime) (hp0 : ((p : ℕ) : F) ≠ 0)
    (hM : 1 ≤ M) (exp log : F → F)
    (hexp0 : exp 0 = 1)
    (hexpm1 : ∀ x : F, vv x ≤ WithZero.exp (-(M : ℤ)) → vv (exp x - 1) = vv x)
    (hexpadd : ∀ x y : F, vv x ≤ WithZero.exp (-(M : ℤ)) → vv y ≤ WithZero.exp (-(M : ℤ)) →
      exp (x + y) = exp x * exp y)
    (hlogval : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M : ℤ)) → vv (log y) = vv (y - 1))
    (hloginv : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M : ℤ)) → exp (log y) = y)
    (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-(e : ℤ))) :
    ∀ u : F, vv (u - 1) ≤ WithZero.exp (-((M + e : ℕ) : ℤ)) →
      ∃ y : F, vv (y - 1) ≤ WithZero.exp (-1) ∧ y ^ p = u := by
  intro u hu
  by_cases hu1 : u = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [sub_self, map_zero]; exact bot_le
    · rw [hu1]; exact one_pow p
  -- the two ball comparisons
  have hNM : WithZero.exp (-((M + e : ℕ) : ℤ)) ≤
      (WithZero.exp (-(M : ℤ)) : Zstar0) := by
    rw [WithZero.exp_le_exp]; push_cast; omega
  have huM : vv (u - 1) ≤ WithZero.exp (-(M : ℤ)) := le_trans hu hNM
  have hle1 : WithZero.exp (-(M : ℤ)) ≤ (WithZero.exp (-1 : ℤ) : Zstar0) := by
    rw [WithZero.exp_le_exp]; omega
  set z : F := log u / ((p : ℕ) : F) with hzdef
  -- `z` lies in the ball of radius `exp (-M)`
  have hzval : vv z ≤ WithZero.exp (-(M : ℤ)) := by
    rw [hzdef, Valuation.map_div, hlogval u huM, hvalp, div_eq_mul_inv]
    have h1 : (WithZero.exp (-(e : ℤ)) : Zstar0)⁻¹ = WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_neg]; congr 1; ring
    rw [h1]
    calc vv (u - 1) * WithZero.exp ((e : ℕ) : ℤ)
        ≤ WithZero.exp (-((M + e : ℕ) : ℤ)) * WithZero.exp ((e : ℕ) : ℤ) :=
          mul_le_mul' hu (le_refl _)
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]; congr 1; push_cast; ring
  -- every natural multiple of `z` lies in the ball
  have hdisk : ∀ m : ℕ, vv ((m : ℕ) • z) ≤ WithZero.exp (-(M : ℤ)) := by
    intro m
    rw [nsmul_eq_mul, Valuation.map_mul]
    calc vv ((m : ℕ) : F) * vv z ≤ 1 * WithZero.exp (-(M : ℤ)) :=
          mul_le_mul' (Commons.Analysis.Nonarchimedean.val_natCast_le_one vv m) hzval
      _ = WithZero.exp (-(M : ℤ)) := one_mul _
  have hpow_exp : ∀ m : ℕ, exp ((m : ℕ) • z) = (exp z) ^ m := by
    intro m; induction m with
    | zero => rw [zero_nsmul, hexp0, pow_zero]
    | succ m ih => rw [succ_nsmul, hexpadd _ _ (hdisk m) hzval, ih, pow_succ]
  have hzlog : (p : ℕ) • z = log u := by
    rw [hzdef, nsmul_eq_mul]
    field_simp
  refine ⟨exp z, ?_, ?_⟩
  · rw [hexpm1 z hzval]
    exact le_trans hzval hle1
  · rw [← hpow_exp p, hzlog, hloginv u huM]

/-- **`ℓ`-th powers near `1` in a `p`-adic completion: the `ℓ`-adic logarithm route.**

Let `k = v.adicCompletion K` be the completion of a number field at a finite prime and let `ℓ` be a
prime with `Valued.v ((ℓ : ℕ) : k) = WithZero.exp (-(e : ℤ))`.  Then for some explicit `N` the
closed ball of radius `exp (-N)` around `1` consists of `ℓ`-th powers of units of `k`.

Proof route (this is `Commons.NumberTheory.NumberField.Completion.powQuotRat_base` of
`Submission/Commons/NumberTheory/NumberField/Completion/natCard_powerQuotient_adicCompletion_rat_units.lean`
with the exponents generalised from `v (p) = exp (-1)` to `v (ℓ) = exp (-e)`; the proof there can be
copied verbatim, replacing `1` by `e` wherever it occurs in an exponent):

* `obtain ⟨M, hM1, exp, log, hexpsum, hexpm1, hexp0, hexpadd, hlog, hlogexp⟩ :=
  Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq v`, the `p`-adic
  exponential/logarithm with their identities on the ball `v ≤ exp (-M)`;
* take `N := M + e`; then `exp (-(N : ℤ)) ≤ exp (-(M : ℤ)) ≤ exp (-1)`;
* for `x` with `v (x - 1) ≤ exp (-N)`: `v (log x) = v (x - 1)` and `exp (log x) = x`;
* put `z := log x / ((ℓ : ℕ) : k)`.  Then `v z = v (log x) · (v ℓ)⁻¹ ≤ exp (-N) · exp e = exp (-M)`,
  so `z` lies in the domain of `exp`; also `((ℓ : ℕ) : k) ≠ 0` follows from `hval` and
  `(Valuation.ne_zero_iff _).mp (by rw [hval]; exact WithZero.exp_ne_zero)`;
* `(exp z) ^ ℓ = exp ((ℓ : ℕ) • z) = exp (log x) = x`: iterate `hexpadd` (each multiple `m • z` has
  `v (m • z) ≤ exp (-M)` by `Commons.Analysis.Nonarchimedean.val_natCast_le_one`), and
  `(ℓ : ℕ) • z = log x` by `field_simp`;
* finally `v (exp z - 1) = v z ≤ exp (-1)`, so `y := Units.mk0 (exp z) _` is a unit of `k`. -/
theorem pow_eq_of_val_le_exp_neg (K : Type*) [Field K] [NumberField K]
    (v : NK.Chebotarev.PrimeIdeal K) (ℓ : ℕ) (hℓ : ℓ.Prime) (e : ℕ)
    (hval : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) ((ℓ : ℕ) : v.adicCompletion K) =
      WithZero.exp (-(e : ℤ))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x : v.adicCompletion K,
      Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) (x - 1) ≤ WithZero.exp (-(N : ℤ)) →
        ∃ y : (v.adicCompletion K)ˣ, ((y : v.adicCompletion K)) ^ ℓ = x := by
  obtain ⟨M, hM1, exp, log, _hexpsum, hexpm1, hexp0, hexpadd, hlog, _hlogexp⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq v
  have hℓ0 : ((ℓ : ℕ) : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0))).mp
      (by rw [hval]; exact WithZero.exp_ne_zero)
  refine ⟨M + e, by omega, ?_⟩
  intro x hx
  obtain ⟨y, hy1, hyp⟩ :=
    pow_eq_powQuotRat_base_gen (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0))
      ℓ M e hℓ hℓ0 hM1 exp log hexp0 hexpm1 hexpadd
      (fun w hw => (hlog w hw).2.1) (fun w hw => (hlog w hw).2.2) hval x hx
  have hylt : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) (y - 1) < 1 :=
    lt_of_le_of_lt hy1 (pow_eq_val_exp_neg_lt_one le_rfl)
  have hyval : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) y = 1 :=
    pow_eq_val_eq_one_of_val_sub_one_lt_one _ hylt
  refine ⟨Units.mk0 y ((Valuation.ne_zero_iff
      (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0))).mp ?_), ?_⟩
  · rw [hyval]; exact one_ne_zero
  · rw [Units.val_mk0]; exact hyp

end NK.UchidaKummer.Approximation
