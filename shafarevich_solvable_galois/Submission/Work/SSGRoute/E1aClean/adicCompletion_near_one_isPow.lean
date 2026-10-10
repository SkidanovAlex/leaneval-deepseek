import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.Analysis.Nonarchimedean.val_pow_sub_one_le_exp_neg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

namespace Work.SSGRoute.E1aClean

open IsDedekindDomain

/-- Auxiliary lemma, purely in the value group: suppose an exponential map `exp` with an inverse
`log` is available on the ball `v x ≤ exp (-M)` of a field `F` carrying a `ℤᵐ⁰`-valued valuation,
in the sense that `exp` is additive there and `exp (log y) = y` for `y` close to `1`. If
additionally `exp (-N) * v (n⁻¹) ≤ exp (-M)` (the correction needed to be able to divide by `n`),
then every `y` with `v (y - 1) ≤ exp (-N)` is an `n`-th power.

The proof writes `y = exp (log y)` and takes `w = exp (log y / n)`: on the ball the exponential is
additive, so `(exp (log y / n)) ^ n = exp (n * (log y / n)) = exp (log y) = y`. -/
private theorem exists_units_pow_of_val_le {F : Type*} [Field F] [CharZero F]
    (v : Valuation F (WithZero (Multiplicative ℤ)))
    (M N : ℕ) (hMN : M ≤ N) (exp log : F → F) (hexp_zero : exp 0 = 1)
    (hadd : ∀ x y : F, v x ≤ WithZero.exp (-(M : ℤ)) → v y ≤ WithZero.exp (-(M : ℤ)) →
      exp (x + y) = exp x * exp y)
    (hlog : ∀ y : F, v (y - 1) ≤ WithZero.exp (-(M : ℤ)) →
      v (log y) = v (y - 1) ∧ exp (log y) = y)
    {n : ℕ} (hn : 0 < n)
    (hcorr : WithZero.exp (-(N : ℤ)) * v (((n : ℕ) : F)⁻¹) ≤ WithZero.exp (-(M : ℤ))) :
    ∀ y : F, v (y - 1) ≤ WithZero.exp (-(N : ℤ)) → ∃ w : Fˣ, ((w : F)) ^ n = y := by
  intro y hyN
  have hn0 : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hyM : v (y - 1) ≤ WithZero.exp (-(M : ℤ)) :=
    hyN.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hMN)))
  obtain ⟨hlog_eq, hexp_log⟩ := hlog y hyM
  set x : F := log y / ((n : ℕ) : F) with hx
  have hxval : v x ≤ WithZero.exp (-(M : ℤ)) := by
    have hdiv : v x = v (log y) * v (((n : ℕ) : F)⁻¹) := by
      rw [hx, div_eq_mul_inv, Valuation.map_mul, Valuation.map_inv]
    rw [hdiv, hlog_eq]
    exact (mul_le_mul' hyN (le_refl _)).trans hcorr
  have hxn : ((n : ℕ) : F) * x = log y := by
    rw [hx]
    exact mul_div_cancel₀ (log y) hn0
  have hpow : ∀ m : ℕ, exp (((m : ℕ) : F) * x) = (exp x) ^ m := by
    intro m
    induction m with
    | zero => simpa using hexp_zero
    | succ m ih =>
        have hm : v (((m : ℕ) : F) * x) ≤ WithZero.exp (-(M : ℤ)) := by
          rw [Valuation.map_mul]
          calc v ((m : ℕ) : F) * v x ≤ 1 * WithZero.exp (-(M : ℤ)) :=
                mul_le_mul' (Commons.Analysis.Nonarchimedean.val_natCast_le_one v m) hxval
            _ = WithZero.exp (-(M : ℤ)) := one_mul _
        rw [show (((m + 1 : ℕ)) : F) * x = ((m : ℕ) : F) * x + x by push_cast; ring]
        rw [hadd _ _ hm hxval, ih, pow_succ]
  have hexpnz : exp x ≠ 0 := by
    intro h0
    have hxneg : v (-x) ≤ WithZero.exp (-(M : ℤ)) := by
      rw [Valuation.map_neg]
      exact hxval
    have h := hadd x (-x) hxval hxneg
    rw [add_neg_cancel, hexp_zero, h0, zero_mul] at h
    exact one_ne_zero h
  refine ⟨Units.mk0 (exp x) hexpnz, ?_⟩
  rw [Units.val_mk0, ← hpow n, hxn, hexp_log]

theorem adicCompletion_near_one_isPow {K : Type} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) (hn : 0 < n) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : q.adicCompletion K, ‖y - 1‖ < r →
      ∃ w : (q.adicCompletion K)ˣ, ((w : q.adicCompletion K)) ^ n = y := by
  classical
  have hF : CharZero (q.adicCompletion K) := algebraRat.charZero _
  obtain ⟨M, hM, exp, log, -, -, hexp_zero, hadd, hlog, -⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq (K := K) q
  obtain ⟨π, hπval, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one (K := K) q
  have hn0 : ((n : ℕ) : q.adicCompletion K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hπne : ((π : q.adicCompletionIntegers K) : q.adicCompletion K) ≠ 0 := by
    intro h
    have h0 : Valued.v (R := q.adicCompletion K)
        ((π : q.adicCompletionIntegers K) : q.adicCompletion K) = 0 := by
      rw [h, Valuation.map_zero]
    rw [hπval] at h0
    exact WithZero.exp_ne_zero h0
  have hvinv_ne : Valued.v (R := q.adicCompletion K)
      (((n : ℕ) : q.adicCompletion K)⁻¹) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact inv_ne_zero hn0
  have hvinv_ge : (1 : WithZero (Multiplicative ℤ)) ≤
      Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K)⁻¹) := by
    have hvn_le : Valued.v (R := q.adicCompletion K) ((n : ℕ) : q.adicCompletion K) ≤ 1 :=
      Commons.Analysis.Nonarchimedean.val_natCast_le_one
        (Valued.v : Valuation (q.adicCompletion K) (WithZero (Multiplicative ℤ))) n
    have hvn_ne : Valued.v (R := q.adicCompletion K) ((n : ℕ) : q.adicCompletion K) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact hn0
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (R := q.adicCompletion K) ((n : ℕ) : q.adicCompletion K)
            * Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K)⁻¹) := by
          rw [← Valuation.map_mul, mul_inv_cancel₀ hn0, Valuation.map_one]
      _ ≤ 1 * Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K)⁻¹) :=
          mul_le_mul' hvn_le le_rfl
      _ = Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K)⁻¹) := one_mul _
  set k : ℤ := (Valued.v (R := q.adicCompletion K)
    (((n : ℕ) : q.adicCompletion K)⁻¹)).log with hk
  have hk_nonneg : 0 ≤ k := by
    refine WithZero.exp_le_exp.mp ?_
    rw [WithZero.exp_zero, hk, WithZero.exp_log hvinv_ne]
    exact hvinv_ge
  set N : ℕ := M + k.toNat with hN
  refine ⟨‖((π : q.adicCompletionIntegers K) : q.adicCompletion K) ^ N‖, ?_, ?_⟩
  · rw [norm_pos_iff]
    exact pow_ne_zero N hπne
  · intro y hy
    have h1 : Valued.v (R := q.adicCompletion K) (y - 1) ≤ WithZero.exp (-(N : ℤ)) := by
      have h2 : Valued.v (R := q.adicCompletion K) (y - 1) <
          Valued.v (R := q.adicCompletion K)
            (((π : q.adicCompletionIntegers K) : q.adicCompletion K) ^ N) :=
        Valued.toNormedField.norm_lt_iff.mp hy
      have hexpN : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^ N =
          WithZero.exp (-(N : ℤ)) := by
        rw [← WithZero.exp_nsmul]
        congr 1
        simp
      rw [Valuation.map_pow, hπval, hexpN] at h2
      exact le_of_lt h2
    have hcorr : WithZero.exp (-(N : ℤ)) *
        Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K))⁻¹ ≤
        WithZero.exp (-(M : ℤ)) := by
      have hvineq : Valued.v (R := q.adicCompletion K) (((n : ℕ) : q.adicCompletion K))⁻¹ =
          WithZero.exp k := by
        rw [hk]
        exact (WithZero.exp_log hvinv_ne).symm
      rw [hvineq, ← WithZero.exp_add]
      refine WithZero.exp_le_exp.mpr ?_
      rw [hN]
      have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
      push_cast
      omega
    exact exists_units_pow_of_val_le (Valued.v (R := q.adicCompletion K)) M N
      (by rw [hN]; exact Nat.le_add_right M k.toNat) exp log hexp_zero hadd
      (fun y hy => (hlog y hy).2) hn hcorr y h1

end Work.SSGRoute.E1aClean
