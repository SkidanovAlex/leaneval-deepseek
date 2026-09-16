import Submission.ZagierHoffmanProof.SuperEntire
import Submission.ZagierHoffmanProof.EntireApp

/-!
# The Carlitz exponential belongs to `ε`

The ring `ε` of `SuperEntire.lean` is the ring of Anderson–Brownawell–Papanikolas.  We show that the
Carlitz exponential (viewed as a power series over `K∞` through `seriesToK`) lies in it.  The
Carlitz logarithm, in contrast, only lies in the Tate algebra `T` (see `entire_carlitzLog`): its
coefficients decay like `exp (-(q/(q-1))·n)`, so the root test for `ε` fails, in agreement with the
classical radius of convergence `|θ|^{q/(q-1)}` of `log_C`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **The Carlitz exponential is super-entire** (belongs to ABP's `ε`). -/
theorem superEntire_carlitzExp : SuperEntire (seriesToK F (carlitzExp F)) := by
  intro M
  refine ⟨((M : ℤ) + 1) * ((Nat.card F : ℤ)) ^ M, fun n => ?_⟩
  rw [seriesToK_coeff]
  by_cases h : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, hi⟩ := h
    subst hi
    rw [show PowerSeries.coeff (Nat.card F ^ i) (carlitzExp F) = carlitzECoeff F (Nat.card F ^ i)
        from PowerSeries.coeff_mk _ _, carlitzECoeff_pow F i,
      v_algebraMap_carlitzFact_inv F i, WithZero.exp_le_exp]
    have hq1 : (1 : ℤ) ≤ (Nat.card F : ℤ) := by have := two_le_card F; omega
    have hcast : (((i * Nat.card F ^ i : ℕ)) : ℤ) = (i : ℤ) * (Nat.card F : ℤ) ^ i := by
      push_cast; ring
    have hcastpow : (((Nat.card F ^ i : ℕ)) : ℤ) = (Nat.card F : ℤ) ^ i := by
      push_cast; ring
    rw [hcast, hcastpow]
    by_cases hle : i ≤ M
    · have h1 : (Nat.card F : ℤ) ^ i ≤ (Nat.card F : ℤ) ^ M := pow_le_pow_right₀ hq1 hle
      have h2 : (0 : ℤ) ≤ (M : ℤ) - i := by
        have : (i : ℤ) ≤ (M : ℤ) := by exact_mod_cast hle
        omega
      have h3 : ((M : ℤ) - i) * (Nat.card F : ℤ) ^ i
          ≤ ((M : ℤ) - i) * (Nat.card F : ℤ) ^ M :=
        mul_le_mul_of_nonneg_left h1 h2
      have h4 : ((M : ℤ) - i) * (Nat.card F : ℤ) ^ M
          ≤ ((M : ℤ) + 1) * (Nat.card F : ℤ) ^ M := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (0 : ℤ) ≤ (i : ℤ) := by positivity
        omega
      linarith
    · have hle0 : ((M : ℤ) - i) * (Nat.card F : ℤ) ^ i ≤ 0 := by
        refine mul_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
        have : (M : ℤ) < (i : ℤ) := by
          have : M < i := Nat.lt_of_not_le hle
          exact_mod_cast this
        omega
      have hge0 : (0 : ℤ) ≤ ((M : ℤ) + 1) * (Nat.card F : ℤ) ^ M := by positivity
      linarith
  · rw [show PowerSeries.coeff n (carlitzExp F) = carlitzECoeff F n from PowerSeries.coeff_mk _ _,
      carlitzECoeff_eq_zero F (fun i hi => h ⟨i, hi⟩),
      map_zero (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)),
      map_zero (Valued.v)]
    exact bot_le

end ZagierHoffmanPositiveChar
