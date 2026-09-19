import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace Commons.NumberTheory.ArithmeticFunction

open Finset Nat
open scoped BigOperators

/-!
# Vaughan's identity for the von Mangoldt function

This file proves the classical "Vaughan identity" expressing the von Mangoldt
function as a truncated divisor expansion, in the precise Finset form needed for
the bounded-gaps sieve:

`Λ n = ∑_{d | n, d ≤ U} μ d · log (n / d)
      - ∑_{d | n, d ≤ U} ∑_{e | n/d, e ≤ V} μ d · Λ e
      + ∑_{d | n, d > U} ∑_{e | n/d, e > V} μ d · Λ e`.

The proof reduces the identity to the single vanishing statement
`∑_{d | n} ∑_{e | n/d, e ≤ V} μ d · Λ e = 0` (valid because `V < n`), which is
established via Dirichlet convolution of arithmetic functions.
-/

/-- The arithmetic function `e ↦ [e ≤ V] · Λ e`. -/
private noncomputable def vaughanH (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun e => if e ≤ V then ArithmeticFunction.vonMangoldt e else 0, by simp⟩

@[simp] private theorem vaughanH_apply (V e : ℕ) :
    vaughanH V e = if e ≤ V then ArithmeticFunction.vonMangoldt e else 0 := rfl

/-- The Möbius sum over the divisors of `m` is the Dirichlet delta. -/
private theorem sum_moebius_divisors_eq (m : ℕ) :
    (∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if m = 1 then 1 else 0 := by
  have key : (∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ArithmeticFunction.intCoe_apply]
  rw [key, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The truncated Möbius–von Mangoldt double sum vanishes for `V < n`. -/
private theorem sum_moebius_vonMangoldt_filter_eq_zero (n V : ℕ) (hn : V < n) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e) = 0 := by
  set G : ArithmeticFunction ℝ :=
    vaughanH V * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) with hGdef
  have hG : ∀ m, G m = ∑ e ∈ m.divisors, vaughanH V e := by
    intro m
    rw [hGdef, ArithmeticFunction.coe_mul_zeta_apply]
  have hT1 : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * G (n / d) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.mul_sum, hG, Finset.sum_filter]
    congr 1
  have hT2 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * G (n / d))
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * G) n := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (f := fun a b => (ArithmeticFunction.moebius : ArithmeticFunction ℝ) a * G b)]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ArithmeticFunction.intCoe_apply]
  have hT3 : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * G) n = 0 := by
    have hcong : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * G)
        = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * vaughanH V) := by
      rw [hGdef, ← mul_assoc,
        mul_comm ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * vaughanH V)
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
    rw [hcong, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul,
      vaughanH_apply, if_neg (by omega)]
  rw [hT1, hT2, hT3]

theorem vonMangoldt_eq_vaughan_sum (n U V : ℕ) (hn : V < n) :
    ArithmeticFunction.vonMangoldt n =
      (∑ d ∈ n.divisors.filter (fun d => d ≤ U),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
      - (∑ d ∈ n.divisors.filter (fun d => d ≤ U),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e)
      + (∑ d ∈ n.divisors.filter (fun d => U < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => V < e),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e) := by
  set S1 : ℝ := ∑ d ∈ n.divisors.filter (fun d => d ≤ U),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) with hS1
  set S2 : ℝ := ∑ d ∈ n.divisors.filter (fun d => d ≤ U),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e with hS2
  set S3 : ℝ := ∑ d ∈ n.divisors.filter (fun d => U < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => V < e),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e with hS3
  set B : ℝ := ∑ d ∈ n.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) with hB
  set D : ℝ := ∑ d ∈ n.divisors.filter (fun d => U < d),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) with hD
  set D1 : ℝ := ∑ d ∈ n.divisors.filter (fun d => U < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e with hD1
  set T : ℝ := ∑ d ∈ n.divisors,
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e with hT
  have hbase : ArithmeticFunction.vonMangoldt n = B := by
    rw [hB, ← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (f := fun a b => (ArithmeticFunction.moebius : ArithmeticFunction ℝ) a *
          ArithmeticFunction.log b)]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
  have hfilU : n.divisors.filter (fun d => ¬ d ≤ U) = n.divisors.filter (fun d => U < d) :=
    Finset.filter_congr (fun d _ => by omega)
  have hsplit1 : B = S1 + D := by
    rw [hB, hS1, hD, ← Finset.sum_filter_add_sum_filter_not (s := n.divisors)
      (p := fun d => d ≤ U)
      (f := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        Real.log (((n / d : ℕ) : ℝ)))]
    rw [hfilU]
  have hsplit2 : S2 + D1 = T := by
    rw [hS2, hD1, hT, ← Finset.sum_filter_add_sum_filter_not (s := n.divisors)
      (p := fun d => d ≤ U)
      (f := fun d => ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e)]
    rw [hfilU]
  have hDS : D = D1 + S3 := by
    rw [hD, hD1, hS3, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hlog2 : Real.log (((n / d : ℕ) : ℝ))
        = ∑ e ∈ (n / d).divisors, ArithmeticFunction.vonMangoldt e :=
      ArithmeticFunction.vonMangoldt_sum.symm
    have hfilV : (n / d).divisors.filter (fun e => ¬ e ≤ V)
        = (n / d).divisors.filter (fun e => V < e) :=
      Finset.filter_congr (fun e _ => by omega)
    have hsp : (∑ e ∈ (n / d).divisors, ArithmeticFunction.vonMangoldt e)
        = (∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
              ArithmeticFunction.vonMangoldt e)
        + (∑ e ∈ (n / d).divisors.filter (fun e => V < e),
              ArithmeticFunction.vonMangoldt e) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (n / d).divisors)
        (p := fun e => e ≤ V) (f := fun e => ArithmeticFunction.vonMangoldt e), hfilV]
    rw [hlog2, hsp, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hT0 : T = 0 := by
    rw [hT]
    exact sum_moebius_vonMangoldt_filter_eq_zero n V hn
  have hD1neg : D1 = -S2 := by
    have := hsplit2
    rw [hT0] at this
    linarith
  calc ArithmeticFunction.vonMangoldt n = S1 + D := hbase.trans hsplit1
    _ = S1 + (D1 + S3) := by rw [hDS]
    _ = S1 - S2 + S3 := by rw [hD1neg]; ring

end Commons.NumberTheory.ArithmeticFunction