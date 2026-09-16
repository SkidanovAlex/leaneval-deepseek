import Mathlib.RingTheory.PowerSeries.Basic
import Submission.ZagierHoffmanProof.Omega
import Submission.ZagierHoffmanProof.EntireTwist
import Submission.Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero
import Submission.Commons.Topology.InfiniteSum.tsum_shift_one
import Submission.ZagierHoffmanProof.FrobPowTsum

/-!
# The depth-one `L`-series of Anderson–Thakur / Chang

The paper (Ngo Dac, §2.2.1) attaches to a tuple of positive integers `s = (s₁,…,s_r)` and
polynomials `Q = (Q₁,…,Q_r)` the series

  `L(s;Q) = ∑_{i₁ > ⋯ > i_r ≥ 0} (Ω^{s_r}Q_r)^{(i_r)} ⋯ (Ω^{s_1}Q_1)^{(i_1)}`,

where `Ω` is the Anderson–Thakur period function and `f^{(i)}` is the coefficientwise
`q^i`-th power twist.  This file develops the **depth-one** case `L(s;Q) = ∑_{i ≥ 0} (ω^sQ)^{(i)}`
(for a general "small" series `ω`, in a `ℤᵐ⁰`-valued field `K`).

The key analytic input is that all coefficients of the series `ω^sQ` lie in the maximal ideal of
the Tate algebra (`IsSmall`): this is exactly the paper's convergence condition (2.1).  Then the
`i`-th twisted factor has coefficients of valuation `≤ exp (-q^i) → 0`, so the defining sums
converge coefficientwise; and the series satisfies the "trivialisation" recursion

  `L = ω^s Q + L^{(1)}`.

For the true Anderson–Thakur period function `Ω` (with its normalising constant
`c = (−θ)^{−q/(q−1)}`, which is *not* in `K∞` — see `PLAN.md` SESSION 301 ADDENDUM (2)) the
paper's `Ω^s` is `IsSmall`; over `K∞` itself the concrete example is `C (θ⁻¹) * Ω̃` (the
normalised period function scaled by the small constant `θ⁻¹`).

## Main definitions and results

* `IsSmall f` — all coefficients of `f` lie in the maximal ideal of the Tate algebra.
* `atL1 q ω s Q` — the depth-one `L`-series `∑_{i ≥ 0} (ω^sQ)^{(i)}`.
* `summable_coeff_atL1_term` — the coefficientwise summability of the defining family.
* `atL1_add_frobTwist` — the recursion `L = ω^sQ + L^{(1)}`.
* `omegaSmall`, `isSmall_omegaSmall` — the concrete small series `θ⁻¹·Ω̃` over `K∞`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- A power series all of whose coefficients lie in the maximal ideal of the Tate algebra,
i.e. `v (coeff n f) ≤ exp (-1)` for every `n`.  This is the convergence condition for the
`L`-series. -/
def IsSmall (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp (-1)

section small

variable {f g : PowerSeries K}

lemma isSmall_zero : IsSmall (0 : PowerSeries K) := by
  intro n; rw [map_zero, map_zero]; exact bot_le

lemma IsSmall.neg (hf : IsSmall f) : IsSmall (-f) := by
  intro n; rw [map_neg (PowerSeries.coeff n) f, Valuation.map_neg]; exact hf n

lemma IsSmall.mul (hf : IsSmall f) (hg : IsSmall g) : IsSmall (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Valued.v.map_sum_le (fun p hp => ?_)
  rw [Valuation.map_mul]
  calc Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
      ≤ WithZero.exp (-1) * WithZero.exp (-1) := mul_le_mul' (hf p.1) (hg p.2)
    _ = WithZero.exp (-1 + -1) := by rw [← WithZero.exp_add]
    _ ≤ WithZero.exp (-1) := WithZero.exp_le_exp.mpr (by omega)

lemma IsSmall.pow_add_one (hf : IsSmall f) (s : ℕ) : IsSmall (f ^ (s + 1)) := by
  induction s with
  | zero => simpa using hf
  | succ s ih => rw [pow_succ]; exact ih.mul hf

lemma IsSmall.pow_mul (hf : IsSmall f) (hg : IsSmall g) (s : ℕ) : IsSmall (f ^ s * g) := by
  cases s with
  | zero => simpa using hg
  | succ s => rw [pow_succ]; exact (hf.pow_add_one s).mul hg

end small

section Lseries

variable (q : ℕ) [FrobPow K q]

/-- The depth-one `L`-series `∑_{i ≥ 0} (ω^s Q)^{(i)}`. -/
noncomputable def atL1 (ω : PowerSeries K) (s : ℕ) (Q : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑' i : ℕ,
    PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))

lemma coeff_atL1 (ω : PowerSeries K) (s : ℕ) (Q : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (atL1 q ω s Q)
      = ∑' i : ℕ, PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q)) :=
  PowerSeries.coeff_mk n _

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The defining family of the depth-one `L`-series is coefficientwise summable: the valuation
of the `i`-th term is bounded by `exp (-q^i)`. -/
lemma summable_coeff_atL1_term (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s n : ℕ) :
    Summable fun i : ℕ =>
      PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q)) := by
  have hsmall : Valued.v (PowerSeries.coeff n (ω ^ s * Q)) ≤ WithZero.exp (-1) :=
    IsSmall.pow_mul hω hQ s n
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun N => ?_)
  rw [Filter.eventually_atTop]
  refine ⟨N.natAbs + 1, fun i hi => ?_⟩
  rw [frobTwist_coeff, map_pow]
  calc (Valued.v (PowerSeries.coeff n (ω ^ s * Q))) ^ (q ^ i)
      ≤ (WithZero.exp (-1)) ^ (q ^ i) := pow_le_pow_left' hsmall _
    _ = WithZero.exp (-1 * (((q ^ i : ℕ)) : ℤ)) := expmul (-1) (q ^ i)
    _ = WithZero.exp (-(((q ^ i : ℕ)) : ℤ)) := by rw [neg_one_mul]
    _ < WithZero.exp N := by
        apply WithZero.exp_lt_exp.mpr
        have h1 : i < q ^ i := Nat.lt_pow_self (by omega : 1 < q)
        have hi' : (N.natAbs : ℤ) + 1 ≤ (i : ℤ) := by omega
        have hq' : (i : ℤ) ≤ ((q ^ i : ℕ) : ℤ) := by exact_mod_cast le_of_lt h1
        have hN : (N : ℤ) ≤ (N.natAbs : ℤ) := Int.le_natAbs
        omega

/-- **The `L`-series recursion**: `L = ω^s Q + L^{(1)}`, i.e.
`∑_{i ≥ 0} (ω^sQ)^{(i)} = ω^sQ + ∑_{i ≥ 0} ((ω^sQ)^{(i)})^{(1)}`.
This is the `r = 1` case of the "rigid analytic trivialisation" relation
`Ψ^{(-1)} = ΦΨ` of the paper. -/
theorem atL1_eq_mul_add_frobTwist (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) :
    atL1 q ω s Q = ω ^ s * Q + frobTwist (R := K) (p := q) 1 (atL1 q ω s Q) := by
  ext n
  have hsum := summable_coeff_atL1_term q hq hω hQ s n
  have hstep : (∑' i : ℕ, (PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))) ^ (q ^ 1))
      = ∑' i : ℕ, PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + 1) (ω ^ s * Q)) := by
    refine tsum_congr (fun i => ?_)
    rw [frobTwist_coeff, frobTwist_coeff, ← pow_mul, pow_one, ← pow_succ]
  rw [coeff_atL1, map_add (PowerSeries.coeff n), frobTwist_coeff, coeff_atL1,
    ZagierHoffmanPositiveChar.tsum_pow_frobPow hsum 1, hstep,
    Commons.Topology.InfiniteSum.tsum_shift_one hsum]
  have h0 : PowerSeries.coeff n (frobTwist (R := K) (p := q) 0 (ω ^ s * Q))
      = PowerSeries.coeff n (ω ^ s * Q) := by
    rw [frobTwist_coeff, pow_zero, pow_one]
  rw [h0]
  ring

end Lseries

section concrete

variable (q : ℕ) (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The concrete "small" series over `K`: `θ⁻¹ · Ω̃`, where `Ω̃` is the normalised
Anderson–Thakur period function.  The paper's period function is `c·Ω̃` with the constant
`c = (−θ)^{−q/(q−1)}`, which is *not* in `K` (it is a fractional power of `θ`); the constant
`θ⁻¹ ∈ K` plays the role of a small normalising constant and makes the series `IsSmall`, which is
exactly the convergence condition for the `L`-series. -/
noncomputable def omegaSmall : PowerSeries K := PowerSeries.C (θ⁻¹) * atOmega q θ

lemma isSmall_omegaSmall (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    IsSmall (omegaSmall q θ) := by
  intro n
  rw [omegaSmall, PowerSeries.coeff_C_mul, Valuation.map_mul, Valuation.map_inv, hθ,
    ← WithZero.exp_neg]
  have h1 : Valued.v (PowerSeries.coeff n (atOmega q θ)) ≤ 1 :=
    le_trans (v_coeff_atOmega_le q θ hθ hq n) (WithZero.exp_le_exp.mpr (by omega))
  calc WithZero.exp (-1) * Valued.v (PowerSeries.coeff n (atOmega q θ))
      ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl h1
    _ = WithZero.exp (-1) := mul_one _

end concrete

section concreteTwist

variable (q : ℕ) [FrobPow K q] (θ : K) [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The twisted functional equation satisfied by `θ⁻¹Ω̃`: the normalising constant `θ⁻¹` turns
the period's functional equation into one with the constant `θ^{-(q-1)}` (of modulus `< 1`). -/
lemma omegaSmall_twist (hθ : Valued.v θ = WithZero.exp 1) (hq : 2 ≤ q) :
    (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * frobTwist (R := K) (p := q) 1 (omegaSmall q θ)
      = PowerSeries.C ((θ ^ (q - 1))⁻¹) * omegaSmall q θ := by
  have hθq : θ ^ q = θ ^ (q - 1) * θ := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ q)]
    rw [pow_succ]
  have hpow : (θ⁻¹) ^ q = (θ ^ (q - 1))⁻¹ * θ⁻¹ := by
    rw [inv_pow, hθq, mul_inv]
  rw [omegaSmall, frobTwist_mul, frobTwist_C, pow_one, hpow, map_mul]
  rw [show (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
        * ((PowerSeries.C ((θ ^ (q - 1))⁻¹) * PowerSeries.C (θ⁻¹))
            * frobTwist (R := K) (p := q) 1 (atOmega q θ))
      = (PowerSeries.C ((θ ^ (q - 1))⁻¹) * PowerSeries.C (θ⁻¹))
        * ((1 - PowerSeries.C (omX q θ 1) * PowerSeries.X)
            * frobTwist (R := K) (p := q) 1 (atOmega q θ)) from by ring,
    atOmega_twist q θ hθ hq, mul_assoc]

end concreteTwist





end ZagierHoffmanPositiveChar
