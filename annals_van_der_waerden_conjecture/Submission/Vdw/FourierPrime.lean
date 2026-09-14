import Mathlib
import Submission.Vdw.BoxFourierIndex

open Polynomial Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The single-prime §4 output: the paper's `ftgen2` input implies the per-prime
index bound (Corollary `index2forms2`)

`BoxFourierIndex.box_index_fourier_le` is the project's per-prime Fourier
counting bound: *given* a bound `M` for the Fourier coefficients of the
index-`≥ k` residue set on the nonzero frequencies, the number of box
polynomials whose reduction mod `p` has index `≥ k` is at most

    `|T_{p,k}|·(2H+1)^n/p^n + M/p^n·(5(p + 2H+1)(1+log p))^n`.

This module supplies the paper's *input* for `M` — Proposition `ftgen2`,
namely `M(Ψ) = O(p^{-(k+1/2)})` for the index-`≥ k` set (the exponent `k+1/2`
is the Weil-refined case `d = n` of `ftgen2`; the `O(p^{-(k+1)})` case `d < n`
is weaker) — as the Prop `MIndexBound`, and derives the single-prime counting
bound

    `#{f ∈ Box n H : index (f mod p) ≥ k}
        ≤ C·(2H+1)^n/p^k + C·(p + 2H+1)^n(1+log p)^n/p^{k+1/2}`,

together with the paper's `H ≤ p` shape

    `≤ C·H^n/p^k + C·p^{n-k-1/2}(1+log p)^n`,

i.e. Corollary `index2forms2` with the logarithmic factor kept explicit (the
`C^ε` of the paper, to be absorbed by the `ε` of the multi-prime statement
`FourierDequi.DequiBound`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- The (unnormalized) Fourier coefficient of the index-`≥ k` residue set
`T_{p,k} ⊆ (ZMod p)^n`, at the frequency `a`: the paper's `p^n·Ψ̂(a)`. -/
noncomputable def indexFourierCoeff (p : ℕ) [Fact (Nat.Prime p)] (n k : ℕ)
    (a : Fin n → ZMod p) : ℂ :=
  ∑ v ∈ indexClassFinset p n k, ZMod.stdAddChar (∑ i, a i * v i)

/-- **Paper Proposition `ftgen2` (index-set form).**

There is `C` such that for every prime `p` and every `k ≤ n`, every nonzero
frequency `a` satisfies

    `‖Σ_{v ∈ T_{p,k}} stdAddChar (a·v)‖ ≤ C·p^{n-k-1/2}`

— the Weil-refined `O(p^{-(k+1/2)})` bound on the Fourier transform of the
index-`≥ k` set, multiplied by `p^n` to match the unnormalized sum used by the
project's Fourier machinery. -/
def MIndexBound (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (p : ℕ) [Fact (Nat.Prime p)], ∀ k : ℕ, k ≤ n →
      ∀ a : Fin n → ZMod p, a ≠ 0 →
        ‖indexFourierCoeff p n k a‖ ≤ C * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2)

/-- The cardinality of the index-`≥ k` residue set: at most
`2^((n+1)^4)·p^{n-k}` (CI-1 in the Fourier normalization used here). -/
theorem indexClassFinset_card_le (p : ℕ) [Fact (Nat.Prime p)] (n k : ℕ) (hk : k ≤ n) :
    (indexClassFinset p n k).card ≤ 2 ^ ((n + 1) ^ 4) * p ^ (n - k) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have h1 : (indexClassFinset p n k).card =
      Nat.card {v : Fin n → ZMod p // indexClass (F := ZMod p) n k v} := by
    rw [indexClassFinset,
      ← Fintype.card_subtype (fun v : Fin n → ZMod p => indexClass (F := ZMod p) n k v)]
    exact (Nat.card_eq_fintype_card).symm
  rw [h1]
  have h2 := indexClass_card_le (F := ZMod p) n k hk
  rwa [ZMod.card] at h2

/-- **The per-prime §4 output**: `MIndexBound` implies the single-prime index
bound with the exact shape delivered by `box_index_fourier_le`. -/
theorem perPrime_index_bound (n : ℕ) (hM : MIndexBound n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k H : ℕ), k ≤ n →
      (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
        ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
          + C * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
              / (p : ℝ) ^ ((k : ℝ) + 1 / 2)) := by
  classical
  obtain ⟨C₀, hC₀, hC₀b⟩ := hM
  refine ⟨max ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n), le_max_of_le_left (by positivity), ?_⟩
  intro p _inst k H hk
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  set M : ℝ := C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hfourier : ∀ a : Fin n → ZMod p, a ≠ 0 →
      ‖∑ v ∈ indexClassFinset p n k, ZMod.stdAddChar (∑ i, a i * v i)‖ ≤ M := by
    intro a ha
    simpa only [indexFourierCoeff, hMdef] using hC₀b p k hk a ha
  have hbound := box_index_fourier_le p n H k M hM0 hfourier
  -- cardinality of the index set
  have hcard : ((indexClassFinset p n k).card : ℝ)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by
    have h := indexClassFinset_card_le p n k hk
    have h2 : ((indexClassFinset p n k).card : ℝ)
        ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := by exact_mod_cast h
    calc ((indexClassFinset p n k).card : ℝ)
        ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := h2
      _ = (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by push_cast; ring
  -- the two algebraic identities
  have hpk : (p : ℝ) ^ (n - k) / (p : ℝ) ^ n = 1 / (p : ℝ) ^ k := by
    have h1 : (p : ℝ) ^ (n - k) * (p : ℝ) ^ k = (p : ℝ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    field_simp
    exact h1
  have hrp : (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) / (p : ℝ) ^ n
      = 1 / (p : ℝ) ^ ((k : ℝ) + 1 / 2) := by
    rw [← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_sub hp0]
    have hexp : (n : ℝ) - (k : ℝ) - 1 / 2 - (n : ℝ) = -((k : ℝ) + 1 / 2) := by ring
    rw [hexp, Real.rpow_neg hp0.le]
    exact inv_eq_one_div _
  -- the two term bounds
  have hT1 : ((indexClassFinset p n k).card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ n
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by
    have h2 : ((indexClassFinset p n k).card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n
        ≤ ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (by positivity))
        (by positivity)
    have h3 : ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n
        = (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by
      rw [show ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
            / (p : ℝ) ^ n
          = (2 : ℝ) ^ ((n + 1) ^ 4)
            * (((2 * H + 1 : ℕ) : ℝ) ^ n * ((p : ℝ) ^ (n - k) / (p : ℝ) ^ n)) from by ring,
        hpk,
        show (2 : ℝ) ^ ((n + 1) ^ 4)
            * (((2 * H + 1 : ℕ) : ℝ) ^ n * (1 / (p : ℝ) ^ k))
          = (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) from by ring]
    exact le_trans h2 (le_of_eq h3)
  have hT2 : M / (p : ℝ) ^ n
        * (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
      ≤ (C₀ * 5 ^ n) * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + 1 / 2)) := by
    have heq : C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) / (p : ℝ) ^ n
          * (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
        = (C₀ * 5 ^ n) * (((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n)
          * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) / (p : ℝ) ^ n) := by
      have hmp : (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
          = 5 ^ n * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n := by
        rw [mul_pow, mul_pow]
      rw [hmp]
      ring
    rw [hMdef, heq, hrp]
    exact le_of_eq (by ring)
  -- assemble
  have hsum : (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + (C₀ * 5 ^ n) * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + 1 / 2)) :=
    le_trans hbound (add_le_add hT1 hT2)
  refine le_trans hsum ?_
  have hX0 : (0 : ℝ) ≤ (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by positivity
  have hY0 : (0 : ℝ) ≤ ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
      / (p : ℝ) ^ ((k : ℝ) + 1 / 2)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n)) hX0
  have h2 := mul_le_mul_of_nonneg_right (le_max_right ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n)) hY0
  linarith

/-- **The paper's Corollary `index2forms2`** (log-tolerant form): in the regime
`H ≤ p` the error term simplifies to `p^{n-k-1/2}(log p)^n`. -/
theorem perPrime_index_bound_le (n : ℕ) (hM : MIndexBound n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k H : ℕ), k ≤ n → H ≤ p →
      (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
        ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
          + C * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n) := by
  obtain ⟨C, hC, hCb⟩ := perPrime_index_bound n hM
  refine ⟨C * 4 ^ n, by positivity, ?_⟩
  intro p _inst k H hk hHp
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hbound := hCb p k H hk
  refine le_trans hbound ?_
  -- the error-term comparison
  have hsp : ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ≤ 4 * (p : ℝ) := by
    have h2 : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    have h3 : (H : ℝ) ≤ (p : ℝ) := by exact_mod_cast hHp
    rw [h2]
    linarith
  have h4p : ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n ≤ (4 * (p : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hsp n
  have hdiv : (p : ℝ) ^ n / (p : ℝ) ^ ((k : ℝ) + 1 / 2)
      = (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_sub hp0]
    congr 1
    ring
  have hstep : ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
        / (p : ℝ) ^ ((k : ℝ) + 1 / 2))
      ≤ 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n) := by
    have hlog0 : (0 : ℝ) ≤ (1 + Real.log p) ^ n := by positivity
    have h1 : (((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
          / (p : ℝ) ^ ((k : ℝ) + 1 / 2)
        ≤ ((4 * (p : ℝ)) ^ n * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + 1 / 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4p hlog0) (by positivity)
    have h2 : ((4 * (p : ℝ)) ^ n * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + 1 / 2)
        = 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n) := by
      rw [mul_pow,
        show (4 : ℝ) ^ n * (p : ℝ) ^ n * (1 + Real.log p) ^ n / (p : ℝ) ^ ((k : ℝ) + 1 / 2)
          = 4 ^ n * ((1 + Real.log p) ^ n * ((p : ℝ) ^ n / (p : ℝ) ^ ((k : ℝ) + 1 / 2)))
          from by ring,
        hdiv]
      ring
    exact le_trans h1 (le_of_eq h2)
  have hX0 : (0 : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k := by positivity
  have hC4 : C ≤ C * 4 ^ n := by
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    nlinarith [hC, h4]
  have h1 : C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
      ≤ C * 4 ^ n * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) :=
    le_trans (mul_le_mul_of_nonneg_right hC4 hX0) (le_of_eq (by ring))
  have h2 : C * (4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n))
      = C * 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n) := by
    ring
  calc C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
            / (p : ℝ) ^ ((k : ℝ) + 1 / 2))
      ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * (4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hC)
    _ ≤ C * 4 ^ n * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1 / 2) * (1 + Real.log p) ^ n) := by
        rw [h2]
        exact add_le_add h1 le_rfl


/-! ## θ-generic form of the per-prime §4 bound

The paper's §4 input is used in the development only through a *power saving*
`θ` in the per-prime Fourier bound.  Below, `MIndexBoundSaving n θ` is the
general form, and the two per-prime count bounds are re-derived for arbitrary
`θ`; the paper's `θ = 1/2` (Weil) case is the original `MIndexBound` and the
elementary Weyl bound supplies `θ = 2^{-n}` (`Submission.Vdw.WeylExpSum`). -/

/-- **The §4 Fourier input with a general power saving `θ`** (paper §4,
Proposition `ftgen2`): every nonzero Fourier coefficient of the index-`≥ k`
residue set satisfies `‖ĉ_p(a)‖ ≤ C·p^{n-k-θ}`. -/
def MIndexBoundSaving (n : ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (p : ℕ) [Fact (Nat.Prime p)], ∀ k : ℕ, k ≤ n →
      ∀ a : Fin n → ZMod p, a ≠ 0 →
        ‖indexFourierCoeff p n k a‖ ≤ C * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ)

/-- The paper's `θ = 1/2` (Weil) case is the original `MIndexBound`. -/
theorem mIndexBoundSaving_half_iff (n : ℕ) : MIndexBoundSaving n (1/2) ↔ MIndexBound n :=
  ⟨fun h => h, fun h => h⟩

/-- **The per-prime §4 output**: `MIndexBound` implies the single-prime index
bound with the exact shape delivered by `box_index_fourier_le`. -/
theorem perPrime_index_bound_saving (n : ℕ) (θ : ℝ) (hM : MIndexBoundSaving n θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k H : ℕ), k ≤ n →
      (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
        ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
          + C * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
              / (p : ℝ) ^ ((k : ℝ) + θ)) := by
  classical
  obtain ⟨C₀, hC₀, hC₀b⟩ := hM
  refine ⟨max ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n), le_max_of_le_left (by positivity), ?_⟩
  intro p _inst k H hk
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  set M : ℝ := C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hfourier : ∀ a : Fin n → ZMod p, a ≠ 0 →
      ‖∑ v ∈ indexClassFinset p n k, ZMod.stdAddChar (∑ i, a i * v i)‖ ≤ M := by
    intro a ha
    simpa only [indexFourierCoeff, hMdef] using hC₀b p k hk a ha
  have hbound := box_index_fourier_le p n H k M hM0 hfourier
  -- cardinality of the index set
  have hcard : ((indexClassFinset p n k).card : ℝ)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by
    have h := indexClassFinset_card_le p n k hk
    have h2 : ((indexClassFinset p n k).card : ℝ)
        ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := by exact_mod_cast h
    calc ((indexClassFinset p n k).card : ℝ)
        ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := h2
      _ = (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k) := by push_cast; ring
  -- the two algebraic identities
  have hpk : (p : ℝ) ^ (n - k) / (p : ℝ) ^ n = 1 / (p : ℝ) ^ k := by
    have h1 : (p : ℝ) ^ (n - k) * (p : ℝ) ^ k = (p : ℝ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    field_simp
    exact h1
  have hrp : (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) / (p : ℝ) ^ n
      = 1 / (p : ℝ) ^ ((k : ℝ) + θ) := by
    rw [← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_sub hp0]
    have hexp : (n : ℝ) - (k : ℝ) - θ - (n : ℝ) = -((k : ℝ) + θ) := by ring
    rw [hexp, Real.rpow_neg hp0.le]
    exact inv_eq_one_div _
  -- the two term bounds
  have hT1 : ((indexClassFinset p n k).card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ n
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by
    have h2 : ((indexClassFinset p n k).card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n
        ≤ ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (by positivity))
        (by positivity)
    have h3 : ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
          / (p : ℝ) ^ n
        = (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by
      rw [show ((2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ (n - k)) * ((2 * H + 1 : ℕ) : ℝ) ^ n
            / (p : ℝ) ^ n
          = (2 : ℝ) ^ ((n + 1) ^ 4)
            * (((2 * H + 1 : ℕ) : ℝ) ^ n * ((p : ℝ) ^ (n - k) / (p : ℝ) ^ n)) from by ring,
        hpk,
        show (2 : ℝ) ^ ((n + 1) ^ 4)
            * (((2 * H + 1 : ℕ) : ℝ) ^ n * (1 / (p : ℝ) ^ k))
          = (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) from by ring]
    exact le_trans h2 (le_of_eq h3)
  have hT2 : M / (p : ℝ) ^ n
        * (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
      ≤ (C₀ * 5 ^ n) * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + θ)) := by
    have heq : C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) / (p : ℝ) ^ n
          * (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
        = (C₀ * 5 ^ n) * (((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n)
          * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) / (p : ℝ) ^ n) := by
      have hmp : (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n
          = 5 ^ n * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n := by
        rw [mul_pow, mul_pow]
      rw [hmp]
      ring
    rw [hMdef, heq, hrp]
    exact le_of_eq (by ring)
  -- assemble
  have hsum : (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
      ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + (C₀ * 5 ^ n) * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n
            * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + θ)) :=
    le_trans hbound (add_le_add hT1 hT2)
  refine le_trans hsum ?_
  have hX0 : (0 : ℝ) ≤ (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) := by positivity
  have hY0 : (0 : ℝ) ≤ ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
      / (p : ℝ) ^ ((k : ℝ) + θ)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n)) hX0
  have h2 := mul_le_mul_of_nonneg_right (le_max_right ((2 : ℝ) ^ ((n + 1) ^ 4)) (C₀ * 5 ^ n)) hY0
  linarith

/-- **The paper's Corollary `index2forms2`** (log-tolerant form): in the regime
`H ≤ p` the error term simplifies to `p^{n-k-1/2}(log p)^n`. -/
theorem perPrime_index_bound_le_saving (n : ℕ) (θ : ℝ) (hM : MIndexBoundSaving n θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k H : ℕ), k ≤ n → H ≤ p →
      (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
        ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
          + C * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n) := by
  obtain ⟨C, hC, hCb⟩ := perPrime_index_bound_saving n θ hM
  refine ⟨C * 4 ^ n, by positivity, ?_⟩
  intro p _inst k H hk hHp
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hbound := hCb p k H hk
  refine le_trans hbound ?_
  -- the error-term comparison
  have hsp : ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ≤ 4 * (p : ℝ) := by
    have h2 : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    have h3 : (H : ℝ) ≤ (p : ℝ) := by exact_mod_cast hHp
    rw [h2]
    linarith
  have h4p : ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n ≤ (4 * (p : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hsp n
  have hdiv : (p : ℝ) ^ n / (p : ℝ) ^ ((k : ℝ) + θ)
      = (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) := by
    rw [← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_sub hp0]
    congr 1
    ring
  have hstep : ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
        / (p : ℝ) ^ ((k : ℝ) + θ))
      ≤ 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n) := by
    have hlog0 : (0 : ℝ) ≤ (1 + Real.log p) ^ n := by positivity
    have h1 : (((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
          / (p : ℝ) ^ ((k : ℝ) + θ)
        ≤ ((4 * (p : ℝ)) ^ n * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + θ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4p hlog0) (by positivity)
    have h2 : ((4 * (p : ℝ)) ^ n * (1 + Real.log p) ^ n) / (p : ℝ) ^ ((k : ℝ) + θ)
        = 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n) := by
      rw [mul_pow,
        show (4 : ℝ) ^ n * (p : ℝ) ^ n * (1 + Real.log p) ^ n / (p : ℝ) ^ ((k : ℝ) + θ)
          = 4 ^ n * ((1 + Real.log p) ^ n * ((p : ℝ) ^ n / (p : ℝ) ^ ((k : ℝ) + θ)))
          from by ring,
        hdiv]
      ring
    exact le_trans h1 (le_of_eq h2)
  have hX0 : (0 : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k := by positivity
  have hC4 : C ≤ C * 4 ^ n := by
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    nlinarith [hC, h4]
  have h1 : C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
      ≤ C * 4 ^ n * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k) :=
    le_trans (mul_le_mul_of_nonneg_right hC4 hX0) (le_of_eq (by ring))
  have h2 : C * (4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n))
      = C * 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n) := by
    ring
  calc C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * ((((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) ^ n * (1 + Real.log p) ^ n)
            / (p : ℝ) ^ ((k : ℝ) + θ))
      ≤ C * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * (4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hC)
    _ ≤ C * 4 ^ n * (((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ k)
        + C * 4 ^ n * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ) * (1 + Real.log p) ^ n) := by
        rw [h2]
        exact add_le_add h1 le_rfl


end

end Submission.Vdw
