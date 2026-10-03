/-
# `Work.FIChain.LamPlusBLayerDefs` — the `B`-delay Rosser–Iwaniec layer sums

The Rosser–Iwaniec identity for the `B`-delay upper weight `lamPlusB B D`
(`Submission/Work/FIChain/lamPlusBDefs.lean`): with the sifting range `y` (the product
`P(y) = ∏_{p < y} p`) and a multiplicative density `ν`,

    `Gp(y,D) = V(y) + ∑_{n odd} T_n(D,y)`,

where `Gp(y,D) = ∑_{d | P(y)} [rdPlusB B D d] μ(d) ν(d)`, `V(y) = ∏_{p<y}(1-ν p)` and the layer sums
`T_n` satisfy `T_0 = V(y)`, `T_{n+1}(D,y) = ∑_{p<y, cond} ν(p) T_n(D/p, p)` with
`cond = (n+1 = 1 → D < p^{B+1}) ∧ (2 ≤ n+1 → Odd (n+1) → p^{B+1} ≤ D)`.
(This is the `B = 2` framework of `Submission/Work/ChenPlan/LinearSieve/RI/`, generalised from the
exponent `3 = B+1` to a general `B ≥ 2`.)

Everything here is definitions plus the elementary vanishing lemmas; the identity itself and the
sieve bound are the obligations named below.
-/
import Mathlib
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.lamPlusB_upper_moebius

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The lower weight and the layer sums -/

/-- The `B`-delay **lower** Rosser–Iwaniec weight: `μ d` on the `rdMinusB`-admissible `d`, `0` else. -/
def lamMinusB (B : ℝ) (D : ℝ) (d : ℕ) : ℝ :=
  if rdMinusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

/-- The sifting modulus `P(y) = ∏_{p < y} p` (primes below `⌈y⌉₊`). -/
def PB (y : ℝ) : ℕ := ∏ p ∈ Nat.primesBelow ⌈y⌉₊, p

/-- The product `V(y) = ∏_{p < y} (1 - ν p)`. -/
def VfB (ν : ℕ → ℝ) (y : ℝ) : ℝ := ∏ p ∈ Nat.primesBelow ⌈y⌉₊, (1 - ν p)

/-- The `B`-delay upper divisor sum `Gp(y,D) = ∑_{d | P(y)} [rdPlusB B D d] μ(d) ν(d)`. -/
def GpB (B : ℝ) (ν : ℕ → ℝ) (y D : ℝ) : ℝ :=
  ∑ d ∈ (PB y).divisors, (if rdPlusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * ν d

/-- The `B`-delay lower divisor sum `Gm(y,D) = ∑_{d | P(y)} [rdMinusB B D d] μ(d) ν(d)`. -/
def GmB (B : ℝ) (ν : ℕ → ℝ) (y D : ℝ) : ℝ :=
  ∑ d ∈ (PB y).divisors, (if rdMinusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * ν d

/-- The Rosser–Iwaniec layer condition at step `n+1`. -/
def TcondB (B : ℝ) (n : ℕ) (D : ℝ) (p : ℕ) : Prop :=
  (n = 1 → D < (p : ℝ) ^ (B + 1)) ∧ (2 ≤ n → Odd n → (p : ℝ) ^ (B + 1) ≤ D)

/-- **The `B`-delay Rosser–Iwaniec layer sums** `T_n(D,y)`, defined by the recursion
`T_0 = V(y)`, `T_{n+1}(D,y) = ∑_{p < y, TcondB B (n+1) D p} ν(p) · T_n(D/p, p)`. -/
def TnB (B : ℝ) (ν : ℕ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, y => VfB ν y
  | (n + 1), D, y =>
      ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B (n + 1) D p),
        ν p * TnB B ν n (D / (p : ℝ)) (p : ℝ)

/-- The odd part of the layer expansion, truncated at `K`: `∑_{n < K, n odd} T_n(D,y)`. -/
def OddLayerSum (B : ℝ) (ν : ℕ → ℝ) (K : ℕ) (D y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range K).filter Odd, TnB B ν n D y

/-- A safe truncation exponent: every nonzero `T_n(D,y)` has `n ≤ Nat.log 2 ⌈D⌉₊`. -/
def layerCut (B : ℝ) (D : ℝ) : ℕ := Nat.log 2 ⌈D⌉₊ + ⌈B⌉₊ + 3

/-- **The κ-dimensional linear-sieve product normalisation** (a one-sided `Ω₂(κ)` condition):
for all `2 ≤ w ≤ z`, `∏_{w ≤ p < z} (1 - ν p)⁻¹ ≤ C · (log z / log w)^κ`.  This is the hypothesis
under which the Rosser–Iwaniec layer induction yields the Fundamental Lemma bound.  For the
Friedlander–Iwaniec density `g̃ · hSieveC g̃ (1/log Δ)` it holds with `κ = 2` and an absolute `C`
(`Work.FIChain.sharpNorm_two_FIgtil`). -/
def LinNormK (ν : ℕ → ℝ) (C κ : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹)
      ≤ C * (Real.log z / Real.log w) ^ κ

/-- The `κ`-dimensional norm restricted to windows below a fixed level `D` (all that the layer
induction over the range `y ≤ D^{1/(B+1)}` uses). -/
def LinNormKup (ν : ℕ → ℝ) (C κ D : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w ≤ z → z ≤ D →
    (∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹)
      ≤ C * (Real.log z / Real.log w) ^ κ

/-! ## Elementary facts -/

lemma VfB_nonneg {ν : ℕ → ℝ} (hν : ∀ p : ℕ, p.Prime → ν p ≤ 1) (y : ℝ) : 0 ≤ VfB ν y := by
  rw [VfB]
  refine Finset.prod_nonneg fun p hp => ?_
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  linarith [hν p hp']

lemma VfB_le_one {ν : ℕ → ℝ} (h0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p)
    (h1 : ∀ p : ℕ, p.Prime → ν p ≤ 1) (y : ℝ) : VfB ν y ≤ 1 := by
  rw [VfB]
  refine Finset.prod_le_one₀ (fun p hp => by
      have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
      linarith [h1 p hp']) fun p hp => by
      have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
      linarith [h0 p hp']

/-- `V(y) = 1` when `y ≤ 2`: there are no primes below `2`. -/
lemma VfB_eq_one_of_le_two (ν : ℕ → ℝ) {y : ℝ} (hy : y ≤ 2) : VfB ν y = 1 := by
  have hy2 : ⌈y⌉₊ ≤ 2 := Nat.ceil_le.mpr hy
  rw [VfB, Finset.prod_eq_one]
  intro p hp
  exfalso
  obtain ⟨hlt, hpr⟩ := Nat.mem_primesBelow.mp hp
  have h2 : 2 ≤ p := hpr.two_le
  omega

/-- `T_n = 0` for `n ≥ 1` when the range is too small: no primes below `y ≤ 2`. -/
lemma TnB_eq_zero_of_le_two (B : ℝ) (ν : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (D : ℝ) {y : ℝ}
    (hy : y ≤ 2) : TnB B ν n D y = 0 := by
  have hy2 : ⌈y⌉₊ ≤ 2 := Nat.ceil_le.mpr hy
  match n with
  | 0 => omega
  | (k+1) =>
    rw [TnB]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpb, _⟩ := hp
    obtain ⟨hlt, hpr⟩ := Nat.mem_primesBelow.mp hpb
    have h2 : 2 ≤ p := hpr.two_le
    omega

end

end Work.FIChain
