/-
# Auxiliary arithmetic weights for the boundary sum of `B_z`

This file fixes the numerical objects used by the boundary (lower cut-off) piece `bzBC` of the
hard-range second moment of `B_z(n) = Λ_z(n) − Λ(n)`.

For `2 ≤ z ≤ N < z*z` the exact reindexing writes the boundary piece as

`bzBC z N = Σ_{q ≤ N/z} Σ_{r,t ≤ N/(qz)} [r⊥t]μ(r)μ(t)·C_{rt}·max(⌊z/t⌋,⌊z/r⌋)·W(z,r,t)`

with `C_c = ζ(2)^{-1}∏_{p ∣ c}p/(p+1)` the density of the squarefree integers coprime to `c`, and
`W(z,r,t) = (log(max(⌊z/t⌋,⌊z/r⌋)·t/z) − 1)(log(max(⌊z/t⌋,⌊z/r⌋)·r/z) − 1) + 1`.

Writing `max(⌊z/t⌋,⌊z/r⌋)` as `⌊max(z/t, z/r)⌋ = ⌊z/min(r,t)⌋`, the dominant contribution comes from
the terms with `min(r,t) = t`, where `⌊z/t⌋·W ≈ (z/t)(2 − log(r/t))`; the whole sum is then
controlled by the `t`-sum

`S(r) = Σ_{t ≤ r, (t,r)=1} (μ(t)/κ(t))·(log(r/t) − 2)  =  ζ(2)·κ(r)/r + error`

(`κ(n) = n∏_{p ∣ n}(1+1/p)`, `ζ(2)L11/L12` of Graham 1978 / An arXiv:2206.10104), and the outer
`μ(r)`-weighted sum is evaluated with the Mertens function.

The definitions below are the vocabulary of the separately proved analytic lemmas
`kappaLogSum`, `kappaSum`, `kappaTwistedG10`, `kappaSwEval` and the elementary bound
`mertensMuBound`.
-/
import Mathlib

namespace Work.ZeroDensity.Jutila

noncomputable section

/-- `κ(n) = n·∏_{p ∣ n}(1 + 1/p)` (Graham 1978, An arXiv:2206.10104 §2). -/
def kappa (n : ℕ) : ℝ := (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))

/-- `pfac(n) = ∏_{p ∣ n} p/(p+1) = n/κ(n)`. -/
def pfac (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- `σ_{-1/2}(n) = Σ_{d ∣ n} d^{-1/2}`. -/
def sigHalf (n : ℕ) : ℝ := ∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)

/-- `f/φ(f) = ∏_{p ∣ f} p/(p−1)` for squarefree `f`. -/
def dFac (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)

/-- `ζ(2) = π²/6`. -/
def zeta2 : ℝ := Real.pi ^ 2 / 6

/-- The Möbius weight `g(n) = μ(n)·∏_{p ∣ n}p/(p+1)`. -/
def gg (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) * pfac n

/-- The `t`-sum of the boundary computation at the cut-off `r`:
`S(r) = Σ_{t ≤ r, (t,r)=1}(μ(t)/κ(t))·(log(r/t) − 2)`. -/
def Sw (r : ℕ) : ℝ := ∑ t ∈ Finset.Icc 1 r,
  (if Nat.Coprime t r then (ArithmeticFunction.moebius t : ℝ) / kappa t else 0)
    * (Real.log ((r : ℝ) / (t : ℝ)) - 2)

/-! ## Elementary structural lemmas -/

lemma zeta2_pos : 0 < zeta2 := by
  unfold zeta2; positivity

lemma kappa_pos {n : ℕ} (hn : n ≠ 0) : 0 < kappa n := by
  unfold kappa
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2 : 0 < ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    positivity
  exact mul_pos h1 h2

lemma pfac_nonneg (n : ℕ) : 0 ≤ pfac n := by
  unfold pfac
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  positivity

lemma pfac_pos (n : ℕ) : 0 < pfac n := by
  unfold pfac
  apply Finset.prod_pos
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  positivity

lemma pfac_le_one (n : ℕ) : pfac n ≤ 1 := by
  unfold pfac
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    positivity
  · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    rw [div_le_one (by positivity)]
    linarith

/-- `pfac n · κ n = n`. -/
lemma pfac_mul_kappa {n : ℕ} (hn : n ≠ 0) : pfac n * kappa n = (n : ℝ) := by
  unfold pfac kappa
  have key : (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
      * (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    field_simp
  calc (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
        * ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
      = (n : ℝ) * ((∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
          * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) := by ring
    _ = (n : ℝ) * 1 := by rw [key]
    _ = (n : ℝ) := by ring

/-- `pfac` is multiplicative on coprime nonzero arguments. -/
lemma pfac_mul_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    pfac (a * b) = pfac a * pfac b := by
  unfold pfac
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

lemma sigHalf_nonneg (n : ℕ) : 0 ≤ sigHalf n := by
  unfold sigHalf
  apply Finset.sum_nonneg
  intro d hd
  positivity

lemma sigHalf_one : sigHalf 1 = 1 := by
  unfold sigHalf
  simp

end

end Work.ZeroDensity.Jutila
