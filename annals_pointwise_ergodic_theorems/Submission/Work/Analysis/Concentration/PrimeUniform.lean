/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.Improving

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The concentration estimates on prime powers; uniformity in the prime

Appendix C of Krause–Mirek–Tao proves its concentration estimate (Corollary `cor:1`) for
`Q = p^j` a *prime power*, and the constant there is of the form
`C_s(P) = C_s · max(1, |a_d|^{1/(d-1)})` with `a_d` the leading coefficient of `P`: in particular
it is bounded uniformly over all primes `p` (for `p ∤ a_d` the p-adic norm `|a_d|` is `1`, and for
the finitely many primes dividing `a_d` it is bounded by a function of `P` alone).  This
"uniformity in the prime" is what makes the tensor-product factorisation of the arithmetic
averages `A_{∏_{p ∈ S} ℤ_p}` of Section 10 work.

We record

* the *elementary* prime-power bounds `fiberMaxBound_prime_pow`, `fiberLpBound_prime_pow`,
  `polyImproving_prime_pow` (obtained by lifting the prime case `fiber_card_le_prime` through
  `fiber_card_prime_pow_le`); these are uniform in the prime but very lossy in `j`;
* the sharp statement `Corollary1` (and its weak-type form `Corollary1WeakType`), as
  `Prop`-valued definitions: this is the Appendix C input quoted in Section 10, with a constant
  independent of the prime power.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory

noncomputable section

/-- **Elementary prime-power fibre bound** (uniform in the prime): for `p` prime and `P` of
degree `d ≥ 1` modulo `p`, every fibre of `P` modulo `p^j` has at most `d p^{j-1}` elements. -/
theorem fiberMaxBound_prime_pow (P : Polynomial ℤ) {p d j : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) (hj : 1 ≤ j) :
    FiberMaxBound P (p ^ j) ((d : ℝ) * (p : ℝ) ^ (j - 1)) := by
  intro y
  have h1 : polyFiberCard P (p ^ j) y ≤ p ^ (j - 1) * polyFiberCard P p
      (ZMod.castHom (by simpa using pow_dvd_pow p hj) (ZMod p) y) :=
    fiber_card_prime_pow_le P hj y
  have h2 : polyFiberCard P p
      (ZMod.castHom (by simpa using pow_dvd_pow p hj) (ZMod p) y) ≤ d :=
    fiber_card_le_prime P hd hdeg _
  have h3 : polyFiberCard P (p ^ j) y ≤ p ^ (j - 1) * d :=
    le_trans h1 (Nat.mul_le_mul_left _ h2)
  calc (polyFiberCard P (p ^ j) y : ℝ) ≤ ((p ^ (j - 1) * d : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (d : ℝ) * (p : ℝ) ^ (j - 1) := by push_cast; ring

/-- **Elementary `L^s` concentration bound at a prime power**, from the maximal-fibre bound. -/
theorem fiberLpBound_prime_pow (P : Polynomial ℤ) {p d j : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) (hj : 1 ≤ j) {s : ℝ} (hs : 1 ≤ s) :
    FiberLpBound P (p ^ j) s (((d : ℝ) * (p : ℝ) ^ (j - 1)) ^ (1 - 1 / s)) :=
  fiberLpBound_of_fiberMaxBound (fiberMaxBound_prime_pow P hd hdeg hj) hs

/-- **Elementary `ℓ^q → ℓ^{q'}` improving estimate at a prime power**, uniform in the prime. -/
theorem polyImproving_prime_pow (P : Polynomial ℤ) {p d j : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) (hj : 1 ≤ j) {q q' : ℝ} (hq : 1 ≤ q)
    (hqq' : q ≤ q') :
    PolyImprovingZMod P (p ^ j) q q' (((d : ℝ) * (p : ℝ) ^ (j - 1)) ^ (1 / q - 1 / q')) :=
  polyImproving_of_fiberMaxBound (fiberMaxBound_prime_pow P hd hdeg hj) hq hqq'

/-! ## The sharp Appendix C input -/

/-- **Appendix C, Corollary `cor:1` (concentration on prime powers, uniformly in the prime).**

For a polynomial `P ∈ ℤ[X]` of degree `d ≥ 2`, every `s < d/(d-1)` comes with a constant `C > 0`,
depending only on `P` and `s` — in particular *not* on the prime `p` nor on the exponent `j` —
such that the fibre counting function of `P` modulo `p^j` satisfies `∑_y h(y)^s ≤ C^s p^j`

This is the estimate quoted in Section 10 of the paper (it is `‖h‖_{L^s(ℤ/p^jℤ)} ≲_{s,P} 1` of
Corollary `cor:1`); the constant is `C_s · max(1, |a_d|^{1/(d-1)})` in the notation of the
proof, which is bounded independently of `p`. -/
def Corollary1 (P : Polynomial ℤ) (d : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < (d : ℝ) / ((d : ℝ) - 1) → ∃ C : ℝ, 0 < C ∧
    ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j → FiberLpBound P (p ^ j) s C

/-- **Appendix C, Corollary `cor:1`, weak-type form.**

For a polynomial `P` of degree `d ≥ 2` there is a constant `C > 0`, depending only on `P`, such
that for every prime `p` and every `j ≥ 1` the fibre counting function satisfies
`#{y : h(y) ≥ t} ≤ C t^{-d/(d-1)} p^j` for all `t > 0`. -/
def Corollary1WeakType (P : Polynomial ℤ) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
    FiberWeakType P (p ^ j) (d : ℝ) C

/-- The prime-uniform form of `Corollary1`, with the constant exhibited as a function of `s`. -/
def Corollary1UniformInPrime (P : Polynomial ℤ) (d : ℕ) (C : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < (d : ℝ) / ((d : ℝ) - 1) → 0 < C s ∧
    ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j → FiberLpBound P (p ^ j) s (C s)

/-- **Reduction of the `ℓ^p`-improving estimates on prime powers to Appendix C.**  If the
concentration estimate `Corollary1` holds, then for exponents `1 ≤ q ≤ q'` related to `s` by
`1/s = 1 + 1/q' - 1/q`, the polynomial averaging operator on `ℤ/p^jℤ` improves `ℓ^q → ℓ^{q'}`
with a constant *depending only on `P` and on the exponents*, uniformly in the prime `p` and the
exponent `j`.  This is the step that Section 10 takes from Appendix C to the arithmetic
(`p₁ = p₂ = 2`) case of the main theorem. -/
theorem polyImproving_prime_pow_of_corollary1 {P : Polynomial ℤ} {d : ℕ}
    (h : Corollary1 P d) {s q q' : ℝ} (hs : 1 ≤ s) (hsd : s < (d : ℝ) / ((d : ℝ) - 1))
    (hr : 1 / s = 1 + 1 / q' - 1 / q) (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    ∃ C : ℝ, 0 < C ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
      PolyImprovingZMod P (p ^ j) q q' C := by
  obtain ⟨C, hC, hCb⟩ := h s (by linarith) hsd
  refine ⟨C, hC, fun p j _ hj => ?_⟩
  refine polyImproving_of_fiberLpBound (r := s) (C := C) (p := q) (p' := q')
    hs (le_of_lt hC) (hCb p j hj) hq hq' hr

/-- `Corollary1` follows from its prime-uniform form with an explicit constant. -/
theorem corollary1_of_uniformInPrime {P : Polynomial ℤ} {d : ℕ} {C : ℝ → ℝ}
    (h : Corollary1UniformInPrime P d C) : Corollary1 P d :=
  fun s hs hs' => ⟨C s, (h s hs hs').1, fun p j _ hj => (h s hs hs').2 p j hj⟩

end

end Work.Analysis.Concentration
