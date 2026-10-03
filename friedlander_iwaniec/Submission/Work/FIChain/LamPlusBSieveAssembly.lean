/-
# `Work.FIChain.LamPlusBSieveAssembly` — reduction of `lamPlusB 19` to its layers

The assembly of the target `Work.FIChain.lamPlusB_FIgtil_sieve`:

* `lamPlusB_support` — the support of the `B`-delay weight: every prime factor `p` of an admissible
  `d` satisfies `p^{B+1} ≤ D`; consequently the admissible `d` divide `∏_{p < y20 Δ} p` and the
  Finset sum over `ν ∈ [1,Δ]` is the divisor sum `GpB`;
* `VfB_le_prod_mul`, `VfB_y20_le_prod` — the product at the layer range `y20 Δ = ⌈Δ^{1/20}⌉₊+1`
  is dominated (by the windowed `Ω_κ` norm) by the product at the target's range `⌈Δ^{1/19}⌉₊`;
* the instantiation of the layer-bound hypotheses for `ν_Δ = g̃·hSieveC g̃ (1/log Δ)`.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.GpB_eq_VfB_add_oddLayers
import Submission.Work.FIChain.Defs
import Submission.ASP.S27
import Submission.Work.FIChain.sharpNorm_two_FIgtil

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `B`-delay **support**: every prime factor `p` of an admissible `d` has `p^{B+1} ≤ D`. -/
lemma lamPlusB_support {B D : ℝ} {d : ℕ} (hd : lamPlusB B D d ≠ 0) :
    ∀ p ∈ d.primeFactors, (p : ℝ) ^ (B + 1) ≤ D := by
  have hrd : rdPlusB B D d := by
    by_contra h
    rw [lamPlusB, if_neg h] at hd
    exact hd rfl
  intro p hp
  obtain ⟨hpp, hpdiv, hd0⟩ := Nat.mem_primeFactors.mp hp
  have hpd : p ∈ d.divisors := Nat.mem_divisors.mpr ⟨hpdiv, hd0⟩
  have hodd : Odd p.primeFactors.card := by
    rw [hpp.primeFactors, Finset.card_singleton]; exact odd_one
  have h := hrd p hpd hodd
  rw [hpp.minFac_eq] at h
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hcomm : (p : ℝ) ^ B * (p : ℝ) = (p : ℝ) * (p : ℝ) ^ B := mul_comm _ _
  calc (p : ℝ) ^ (B + 1) = (p : ℝ) ^ B * (p : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add hp0]
    _ = (p : ℝ) ^ B * (p : ℝ) := by rw [Real.rpow_one]
    _ = (p : ℝ) * (p : ℝ) ^ B := hcomm
    _ ≤ D := h

lemma lamPlusB_squarefree_of_ne_zero {B D : ℝ} {d : ℕ} (hd : lamPlusB B D d ≠ 0) :
    Squarefree d := by
  by_contra h
  exact hd (lamPlusB_squarefree B D d h)

/-- The range used for the layer expansion: one more than `⌈Δ^{1/20}⌉₊`, so that all primes with
`p^{20} ≤ Δ` are below it. -/
def y20 (Δ : ℕ) : ℕ := ⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ + 1

/-- The sieve density `ν_Δ = g̃ · hSieveC g̃ (1/log Δ)`. -/
def nuD (Δ : ℕ) : ℕ → ℝ :=
  fun n => Submission.ASP.FIgtil n * hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) n

lemma PB_ne_zero_y20 (Δ : ℕ) : PB (y20 Δ) ≠ 0 := by
  rw [PB, Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.mem_primesBelow.mp hp).2.ne_zero

/-- The primes of the range `y20 Δ` contain every prime `p` with `p^{20} ≤ Δ`. -/
lemma prime_mem_PB_y20 {Δ : ℕ} {p : ℕ} (hp : p.Prime) (h : (p : ℝ) ^ (20 : ℕ) ≤ (Δ : ℝ)) :
    p ∈ Nat.primesBelow (y20 Δ) := by
  rw [Nat.mem_primesBelow]
  refine ⟨?_, hp⟩
  have h1 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h3 : ((p : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) = (p : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h1)]
    norm_num
  have h2 : (p : ℝ) ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) := by
    calc (p : ℝ) = ((p : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) := h3.symm
      _ ≤ (Δ : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h4 : (Δ : ℝ) ^ ((1 : ℝ) / 20) < (y20 Δ : ℝ) := by
    have h5 : (Δ : ℝ) ^ ((1 : ℝ) / 20) < (⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil ((Δ : ℝ) ^ ((1 : ℝ) / 20))
      linarith
    simpa [y20] using h5
  have : (p : ℝ) < (y20 Δ : ℝ) := lt_of_le_of_lt h2 h4
  exact_mod_cast this

end

end Work.FIChain
