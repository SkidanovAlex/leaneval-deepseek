import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.galMapPow_eq_add_nsmul

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-! ## Auxiliary group-theoretic facts

The two halves of the coboundary criterion are pure facts about an additive commutative group `G`
with an endomorphism `σ`, an element `x` fixed by `σ` with `5 • x = 0`, and `k ≢ 0 (mod 5)`.  We
prove them here in that generality, so that the criterion below is a two-line assembly. -/

section General

variable {G : Type*} [AddCommGroup G]

/-- **The telescoping identity `σ ^ k - 1 = (σ - 1)(1 + σ + ⋯ + σ ^ (k-1))`.**  The
`(σ ^ k - 1)`-coboundary `σ^k R - R` is already a `(σ - 1)`-coboundary: it is the shift of the
partial orbit sum `∑_{i<k} σ^i R`.  No hypothesis on `x` is needed. -/
private lemma exists_shift_eq_iterate_sub (σ : G →+ G) (R : G) (k : ℕ) :
    ∃ S : G, σ S - S = (σ^[k]) R - R := by
  refine ⟨Finset.sum (Finset.range k) (fun i => (σ^[i]) R), ?_⟩
  have h1 : σ (Finset.sum (Finset.range k) (fun i => (σ^[i]) R))
      = Finset.sum (Finset.range k) (fun i => (σ^[i + 1]) R) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Function.iterate_succ_apply']
  rw [h1, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (σ^[i]) R) k]
  simp

/-- An inverse of `k` modulo `5`, for `k` not divisible by `5`, given by the table
`1 ↦ 1, 2 ↦ 3, 3 ↦ 2, 4 ↦ 4` on the non-zero residues (`k * k³ ≡ 1` would do as well). -/
private lemma exists_mul_mod_five (k : ℕ) (hk : k % 5 ≠ 0) : ∃ m : ℕ, (m * k) % 5 = 1 := by
  have h : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
    have := Nat.mod_lt k (by norm_num : 0 < 5)
    omega
  rcases h with h | h | h | h
  · exact ⟨1, by rw [one_mul, h]⟩
  · exact ⟨3, by rw [Nat.mul_mod, h]⟩
  · exact ⟨2, by rw [Nat.mul_mod, h]⟩
  · exact ⟨4, by rw [Nat.mul_mod, h]⟩

/-- Exponents of a `5`-torsion element only matter modulo `5`. -/
private lemma nsmul_eq_of_mod_five {x : G} (h5 : (5 : ℕ) • x = 0) {a b : ℕ}
    (h : a % 5 = b % 5) : a • x = b • x := by
  rw [nsmul_eq_mod_nsmul a h5, nsmul_eq_mod_nsmul b h5, h]

end General

/-- **The coboundary criterion does not depend on the chosen generator of the Galois group.**
For a `σ`-invariant `x` with `5 • x = 0` (in the applications `x = P`, or `x = n • P`) and `k`
coprime to `5`, `x` is a `(σ - 1)`-coboundary in `E(L)` if and only if it is a
`(σ ^ k - 1)`-coboundary.  Here `QuinticTwist.galMapPow D k` is the action of `σ ^ k`
(`Submission/Work/Twist/Defs.lean`).

Direction `⟹` is the telescoping identity `σ ^ k - 1 = (σ - 1)(1 + σ + … + σ ^ (k-1))`, which
needs no hypothesis.  Direction `⟸` uses the orbit identity `σ ^ k R = R + k • x`
(`galMapPow_eq_add_nsmul`, in `Submission/Work/Twist/galMapPow_eq_add_nsmul.lean`) and
multiplies by an inverse of `k` modulo `5` (which exists as `k % 5 ≠ 0`; `k * (k^3) ≡ 1` by
Fermat, so `k * k^3` works). -/
theorem exists_shift_pow_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (x : D.LPoints) (hfix : D.galMap x = x)
    (h5 : (5 : ℕ) • x = 0) {k : ℕ} (hk : k % 5 ≠ 0) :
    (∃ R : D.LPoints, QuinticTwist.galMapPow D k R - R = x) ↔
      (∃ R : D.LPoints, D.galMap R - R = x) := by
  constructor
  · -- `⟹`: a `(σ ^ k - 1)`-coboundary is a `(σ - 1)`-coboundary, by telescoping.
    rintro ⟨R, hR⟩
    obtain ⟨S, hS⟩ := exists_shift_eq_iterate_sub D.galMap R k
    rw [← QuinticTwist.galMapPow_apply D k R] at hS
    exact ⟨S, hS.trans hR⟩
  · -- `⟸`: given `σ R = R + x`, the orbit identity reads `σ ^ k R = R + k • x`, so multiplying
    -- `R` by the inverse of `k` modulo `5` makes `σ ^ k - 1` hit `x`.
    rintro ⟨R, hR⟩
    obtain ⟨m, hm⟩ := exists_mul_mod_five k hk
    refine ⟨(m : ℕ) • R, ?_⟩
    have horbit : QuinticTwist.galMapPow D k R = R + (k : ℕ) • x :=
      galMapPow_eq_add_nsmul D hfix hR k
    have hmap : QuinticTwist.galMapPow D k ((m : ℕ) • R)
        = (m : ℕ) • QuinticTwist.galMapPow D k R :=
      map_nsmul _ m R
    rw [hmap, horbit, nsmul_add]
    have hmul : (m : ℕ) • ((k : ℕ) • x) = (m * k) • x := by
      rw [← mul_nsmul x k m, Nat.mul_comm]
    rw [hmul]
    have hx : (m * k) • x = x := by
      have h := nsmul_eq_of_mod_five (x := x) h5 (a := m * k) (b := 1) (by rw [hm])
      simpa using h
    rw [hx, add_sub_cancel_left]

end Work.Twist
