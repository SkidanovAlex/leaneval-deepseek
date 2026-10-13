import Submission.Work.DSM7p.Basic

/-!
# DSM7p — Krull input for the M7p assembly

The two number-theoretic/Krull inputs of the model-level Bhatt §4 assembly (`area_M7p`):

* `exists_pow_notMem`: for a proper ideal `J` of a Noetherian local ring and a nonzero element `x`,
  some power of `J` misses `x` (Krull's intersection result, Mathlib's
  `Ideal.iInf_pow_eq_bot_of_isLocalRing`);
* `exists_pow_notMem_two_mul_le`: the same with the exponent normalised so that `2 * K ≤ p ^ K`,
  which is what `Work.DSM7p.exists_mul_pow_eq` (the `p`-power/root computation) consumes.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory IsLocalRing

namespace Work.DSM7p

universe a

/-- Small arithmetic: `2 * n ≤ 2 ^ n` for `1 ≤ n`. -/
lemma two_mul_le_two_pow : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ 2 ^ n
  | 0, h => absurd h (by omega)
  | 1, _ => by norm_num
  | (n + 2), _ => by
      have ih : 2 * (n + 1) ≤ 2 ^ (n + 1) := two_mul_le_two_pow (n + 1) (by omega)
      have h2 : (2 : ℕ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n + 1) := by apply Nat.pow_le_pow_right <;> omega
      calc 2 * (n + 2) = 2 * (n + 1) + 2 := by ring
        _ ≤ 2 ^ (n + 1) + 2 := by omega
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 2) := by ring

/-- Krull: for a proper ideal of a Noetherian local ring and a nonzero element, some power of the
ideal misses the element. -/
lemma exists_pow_notMem {A : Type a} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ≠ ⊤) {x : A} (hx : x ≠ 0) : ∃ K : ℕ, x ∉ J ^ K := by
  by_contra h
  push_neg at h
  have hmem : x ∈ ⨅ k, J ^ k := Ideal.mem_iInf.mpr h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing J hJ] at hmem
  exact hx hmem

/-- Krull, upgraded so that the exponent also satisfies `2 * K ≤ p ^ K` (needed to convert the
almost-value `(Q.ϖ K)^3 * (gr K)^2` into `algebraMap (p^2 * g)`). -/
lemma exists_pow_notMem_two_mul_le {A : Type a} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ≠ ⊤) (p : ℕ) (hp : 2 ≤ p) {x : A} (hx : x ≠ 0) :
    ∃ K : ℕ, x ∉ J ^ K ∧ 2 * K ≤ p ^ K := by
  obtain ⟨K₀, hK₀⟩ := exists_pow_notMem J hJ hx
  refine ⟨K₀ + p, fun hmem => hK₀ (Ideal.pow_le_pow_right (Nat.le_add_right K₀ p) hmem), ?_⟩
  have h1 : 1 ≤ K₀ + p := by omega
  calc 2 * (K₀ + p) ≤ 2 ^ (K₀ + p) := two_mul_le_two_pow _ h1
    _ ≤ p ^ (K₀ + p) := by
        apply Nat.pow_le_pow_left
        omega

end Work.DSM7p
