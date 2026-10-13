import Mathlib
import Submission.Work.DSEQP.Basic

namespace Work.DSEQP

set_option linter.unusedVariables false

/-- **Krull's descent lemma.**  Let `A` be a Noetherian local domain, `I` an ideal contained in
the maximal ideal, `0 ≠ a ∈ I`, and `S` a faithfully flat `A`-algebra.  Then `a` cannot acquire
`p^e`-th roots *inside* `I S` for every `e ≥ 0`.

The mathematical content is a two-line argument.  Since `t ∈ I·S` with `t^(p^e) = a` gives
`a ∈ (I·S)^(p^e) = I^(p^e)·S`, and contraction along the faithfully flat map `A → S` is exact on
ideals (`Ideal.comap_map_eq_self_of_faithfullyFlat`), we get `a ∈ I^(p^e)` for every `e`.
As `p^e ≥ n` for large `e`, this shows `a ∈ ⋂ n, I^n`, which is `⊥` by Krull's intersection
theorem in the Noetherian local ring `A`.  Hence `a = 0`, contradicting `a ≠ 0`. -/
theorem krull_descent (A S : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S] (p : ℕ)
    [Fact p.Prime] (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) {a : A} (ha : a ∈ I)
    (ha0 : a ≠ 0)
    (h : ∀ e : ℕ, ∃ t : S, t ∈ I.map (algebraMap A S) ∧ t ^ (p ^ e) = algebraMap A S a) :
    False := by
  -- Step 1: the `p^e`-th root of `a` lying in `I · S` forces `a ∈ I^(p^e)`.
  have key : ∀ e : ℕ, a ∈ I ^ (p ^ e) := by
    intro e
    obtain ⟨t, ht, htpow⟩ := h e
    have h1 : algebraMap A S a ∈ Ideal.map (algebraMap A S) (I ^ (p ^ e)) := by
      rw [Ideal.map_pow]
      rw [← htpow]
      exact Ideal.pow_mem_pow ht (p ^ e)
    have h2 : a ∈ Ideal.comap (algebraMap A S) (Ideal.map (algebraMap A S) (I ^ (p ^ e))) := h1
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat (I ^ (p ^ e))] at h2
  -- Step 2: hence `a` lies in every power of `I`, so in `⋂ n, I^n = ⊥` by Krull.
  have hmem : a ∈ ⨅ i : ℕ, I ^ i := by
    rw [Ideal.mem_iInf]
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hlt : n < p ^ n := Nat.lt_pow_self (n := n) (a := p) (Fact.out : p.Prime).one_lt
      exact Ideal.pow_le_pow_right hlt.le (key n)
  have hbot : (⨅ i : ℕ, I ^ i : Ideal A) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing I
      (fun htop => (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (htop ▸ hI)))
  rw [hbot] at hmem
  exact ha0 (by simpa using hmem)

end Work.DSEQP
