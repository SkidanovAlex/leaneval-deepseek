import Mathlib
import Submission.Work.BMF.liouville.prime_power_twist_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Every prime power `n` that is not itself prime is of the form `p ^ k` with `p` prime and
`2 ≤ k`. -/
lemma exists_prime_pow_of_isPrimePow_not_prime (n : ℕ) (hn : IsPrimePow n) (h : ¬ n.Prime) :
    ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hn
  have hk1 : k ≠ 1 := by
    intro hk1
    apply h
    rw [← hpk, hk1]
    simpa using hp
  exact ⟨p, k, hp, by omega, hpk.symm⟩

/-- A prime power `p ^ k` bounded by `M`, with `p` prime and `2 ≤ k`, has both its base and its
exponent in `[2, M]`. -/
lemma prime_pow_mem_Icc {p k M : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) (hM : p ^ k ≤ M) :
    p ∈ Finset.Icc 2 M ∧ k ∈ Finset.Icc 2 M := by
  rw [Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨hp.two_le, ?_⟩, ⟨hk, ?_⟩⟩
  · calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
      _ ≤ M := hM
  · calc k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
      _ ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ ≤ M := hM

/-- A choice, for every `n` that can be written as `p ^ k` with `p` prime and `2 ≤ k`, of such a
pair `(p, k)`; arbitrary otherwise. -/
noncomputable def powRep (n : ℕ) : ℕ × ℕ := by
  classical
  exact if h : ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k then
    (h.choose, h.choose_spec.choose) else (0, 0)

/-- Specification of the chosen representation `powRep n`. -/
lemma powRep_spec {n : ℕ} (h : ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k) :
    Nat.Prime (powRep n).1 ∧ 2 ≤ (powRep n).2 ∧ n = (powRep n).1 ^ (powRep n).2 := by
  have hdef : powRep n = (h.choose, h.choose_spec.choose) := by
    unfold powRep
    exact dite_eq_left h
  rw [hdef]
  exact ⟨h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2.1,
    h.choose_spec.choose_spec.2.2⟩

/-- The sum of `F` over the non-prime prime powers in `[N, M]` is dominated by the sum of `F`
over *all* pairs `(p, k)` with `p` and `k` in `[2, M]`, evaluated at `p ^ k`. -/
theorem sum_prime_pow_le_rect_sum (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (N M : ℕ) :
    ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), F n
      ≤ ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, F (p ^ k) := by
  classical
  set S : Finset ℕ := (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
  have hmem : ∀ n ∈ S, ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k := by
    intro n hn
    obtain ⟨_, hpred⟩ := Finset.mem_filter.mp hn
    exact exists_prime_pow_of_isPrimePow_not_prime n hpred.1 hpred.2
  have hinj : Set.InjOn powRep ↑S := by
    intro a ha b hb heq
    have sa := powRep_spec (hmem a ha)
    have sb := powRep_spec (hmem b hb)
    rw [sa.2.2, sb.2.2, heq]
  have hsub : S.image powRep ⊆ (Finset.Icc 2 M).product (Finset.Icc 2 M) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    obtain ⟨hxIcc, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hMe⟩ := Finset.mem_Icc.mp hxIcc
    have spec := powRep_spec (hmem x hx)
    exact Finset.mem_product.mpr (prime_pow_mem_Icc spec.1 spec.2.1 (spec.2.2 ▸ hMe))
  calc ∑ n ∈ S, F n
      = ∑ n ∈ S, F ((powRep n).1 ^ (powRep n).2) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg F (powRep_spec (hmem n hn)).2.2
    _ = ∑ q ∈ S.image powRep, F (q.1 ^ q.2) :=
        (Finset.sum_image (f := fun q => F (q.1 ^ q.2)) hinj).symm
    _ ≤ ∑ q ∈ (Finset.Icc 2 M).product (Finset.Icc 2 M), F (q.1 ^ q.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hF _)
    _ = ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, F (p ^ k) :=
        Finset.sum_product _ _ _

end Work.BMF.liouville
