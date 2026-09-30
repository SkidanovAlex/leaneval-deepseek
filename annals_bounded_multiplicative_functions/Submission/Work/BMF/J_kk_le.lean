import Mathlib
import Submission.Vinogradov.ChallengeDeps
import Submission.Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open LeanEval.NumberTheory.VinogradovMeanValue

/-- **The base case of the iteration**: `J_{k,k}(Q) ≤ k!·Q^k`, valid for every `k, Q : ℕ` (Wooley's "stemming from Newton's formulae"). Route: `J k k Q = Σ_c (N_c)²` where `c` runs over the classes of the equivalence relation "same power sums of degrees `1..k`" and `N_c` is the number of `x ∈ [1,Q]^k` in class `c`; the power sums of degrees `1..k` determine the **multiset** `{x_1,…,x_k}` (Newton's identities / `MvPolynomial.mul_esymm_eq_sum`, or `Multiset.esymm`), so each class consists of the permutations of a fixed multiset and hence has `N_c ≤ k!` elements; therefore `Σ_c (N_c)² ≤ k!·Σ_c N_c = k!·Q^k`. The module `Submission.Work.BMF.vmvt_setup` imports `Submission.Vinogradov.ChallengeDeps`, which defines `LeanEval.NumberTheory.VinogradovMeanValue.J`. -/
theorem J_kk_le (k Q : ℕ) :
    LeanEval.NumberTheory.VinogradovMeanValue.J k k Q ≤ ((k.factorial : ℕ) : ℝ) * (Q : ℝ)^k := by
  classical
  have hJ : LeanEval.NumberTheory.VinogradovMeanValue.J k k Q
      = (((Finset.univ : Finset ((Fin k → Finset.Icc 1 Q) × (Fin k → Finset.Icc 1 Q))).filter
          (fun p => ∀ j ≤ k, ∑ i, (p.1 i).1 ^ j = ∑ i, (p.2 i).1 ^ j)).card : ℝ) := rfl
  rw [hJ]
  set s : Finset ((Fin k → Finset.Icc 1 Q) × (Fin k → Finset.Icc 1 Q)) :=
    (Finset.univ : Finset ((Fin k → Finset.Icc 1 Q) × (Fin k → Finset.Icc 1 Q))).filter
          (fun p => ∀ j ≤ k, ∑ i, (p.1 i).1 ^ j = ∑ i, (p.2 i).1 ^ j) with hs
  have hmain : s.card ≤ Q^k * k.factorial := by
    -- The Newton's-identities input: matching power sums force `p.2` to be a permutation of `p.1`.
    have hex : ∀ p : (Fin k → Finset.Icc 1 Q) × (Fin k → Finset.Icc 1 Q), p ∈ s →
        ∃ σ : Equiv.Perm (Fin k), p.2 = p.1 ∘ σ := by
      intro p hp
      have hpP : ∀ j ≤ k, ∑ i, (p.1 i).1 ^ j = ∑ i, (p.2 i).1 ^ j := by
        rw [hs] at hp
        exact (Finset.mem_filter.mp hp).2
      obtain ⟨σ, hσ⟩ := Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq k
        (fun i => (p.1 i).1) (fun i => (p.2 i).1) hpP
      exact ⟨σ, by funext i; exact Subtype.ext (hσ i)⟩
    have hinj : Function.Injective
        (fun q : ↥s => (q.1.1, Classical.choose (hex q.1 q.2))) := by
      intro q q' hq
      have h1 : q.1.1 = q'.1.1 := by simpa using congrArg Prod.fst hq
      have h2 : Classical.choose (hex q.1 q.2) = Classical.choose (hex q'.1 q'.2) := by
        simpa using congrArg Prod.snd hq
      have hc := Classical.choose_spec (hex q.1 q.2)
      have hc' := Classical.choose_spec (hex q'.1 q'.2)
      apply Subtype.ext
      apply Prod.ext
      · exact h1
      · calc q.1.2 = q.1.1 ∘ ⇑(Classical.choose (hex q.1 q.2)) := hc
          _ = q'.1.1 ∘ ⇑(Classical.choose (hex q'.1 q'.2)) := by rw [h2, h1]
          _ = q'.1.2 := hc'.symm
    have hcard := Fintype.card_le_of_injective
      (fun q : ↥s => (q.1.1, Classical.choose (hex q.1 q.2))) hinj
    rw [Fintype.card_coe] at hcard
    have hS : Fintype.card (Fin k → Finset.Icc 1 Q) = Q^k := by
      rw [Fintype.card_fun]
      congr 1
      · rw [Fintype.card_coe, Nat.card_Icc]; simp
      · simp
    refine le_trans hcard ?_
    rw [Fintype.card_prod, hS, Fintype.card_perm, Fintype.card_fin]
  calc (s.card : ℝ) ≤ ((Q^k * k.factorial : ℕ) : ℝ) := by exact_mod_cast hmain
    _ = (k.factorial : ℝ) * (Q : ℝ)^k := by push_cast; ring

end Work.BMF
