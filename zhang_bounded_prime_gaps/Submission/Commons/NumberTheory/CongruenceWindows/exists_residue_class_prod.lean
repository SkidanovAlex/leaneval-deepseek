import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.Order.Ring.Nat
import Submission.Commons.NumberTheory.CongruenceWindows.modEq_prod_iff_forall

namespace Commons.NumberTheory.CongruenceWindows

open scoped BigOperators

/-- **CRT residue-class identification.**  For a finite family of pairwise coprime
nonzero moduli `s i` and residues `a i`, the system `n ≡ a i (mod s i)` is equivalent
to a single congruence `n ≡ r (mod ∏ i, s i)` for a suitable `r < ∏ i, s i`.

This is the "CRT output" used by the sieve: it converts the congruence system
`n ≡ b (W)`, `n + H i ≡ 0 (mod m i)` into a single residue class modulo
`W · ∏ i, m i`, which is what the θ-weighted prime sum (Polymath8a (45)) is taken
over.  Provable from `Nat.chineseRemainderOfFinset`, or directly from
`Commons.NumberTheory.CongruenceWindows.modEq_prod_iff_forall` plus the existence
half of the CRT. -/
theorem exists_residue_class_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s a : ι → ℕ) (hs : ∀ i, s i ≠ 0)
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) :
    ∃ r : ℕ, r < ∏ i, s i ∧
      ∀ n : ℕ, (∀ i, n % s i = a i % s i) ↔ n % (∏ i, s i) = r := by
  classical
  -- The hypotheses on the full index set `univ`.
  have hs_univ : ∀ i ∈ (Finset.univ : Finset ι), s i ≠ 0 := fun i _ => hs i
  have hcop_univ : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime s) := by
    intro i _ j _ hij
    exact hcop hij
  -- Existence half of the CRT: a simultaneous solution `k`.
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset a s Finset.univ hs_univ hcop_univ
  -- Reduce `k` to a residue `r` in the range `[0, ∏ i, s i)`.
  refine ⟨k % (∏ i, s i),
    Nat.mod_lt _ (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (hs i))), ?_⟩
  intro n
  -- It suffices to identify the two statements as congruences.
  have hmain : (∀ i, n ≡ a i [MOD s i]) ↔ n ≡ k [MOD ∏ i, s i] := by
    constructor
    · intro h
      -- Uniqueness half of the CRT, package form.
      exact (modEq_prod_iff_forall Finset.univ s n k hs_univ hcop_univ).mpr
        (fun i _ => (h i).trans (hk i (Finset.mem_univ i)).symm)
    · intro h i
      -- A congruence modulo the product restricts to each factor.
      exact (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem s (Finset.mem_univ i)) h).trans
        (hk i (Finset.mem_univ i))
  -- Both sides are just restatements of `Nat.ModEq`.
  simpa only [Nat.ModEq] using hmain

end Commons.NumberTheory.CongruenceWindows