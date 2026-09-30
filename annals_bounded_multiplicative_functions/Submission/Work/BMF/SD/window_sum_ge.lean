import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.coprime_primesIn_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- The hypotheses `hr`, `h1r`, `hP` are part of the requested statement but are not needed by
-- the argument (it only uses `j₀ + 1 ≤ N` and `f ≥ 0`); silence the unused-variable linter.
set_option linter.unusedVariables false

/-!
# Splitting a window sum over primes into consecutive dyadic-geometric blocks

For `r ≥ 1` and `P > 0` the real intervals `[P r^j, P r^{j+1}]`, `j = j₀, …, N-1`, cover
`[P r^{j₀}, P r^N]` (they overlap only in their endpoints, and possibly not even there).
Since `f ≥ 0`, the sum of `f` over the primes of the big interval is therefore bounded by
the sum, over all blocks, of the sum of `f` over the primes of that block: overlapping is
harmless because the right-hand side may count a prime several times.

The two ingredients are
* `Work.BMF.SD.window_primesIn_cover`: the covering statement, proved by taking for a prime
  `p` in the big interval the *largest* `m ≤ N-1` with `P r^m ≤ p` (`Nat.findGreatest`);
  maximality forces `p ≤ P r^{m+1}`, since otherwise `m = N-1` and `p ≤ P r^N = P r^{m+1}`.
  Note that no monotonicity of `j ↦ P r^j` is needed, only the case distinction.
* `Work.BMF.SD.sum_biUnion_le_of_nonneg`: `∑_{b ∈ s.biUnion t} f b ≤ ∑_{a ∈ s} ∑_{b ∈ t a} f b`
  for `f ≥ 0` (a standard Mathlib gap): the union bound for finset sums, no disjointness
  required.
-/

namespace Work.BMF.SD

open Finset

/-- Union bound for finset sums: if `f ≥ 0`, the sum over `s.biUnion t` is at most the sum of
the sums over the individual `t a` (a prime may be counted several times, which only helps). -/
private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  have key : ∀ u v : Finset β, ∑ b ∈ u ∪ v, f b ≤ ∑ b ∈ u, f b + ∑ b ∈ v, f b := by
    intro u v
    have h1 : ∑ b ∈ v \ u, f b ≤ ∑ b ∈ v, f b :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
    calc ∑ b ∈ u ∪ v, f b = ∑ b ∈ u ∪ (v \ u), f b := by rw [Finset.union_sdiff_self_eq_union]
      _ = ∑ b ∈ u, f b + ∑ b ∈ v \ u, f b := Finset.sum_union Finset.disjoint_sdiff
      _ ≤ ∑ b ∈ u, f b + ∑ b ∈ v, f b := by linarith
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc ∑ b ∈ t a ∪ s.biUnion t, f b
          ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := key _ _
        _ ≤ ∑ b ∈ t a, f b + ∑ x ∈ s, ∑ b ∈ t x, f b := by linarith

/-- The primes of `[P r^{j₀}, P r^N]` lie in the union of the blocks `[P r^j, P r^{j+1}]`,
`j₀ ≤ j ≤ N-1`. -/
private lemma window_primesIn_cover {r P : ℝ} {j₀ N : ℕ} (hj : j₀ + 1 ≤ N) :
    Work.BMF.primesIn (P * r ^ j₀) (P * r ^ N) ⊆
      (Finset.Icc j₀ (N - 1)).biUnion
        (fun j => Work.BMF.primesIn (P * r ^ j) (P * r ^ (j + 1))) := by
  intro p hp
  rw [Work.BMF.mr_direct.mem_primesIn_iff] at hp
  obtain ⟨hprime, hlo, hhi⟩ := hp
  have hj₀ : j₀ ≤ N - 1 := by omega
  -- the largest block index `j ≤ N-1` with `P r^j ≤ p`
  set m := Nat.findGreatest (fun j => P * r ^ j ≤ (p : ℝ)) (N - 1) with hmdef
  have hmj : j₀ ≤ m := by
    rw [hmdef]
    exact Nat.le_findGreatest (P := fun j => P * r ^ j ≤ (p : ℝ)) hj₀ hlo
  have hmle : m ≤ N - 1 := by
    rw [hmdef]; exact Nat.findGreatest_le _
  have hmP : P * r ^ m ≤ (p : ℝ) := by
    rw [hmdef]
    exact Nat.findGreatest_spec (P := fun j => P * r ^ j ≤ (p : ℝ)) hj₀ hlo
  -- maximality forces the upper endpoint `P r^{m+1}` to reach `p`
  have hup : (p : ℝ) ≤ P * r ^ (m + 1) := by
    by_contra hcon
    push Not at hcon
    by_cases hcase : m + 1 ≤ N - 1
    · -- then `m + 1` would be a larger admissible index
      have hle' : m + 1 ≤ m := by
        rw [hmdef]
        exact Nat.le_findGreatest (P := fun j => P * r ^ j ≤ (p : ℝ)) hcase (le_of_lt hcon)
      omega
    · -- otherwise `m + 1 = N` and `p ≤ P r^N = P r^{m+1}`
      have hEq : m + 1 = N := by omega
      have hlt : P * r ^ N < (p : ℝ) := by rwa [hEq] at hcon
      linarith
  rw [Finset.mem_biUnion]
  exact ⟨m, by rw [Finset.mem_Icc]; exact ⟨hmj, hmle⟩,
    Work.BMF.mr_direct.mem_primesIn_iff.mpr ⟨hprime, hmP, hup⟩⟩

theorem window_sum_ge {r P : ℝ} (hr : 0 < r) (h1r : 1 ≤ r) (hP : 0 < P) {j₀ N : ℕ}
    (hj : j₀ + 1 ≤ N) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ p ∈ Work.BMF.primesIn (P * r ^ j₀) (P * r ^ N), f p
      ≤ ∑ j ∈ Finset.Icc j₀ (N - 1),
          ∑ p ∈ Work.BMF.primesIn (P * r ^ j) (P * r ^ (j + 1)), f p := by
  calc ∑ p ∈ Work.BMF.primesIn (P * r ^ j₀) (P * r ^ N), f p
      ≤ ∑ p ∈ (Finset.Icc j₀ (N - 1)).biUnion
            (fun j => Work.BMF.primesIn (P * r ^ j) (P * r ^ (j + 1))), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (window_primesIn_cover hj) (fun i _ _ => hf i)
    _ ≤ ∑ j ∈ Finset.Icc j₀ (N - 1),
          ∑ p ∈ Work.BMF.primesIn (P * r ^ j) (P * r ^ (j + 1)), f p :=
        sum_biUnion_le_of_nonneg _ _ _ hf

end Work.BMF.SD
