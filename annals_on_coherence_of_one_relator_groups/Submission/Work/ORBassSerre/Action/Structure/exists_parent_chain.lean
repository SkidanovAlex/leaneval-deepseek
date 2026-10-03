import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum

namespace Work.ORBassSerre.Action.Structure

/-- Every vertex orbit `A` is joined to the root orbit by a chain that follows the parent map:
there is a sequence `c 0 = d.root, c 1, …, c n = A` with `d.par (c (k+1)) = c k` and such that
every orbit that is a parent (`c (k+1)`, `k < n`) is not the root. -/
theorem exists_parent_chain {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum G V)
    (A : Work.ORBassSerre.orbitV G V) :
    ∃ (c : ℕ → Work.ORBassSerre.orbitV G V) (n : ℕ),
      c 0 = d.root ∧ c n = A ∧
        (∀ k < n, c (k + 1) ≠ d.root) ∧ (∀ k < n, d.par (c (k + 1)) = c k) := by
  classical
  -- Strong induction on an upper bound for the rank.
  suffices key : ∀ m : ℕ, ∀ A : Work.ORBassSerre.orbitV G V, d.rank A ≤ m →
      ∃ (c : ℕ → Work.ORBassSerre.orbitV G V) (n : ℕ),
        c 0 = d.root ∧ c n = A ∧
          (∀ k < n, c (k + 1) ≠ d.root) ∧ (∀ k < n, d.par (c (k + 1)) = c k) from
    key (d.rank A) A le_rfl
  intro m
  induction m with
  | zero =>
    intro A hA
    have hrank : d.rank A = 0 := Nat.le_zero.mp hA
    have hroot : A = d.root := (d.rank_eq_zero A).mp hrank
    refine ⟨fun _ => d.root, 0, rfl, hroot.symm, ?_, ?_⟩
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
    intro A hA
    by_cases hle : d.rank A ≤ m
    · exact ih A hle
    · have hrank : d.rank A = m + 1 := by
        have h1 : m < d.rank A := Nat.lt_of_not_le hle
        omega
      have hAne : A ≠ d.root := by
        intro h
        rw [h, d.rank_root] at hrank
        omega
      have hpar_le : d.rank (d.par A) ≤ m := by
        have hlt : d.rank (d.par A) < m + 1 := by
          rw [← hrank]; exact d.rank_par_lt A hAne
        exact Nat.lt_succ_iff.mp hlt
      obtain ⟨c', n', hc0, hcn, hne, hpar⟩ := ih (d.par A) hpar_le
      refine ⟨fun k => if k ≤ n' then c' k else A, n' + 1, ?_, ?_, ?_, ?_⟩
      · show (if (0 : ℕ) ≤ n' then c' 0 else A) = d.root
        rw [if_pos (Nat.zero_le n'), hc0]
      · show (if n' + 1 ≤ n' then c' (n' + 1) else A) = A
        rw [if_neg (Nat.not_succ_le_self n')]
      · intro k hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · have hk1 : k + 1 ≤ n' := hlt
          show (if k + 1 ≤ n' then c' (k + 1) else A) ≠ d.root
          rw [if_pos hk1]
          exact hne k hlt
        · rw [heq]
          show (if n' + 1 ≤ n' then c' (n' + 1) else A) ≠ d.root
          rw [if_neg (Nat.not_succ_le_self n')]
          exact hAne
      · intro k hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · have hk1 : k + 1 ≤ n' := hlt
          have hk0 : k ≤ n' := le_of_lt hlt
          show d.par (if k + 1 ≤ n' then c' (k + 1) else A) = (if k ≤ n' then c' k else A)
          rw [if_pos hk1, if_pos hk0]
          exact hpar k hlt
        · rw [heq]
          show d.par (if n' + 1 ≤ n' then c' (n' + 1) else A) = (if n' ≤ n' then c' n' else A)
          rw [if_neg (Nat.not_succ_le_self n'), if_pos le_rfl]
          exact hcn.symm

end Work.ORBassSerre.Action.Structure
