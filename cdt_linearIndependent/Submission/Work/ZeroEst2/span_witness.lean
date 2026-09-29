import Mathlib

namespace Work.ZeroEst2

/-- The contrapositive of the target: if no `v k` lies in the span of the previous ones,
then the first `N` vectors are linearly independent. -/
theorem span_witness_aux {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
    (v : ℕ → M) : ∀ N : ℕ,
      (∀ k < N, v k ∉ Submodule.span K (Set.range fun i : Fin k => v i)) →
        LinearIndependent K (fun i : Fin N => v i) := by
  intro N
  induction N with
  | zero => intro _; exact linearIndependent_empty_type
  | succ N ih =>
    intro H
    rw [linearIndependent_finSucc']
    exact ⟨ih (fun k hk => H k (Nat.lt_succ_of_lt hk)), H N (Nat.lt_succ_self N)⟩

theorem span_witness {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (v : ℕ → M) {N : ℕ} (h : ¬ LinearIndependent K (fun i : Fin N => v i)) :
    ∃ k, k < N ∧ v k ∈ Submodule.span K (Set.range fun i : Fin k => v i) := by
  by_contra hc
  exact h (span_witness_aux v N fun k hk hmem => hc ⟨k, hk, hmem⟩)

end Work.ZeroEst2
