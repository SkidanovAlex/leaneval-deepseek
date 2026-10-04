import Mathlib.Analysis.Normed.Order.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology

/-- If `c k ≤ c (k+1)` on `k < A`, then `c` is monotone on `{0, …, A}`. -/
private lemma chain_mono_of_le_succ {c : ℕ → ℝ} {A : ℕ}
    (hmono : ∀ k < A, c k ≤ c (k + 1)) :
    ∀ j, j ≤ A → ∀ i, i ≤ j → c i ≤ c j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this; rfl
  | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · rw [Nat.lt_succ_iff] at hlt
        exact le_trans (ih (by omega) i hlt) (hmono j (by omega))
      · have : i = j + 1 := by omega
        subst this; rfl

theorem continuousOn_Icc_of_continuousOn_pieces {f : ℝ → ℝ} {N : ℕ} {c : ℕ → ℝ} {a b : ℝ}
    (hc0 : c 0 = a) (hcN : c N = b) (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, ContinuousOn f (Set.Icc (c k) (c (k + 1)))) :
    ContinuousOn f (Set.Icc a b) := by
  have aux : ∀ N : ℕ, ∀ c : ℕ → ℝ, ∀ a b : ℝ, c 0 = a → c N = b →
      (∀ k < N, c k ≤ c (k + 1)) →
      (∀ k < N, ContinuousOn f (Set.Icc (c k) (c (k + 1)))) →
      ContinuousOn f (Set.Icc a b) := by
    intro N
    induction N with
    | zero =>
        intro c a b hc0 hcN _hmono _hpiece
        have hab : a = b := hc0.symm.trans hcN
        rw [hab, Set.Icc_self]
        exact continuousOn_singleton f b
    | succ N ih =>
        intro c a b hc0 hcN hmono hpiece
        have h₁ : ContinuousOn f (Set.Icc a (c N)) :=
          ih c a (c N) hc0 rfl (fun k hk => hmono k (Nat.lt_succ_of_lt hk))
            (fun k hk => hpiece k (Nat.lt_succ_of_lt hk))
        have h₂ : ContinuousOn f (Set.Icc (c N) b) := by
          have h := hpiece N (Nat.lt_succ_self N)
          simpa [hcN] using h
        have hac : a ≤ c N := by
          rw [← hc0]
          exact chain_mono_of_le_succ hmono N (Nat.le_succ N) 0 (Nat.zero_le N)
        have hcb : c N ≤ b := by
          have h := hmono N (Nat.lt_succ_self N)
          rwa [hcN] at h
        have hU := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
        rw [Set.Icc_union_Icc_eq_Icc hac hcb] at hU
        exact hU
  exact aux N c a b hc0 hcN hmono hpiece

end Commons.Topology