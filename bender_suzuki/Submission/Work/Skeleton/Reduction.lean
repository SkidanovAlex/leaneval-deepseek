import Submission.Work.Skeleton.Basic
import Submission.Work.Skeleton.card_subgroup_lt_card
import Submission.Work.Skeleton.card_quotient_lt_card
import Submission.Work.Skeleton.odd_card_subgroup
import Submission.Work.Skeleton.odd_card_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A0 — Skeleton: the reduction to a minimal counterexample

This module proves the reduction step of the Feit–Thompson odd order theorem: it suffices to
rule out the existence of a minimal counterexample (`Work.Skeleton.MinSimpleOdd`) *in the
universe of the group under consideration*.

The proof is a strong induction on `Nat.card G`.  If `G` is not solvable, then

* every proper normal subgroup `N` (with `N ≠ ⊥`) gives proper subgroups `N` and `G ⧸ N` of
  smaller order, which are solvable by the induction hypothesis, whence `G` is solvable by
  `Group.isSolvable_of_subgroup_quotient` — a contradiction; so `G` has no proper nontrivial
  normal subgroup, i.e. `G` is simple;
* if `G` were commutative it would be solvable, so `G` is not commutative;
* every proper subgroup of `G` has smaller order, hence is solvable by the induction
  hypothesis.

Thus `G` is a minimal counterexample, contradicting the hypothesis `hnomin`.

Note the strong induction is carried out *within a fixed universe* `u`: all groups occurring
in the induction (`↥N`, `G ⧸ N`, and the subgroups `H ≤ G`) live in `Type u`, and this is why
`feit_thompson_of_no_min` quantifies over `G : Type u` on both sides.
-/

namespace Work.Skeleton

universe u

/-- **Reduction step of the odd order theorem.**  If no minimal counterexample exists in the
universe `u`, then every finite group of odd order in `Type u` is solvable. -/
theorem feit_thompson_of_no_min
    (hnomin : ∀ (G : Type u) [Group G] [Finite G], ¬ MinSimpleOdd G)
    {G : Type u} [Group G] [Finite G] (hG : Odd (Nat.card G)) : Group.IsSolvable G := by
  suffices key : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      Odd (Nat.card G) → Group.IsSolvable G from key _ G rfl hG
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G instG finG hcard hodd
    by_contra hnsol
    have hnonab : ∃ a b : G, a * b ≠ b * a := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hnsol (Group.isSolvable_of_comm h)
    have hsimple : IsSimpleGroup G := by
      have hnt : Nontrivial G := by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨a, b, fun heq => hab (by rw [heq])⟩
      refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := ?_ }
      intro N hN
      by_cases hNbot : N = ⊥
      · exact Or.inl hNbot
      right
      by_contra hNtop
      have hNlt : Nat.card N < n := by
        rw [← hcard]; exact card_subgroup_lt_card N hNtop
      have hQlt : Nat.card (G ⧸ N) < n := by
        rw [← hcard]; exact card_quotient_lt_card N hNbot
      have : Group.IsSolvable N := ih (Nat.card N) hNlt N rfl (odd_card_subgroup hodd N)
      have : Group.IsSolvable (G ⧸ N) :=
        ih (Nat.card (G ⧸ N)) hQlt (G ⧸ N) rfl (odd_card_quotient hodd N)
      exact hnsol (Group.isSolvable_of_subgroup_quotient N)
    have hpropsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H := by
      intro H hH
      exact ih (Nat.card H) (by rw [← hcard]; exact card_subgroup_lt_card H hH) H rfl
        (odd_card_subgroup hodd H)
    exact hnomin G ⟨hodd, hsimple, hnonab, hpropsolv⟩

end Work.Skeleton
