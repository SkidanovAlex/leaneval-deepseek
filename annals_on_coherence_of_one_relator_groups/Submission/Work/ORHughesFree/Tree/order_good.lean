import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.edge
import Submission.Work.ORHughesFree.Tree.fam_basic
import Submission.Work.ORHughesFree.Tree.dmLT_trans
import Submission.Work.ORHughesFree.Tree.dmLT_irrefl
import Submission.Work.ORHughesFree.Tree.dmLT_trichotomy

/-!
# The tree order is a strict total order

We prove that `lt` is irreflexive, transitive and trichotomous, by induction on the number of
edges.  On trees with at most `n` edges the order is the Dershowitz–Manna order on the (multiset
of) children, whose entries have at most `n - 1` edges; the Dershowitz–Manna facts then transfer.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The one-vertex tree is not strictly below itself. -/
theorem zero_not_lt_zero : ¬ lt (0 : Tree) 0 := by
  rw [lt_iff_dmLT, fam_zero]
  exact dmLT_irrefl (M := (0 : Multiset Tree))
    (fun a ha => absurd ha (by simp)) (fun a ha => absurd ha (by simp))
    (fun a ha => absurd ha (by simp))

/-- The order restricted to trees with at most `n` edges is a strict total order. -/
private def Good (n : ℕ) : Prop :=
  (∀ x : Tree, edge x ≤ n → ¬ lt x x) ∧
  (∀ x y : Tree, edge x ≤ n → edge y ≤ n → lt x y ∨ x = y ∨ lt y x) ∧
  (∀ x y z : Tree, edge x ≤ n → edge y ≤ n → edge z ≤ n → lt x y → lt y z → lt x z)

private theorem good : ∀ n, Good n := by
  intro n
  induction n with
  | zero =>
    have hirr : ∀ x : Tree, edge x ≤ 0 → ¬ lt x x := by
      intro x hx hlt
      have hx0 : x = 0 := edge_eq_zero (Nat.le_zero.mp hx)
      rw [hx0] at hlt
      exact zero_not_lt_zero hlt
    refine ⟨hirr, ?_, ?_⟩
    · intro x y hx hy
      have hx0 : x = 0 := edge_eq_zero (Nat.le_zero.mp hx)
      have hy0 : y = 0 := edge_eq_zero (Nat.le_zero.mp hy)
      exact Or.inr (Or.inl (hx0.trans hy0.symm))
    · intro x y z hx hy hz hxy hyz
      have hx0 : x = 0 := edge_eq_zero (Nat.le_zero.mp hx)
      have hy0 : y = 0 := edge_eq_zero (Nat.le_zero.mp hy)
      rw [hx0, hy0] at hxy
      exact absurd hxy zero_not_lt_zero
  | succ n ih =>
    have hbX : ∀ {x : Tree}, edge x ≤ n + 1 → ∀ a : Tree, a ∈ fam x → edge a ≤ n :=
      fun {x} hx a ha => Nat.le_of_lt_succ (lt_of_lt_of_le (edge_lt_of_mem_fam ha) hx)
    have hbN : ∀ {x y : Tree}, edge x ≤ n + 1 → edge y ≤ n + 1 →
        ∀ a : Tree, a ∈ fam x + fam y → edge a ≤ n := by
      intro x y hx hy a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · exact hbX hx a ha
      · exact hbX hy a ha
    have hirr : ∀ x : Tree, edge x ≤ n + 1 → ¬ lt x x := by
      intro x hx hlt
      rw [lt_iff_dmLT] at hlt
      exact dmLT_irrefl (M := fam x)
        (fun a ha b hb => ih.2.1 a b (hbX hx a ha) (hbX hx b hb))
        (fun a ha b hb c hc => ih.2.2 a b c (hbX hx a ha) (hbX hx b hb) (hbX hx c hc))
        (fun a ha => ih.1 a (hbX hx a ha)) hlt
    refine ⟨hirr, ?_, ?_⟩
    · intro x y hx hy
      rcases dmLT_trichotomy (M := fam x) (N := fam y)
        (fun a ha b hb => ih.2.1 a b (hbN hx hy a ha) (hbN hx hy b hb))
        (fun a ha b hb c hc =>
          ih.2.2 a b c (hbN hx hy a ha) (hbN hx hy b hb) (hbN hx hy c hc))
        (fun a ha => ih.1 a (hbN hx hy a ha)) with h | h | h
      · exact Or.inl ((lt_iff_dmLT x y).mpr h)
      · exact Or.inr (Or.inl (fam_injective h))
      · exact Or.inr (Or.inr ((lt_iff_dmLT y x).mpr h))
    · intro x y z hx hy hz hxy hyz
      rw [lt_iff_dmLT] at hxy hyz ⊢
      exact dmLT_trans
        (fun a ha b hb c hc hab hbc =>
          ih.2.2 a b c (hbX hx a ha) (hbX hy b hb) (hbX hz c hc) hab hbc)
        hxy hyz

/-- The tree order is irreflexive. -/
theorem lt_irrefl {x : Tree} : ¬ lt x x := (good (edge x)).1 x le_rfl

/-- The tree order is trichotomous. -/
theorem lt_trichotomy (x y : Tree) : lt x y ∨ x = y ∨ lt y x :=
  (good (max (edge x) (edge y))).2.1 x y (le_max_left _ _) (le_max_right _ _)

/-- The tree order is transitive. -/
theorem lt_trans {x y z : Tree} (hxy : lt x y) (hyz : lt y z) : lt x z :=
  (good (edge x + edge y + edge z)).2.2 x y z (by omega) (by omega) (by omega) hxy hyz

/-- The tree order is asymmetric. -/
theorem lt_asymm {x y : Tree} (h : lt x y) : ¬ lt y x :=
  fun h' => (good (max (edge x) (edge y))).1 x (le_max_left _ _) (lt_trans h h')

end Work.ORHughesFree.Tree
