import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data
import Submission.Work.MassTransferenceAlt.Tree.childrenMem

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-! ### Two auxiliary lemmas about the mass functional

`childrenMass` is the one-step mass-conservation identity: the masses of the children of
a node add up to the mass of the node.  `massAncestor_step` is the corresponding one-step
identity for the sums over the descendants of a node, obtained by decomposing the
descendants of level `N+1` according to their parent at level `N`. -/

/-- **Mass conservation at one node.**  The masses of the children of a ball `B` of
level `m` add up to the mass of `B`.  This is the identity "the mass of a node is
distributed among its children" from the definition of `Mass`, made into an equality
using the fact that a node always has at least one child (`childrenMem`). -/
lemma childrenMass (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    (m B : ℕ) (hB : B ∈ T.lev m) :
    ∑ i ∈ (T.lev (m+1)).filter (fun i => T.par (m+1) i = some B),
        Mass d c ρ η T (m+1) (some i) = Mass d c ρ η T m (some B) := by
  classical
  set F : Finset ℕ := (T.lev (m+1)).filter (fun i => T.par (m+1) i = some B) with hF
  have hFmem : ∀ i, i ∈ F ↔ i ∈ T.lev (m+1) ∧ T.par (m+1) i = some B := by
    intro i; rw [hF, Finset.mem_filter]
  -- a node always has a child, and every child has positive `f`-volume, so the normalising
  -- sum is non-zero
  have hCpos : 0 < ∑ j ∈ F, vf d ρ j := by
    obtain ⟨i, hi, hpar⟩ := childrenMem d c ρ η T hB
    refine Finset.sum_pos (fun j hj => vf_pos ?_) ⟨i, (hFmem i).mpr ⟨hi, hpar⟩⟩
    exact (T.good (m+1) j ((hFmem j).mp hj).1).1
  have hstep : ∀ i ∈ F, Mass d c ρ η T (m+1) (some i)
      = (vf d ρ i / (∑ j ∈ F, vf d ρ j)) * Mass d c ρ η T m (some B) := by
    intro i hi
    obtain ⟨hi1, hpar⟩ := (hFmem i).mp hi
    simp only [Mass]
    rw [if_pos hi1]
    rw [hpar, hF]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, ← Finset.sum_div,
    div_self (ne_of_gt hCpos), one_mul]

/-- **One step of the mass distribution.**  The descendants of level `N+1` of a ball of
level `n ≤ N` are the disjoint union of the sets of children of the descendants of level
`N`, and each set of children carries the mass of its parent; hence the total mass of the
descendants of level `N+1` equals the total mass of the descendants of level `N`. -/
lemma massAncestor_step (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {N n : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) (B : ℕ) :
    ∑ i ∈ (T.lev (N+1)).filter (fun i => Anc d c ρ η T (N+1) n i = some B),
        Mass d c ρ η T (N+1) (some i)
    = ∑ i ∈ (T.lev N).filter (fun i => Anc d c ρ η T N n i = some B),
        Mass d c ρ η T N (some i) := by
  classical
  -- the descendants of `B` at level `N+1` form the disjoint union, over the descendants
  -- of `B` at level `N`, of the corresponding sets of children
  have hS_eq : (T.lev (N+1)).filter (fun i => Anc d c ρ η T (N+1) n i = some B)
      = ((T.lev N).filter (fun B' => Anc d c ρ η T N n B' = some B)).biUnion
          (fun B' => (T.lev (N+1)).filter (fun i => T.par (N+1) i = some B')) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hi, hanc⟩
      obtain ⟨B', hB', hpar⟩ := T.par_mem N i hi
      refine ⟨B', ⟨hB', ?_⟩, hi, hpar⟩
      rw [anc_step d c ρ η T hn0 hnN, hpar] at hanc
      simpa using hanc
    · rintro ⟨B', ⟨hB', hanc'⟩, hi, hpar⟩
      refine ⟨hi, ?_⟩
      rw [anc_step d c ρ η T hn0 hnN, hpar]
      simpa using hanc'
  have hdisj : (↑((T.lev N).filter (fun B' => Anc d c ρ η T N n B' = some B)) : Set ℕ).PairwiseDisjoint
      (fun B' => (T.lev (N+1)).filter (fun i => T.par (N+1) i = some B')) := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact fun hab => hxy (Option.some.inj (by rw [← ha.2, hab, hb.2]))
  rw [hS_eq, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro B' hB'
  exact childrenMass d c ρ η T N B' (Finset.mem_filter.mp hB').1

/-- **The mass of a node is the total mass of its descendants.**  Summing the masses of
all balls of level `N` whose ancestor at level `n` is `B` returns the mass of `B`. -/
lemma massAncestor (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : Work.MassTransferenceAlt.TreeData d c ρ η)
    {n N : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) (B : ℕ) (hB : B ∈ T.lev n) :
    ∑ i ∈ (T.lev N).filter (fun i => Work.MassTransferenceAlt.Anc d c ρ η T N n i = some B),
        Work.MassTransferenceAlt.Mass d c ρ η T N (some i)
      = Work.MassTransferenceAlt.Mass d c ρ η T n (some B) := by
  classical
  -- `n ≥ 1`, so `n = k + 1`; induct on the difference between `N` and `n`
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn0)
  have key : ∀ t : ℕ, ∀ B : ℕ, B ∈ T.lev (k+1) →
      ∑ i ∈ (T.lev ((k+1)+t)).filter (fun i => Anc d c ρ η T ((k+1)+t) (k+1) i = some B),
          Mass d c ρ η T ((k+1)+t) (some i) = Mass d c ρ η T (k+1) (some B) := by
    intro t B hB
    induction t with
    | zero =>
        -- base case `N = n`: every ball of the level is its own ancestor, so only `B` itself
        -- contributes
        simp only [Nat.add_zero]
        have hfilter : (T.lev (k+1)).filter (fun i => Anc d c ρ η T (k+1) (k+1) i = some B) = {B} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hi, hanc⟩
            simpa using hanc
          · intro hi
            subst hi
            exact ⟨hB, by simp⟩
        rw [hfilter, Finset.sum_singleton]
    | succ t ih =>
        -- inductive step: pass from level `(k+1)+t` to the next level
        simp only [Nat.add_succ]
        rw [massAncestor_step d c ρ η T (by omega : 0 < k+1) (by omega : k+1 ≤ (k+1)+t)]
        exact ih
  have hthis := key (N - (k+1)) B hB
  rw [Nat.add_sub_of_le hnN] at hthis
  exact hthis

end Work.MassTransferenceAlt.Tree
