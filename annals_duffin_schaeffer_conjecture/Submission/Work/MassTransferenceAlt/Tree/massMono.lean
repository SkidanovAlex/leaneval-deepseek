import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.massAncestor
import Submission.Work.MassTransferenceAlt.Tree.ballSubsetAnc
import Submission.Work.MassTransferenceAlt.Tree.ancMem
import Submission.Work.MassTransferenceAlt.Tree.MassSum

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-!
# Monotonicity of the mass of the balls hit by an interval

The mass functional `Mass` distributes, at every node of the Cantor tree, the mass of the
node among its children in proportion to their `f`-volumes, so that the total mass of the
children of a node is exactly the mass of the node (`massSum_children`).

Consequently the total mass of the balls of a level that meet a fixed interval is
*nonincreasing* in the level: a child ball is contained in the ball of its parent
(`child_ball_subset`), hence a hitting child has a hitting parent; and the hitting children
of a ball `B` are a subfamily of all children of `B`, whose total mass is the mass of `B`.

This is the estimate that makes the Cantor set of the construction carry the correct
`d`-dimensional measure.
-/

/-- The mass of a ball of the tree is nonnegative. -/
private lemma mass_nonneg (d : ℝ) (_hd0 : 0 < d) (_hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) : ∀ n (i : ℕ), i ∈ T.lev n → 0 ≤ Mass d c ρ η T n (some i) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      have hne : (T.lev 0).Nonempty := by
        obtain ⟨i, hi, _⟩ :=
          T.root_loc.2.2.2.2.2.2.1 0 (lt_of_lt_of_le Nat.zero_lt_one (nsubRoot_pos η))
        exact ⟨i, hi⟩
      have hpos : ∀ j ∈ T.lev 0, 0 < vf d ρ j := fun j hj => vf_pos (T.root_loc.1 j hj)
      have hS : 0 < ∑ j ∈ T.lev 0, vf d ρ j :=
        Finset.sum_pos' (fun j hj => (hpos j hj).le) (hne.imp fun j hj => ⟨hj, hpos j hj⟩)
      rw [mass_zero_eq, if_pos hi]
      exact div_nonneg (hpos i hi).le hS.le
  | succ n ih =>
      intro i hi
      obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
      rw [show Mass d c ρ η T (n+1) (some i) =
          (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter
            (fun j => T.par (n+1) j = T.par (n+1) i), vf d ρ j))
            * Mass d c ρ η T n (T.par (n+1) i) from by simp [Mass, hi]]
      rw [hpar]
      refine mul_nonneg (div_nonneg (le_of_lt (vf_pos (T.good (n+1) i hi).1)) ?_) (ih B hB)
      exact Finset.sum_nonneg (fun j hj =>
        (vf_pos (T.good (n+1) j (Finset.mem_filter.mp hj).1).1).le)

/-- The ball of a ball of level `n + 1` is contained in the ball of its parent: `IsLoc`
puts the *enlarged* interval of a child inside the parent ball, and the enlarged interval
contains the ordinary one because the child radius is at most `Rabs d ≤ 1`. -/
private lemma child_ball_subset (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) {n i B : ℕ} (hi : i ∈ T.lev (n + 1))
    (hpar : T.par (n + 1) i = some B) : Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B) := by
  obtain ⟨B', hB', hpar'⟩ := T.par_mem n i hi
  have hBB : B' = B := by
    have h2 := hpar'
    rw [hpar] at h2
    exact (Option.some.inj h2).symm
  have hB : B ∈ T.lev n := by rw [← hBB]; exact hB'
  have hmem : i ∈ (T.lev (n + 1)).filter (fun j => T.par (n + 1) j = some B) :=
    Finset.mem_filter.mpr ⟨hi, hpar⟩
  have hIv : Fenl d c ρ i ⊆ Iv (c B) (ρ B) := (T.loc n B hB).2.2.1 i hmem
  have hgood := T.good (n + 1) i hi
  have hle : ρ i ≤ (ρ i) ^ d := self_le_rpow hd0 hd1 hgood.1 hgood.2.1
  calc Iv (c i) (ρ i) ⊆ Iv (c i) ((ρ i) ^ d) := Iv_mono hle
    _ = Fenl d c ρ i := rfl
    _ ⊆ Iv (c B) (ρ B) := hIv

/-- If the ball of `i` is contained in the ball of `B`, then everything hit by `i` is hit
by `B`.  (The inclusion of intervals is turned into the linear inequality
`|c i - c B| + ρ i ≤ ρ B` by evaluating it at the two endpoints of `Iv (c i) (ρ i)`.) -/
private lemma hits_of_subset {c ρ : ℕ → ℝ} {x r : ℝ} {i B : ℕ} (hρi : 0 ≤ ρ i)
    (hsub : Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B)) (h : hits c ρ x r i) : hits c ρ x r B := by
  have h1 : c i + ρ i ∈ Iv (c i) (ρ i) := by
    rw [mem_Iv, abs_le]; constructor <;> linarith
  have h2 : c i - ρ i ∈ Iv (c i) (ρ i) := by
    rw [mem_Iv, abs_le]; constructor <;> linarith
  have h3 : |c i + ρ i - c B| ≤ ρ B := mem_Iv.mp (hsub h1)
  have h4 : |c i - ρ i - c B| ≤ ρ B := mem_Iv.mp (hsub h2)
  rw [abs_le] at h3 h4
  have hab : |c i - c B| ≤ ρ B - ρ i := by
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  have hxi : |x - c i| ≤ r + ρ i := h
  rw [hits]
  calc |x - c B| = |(x - c i) + (c i - c B)| := by ring_nf
    _ ≤ |x - c i| + |c i - c B| := abs_add_le _ _
    _ ≤ (r + ρ i) + (ρ B - ρ i) := add_le_add hxi hab
    _ = r + ρ B := by ring

/-- **One step of the monotonicity.**  The total mass of the balls of level `N + 1` meeting
`Iv x r` is at most the total mass of the balls of level `N` meeting `Iv x r`:
the meeting balls of level `N + 1` are children of meeting balls of level `N`, and the
meeting children of a ball form a subfamily of all its children, whose masses add up to
the mass of the ball. -/
private lemma massMono_step (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) (x r : ℝ) (N : ℕ) :
    ∑ i ∈ (T.lev (N+1)).filter (fun i => hits c ρ x r i), Mass d c ρ η T (N+1) (some i)
      ≤ ∑ i ∈ (T.lev N).filter (fun i => hits c ρ x r i), Mass d c ρ η T N (some i) := by
  classical
  -- the meeting balls of level `N + 1` are the disjoint union, over the meeting balls `B`
  -- of level `N`, of the meeting children of `B`
  have hS_eq : (T.lev (N+1)).filter (fun i => hits c ρ x r i)
      = ((T.lev N).filter (fun i => hits c ρ x r i)).biUnion
          (fun B => ((T.lev (N+1)).filter (fun i => T.par (N+1) i = some B)).filter
            (fun i => hits c ρ x r i)) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hilev, hhit⟩ := hi
      obtain ⟨B, hB, hpar⟩ := T.par_mem N i hilev
      have hhitB : hits c ρ x r B :=
        hits_of_subset (le_of_lt (T.good (N+1) i hilev).1)
          (child_ball_subset d hd0 hd1 c ρ η T hilev hpar) hhit
      rw [Finset.mem_biUnion]
      exact ⟨B, Finset.mem_filter.mpr ⟨hB, hhitB⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hilev, hpar⟩, hhit⟩⟩
    · intro hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨B, _hB, hi⟩ := hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1, (Finset.mem_filter.mp hi).2⟩
  have hdisj : (↑((T.lev N).filter (fun i => hits c ρ x r i)) : Set ℕ).PairwiseDisjoint
      (fun B => ((T.lev (N+1)).filter (fun i => T.par (N+1) i = some B)).filter
        (fun i => hits c ρ x r i)) := by
    intro B _ B' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    intro hab
    exact hne (Option.some.inj (by rw [← ha.1.2, hab, hb.1.2]))
  rw [hS_eq, Finset.sum_biUnion hdisj]
  calc ∑ B ∈ (T.lev N).filter (fun i => hits c ρ x r i),
        ∑ i ∈ ((T.lev (N+1)).filter (fun i => T.par (N+1) i = some B)).filter
          (fun i => hits c ρ x r i), Mass d c ρ η T (N+1) (some i)
      ≤ ∑ B ∈ (T.lev N).filter (fun i => hits c ρ x r i),
        ∑ i ∈ (T.lev (N+1)).filter (fun i => T.par (N+1) i = some B),
          Mass d c ρ η T (N+1) (some i) := by
        -- the meeting children of `B` are a subfamily of all the children of `B`
        refine Finset.sum_le_sum (fun B _hB => ?_)
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i hi _ => ?_)
        · exact (Finset.mem_filter.mp hi).1
        · exact mass_nonneg d hd0 hd1 c ρ η T (N+1) i (Finset.mem_filter.mp hi).1
    _ = ∑ B ∈ (T.lev N).filter (fun i => hits c ρ x r i),
          Mass d c ρ η T N (some B) := by
        -- the masses of all the children of `B` add up to the mass of `B`
        refine Finset.sum_congr rfl (fun B hB => ?_)
        exact massSum_children d c ρ η T N B (Finset.mem_filter.mp hB).1

lemma massMono (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : Work.MassTransferenceAlt.TreeData d c ρ η) {x r : ℝ} {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) : ∑ i ∈ (T.lev N).filter (fun i => Work.MassTransferenceAlt.hits c ρ x r i), Work.MassTransferenceAlt.Mass d c ρ η T N (some i) ≤ ∑ i ∈ (T.lev n).filter (fun i => Work.MassTransferenceAlt.hits c ρ x r i), Work.MassTransferenceAlt.Mass d c ρ η T n (some i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  have key : ∀ k : ℕ,
      ∑ i ∈ (T.lev (n + k)).filter (fun i => hits c ρ x r i), Mass d c ρ η T (n + k) (some i)
        ≤ ∑ i ∈ (T.lev n).filter (fun i => hits c ρ x r i),
            Mass d c ρ η T n (some i) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        calc ∑ i ∈ (T.lev (n + (k + 1))).filter (fun i => hits c ρ x r i),
              Mass d c ρ η T (n + (k + 1)) (some i)
            = ∑ i ∈ (T.lev ((n + k) + 1)).filter (fun i => hits c ρ x r i),
              Mass d c ρ η T ((n + k) + 1) (some i) := by rw [Nat.add_succ]
          _ ≤ ∑ i ∈ (T.lev (n + k)).filter (fun i => hits c ρ x r i),
              Mass d c ρ η T (n + k) (some i) :=
              massMono_step d hd0 hd1 c ρ η T x r (n + k)
          _ ≤ ∑ i ∈ (T.lev n).filter (fun i => hits c ρ x r i),
              Mass d c ρ η T n (some i) := ih
  exact key k

end Work.MassTransferenceAlt.Tree
