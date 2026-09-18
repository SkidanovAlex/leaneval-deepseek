import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-- The ancestor map vanishes at level `0`. -/
lemma anc_level_zero (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n i : ℕ) :
    Anc d c ρ η T 0 n i = none := rfl

/-- The recursion step of the ancestor map, in the form where only the two
non-matching conditions on the ancestor level are needed. -/
lemma anc_succ (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {N n i : ℕ} (h1 : n ≠ 0) (h2 : n ≠ N + 1) :
    Anc d c ρ η T (N+1) n i = (T.par (N+1) i).bind (fun j => Anc d c ρ η T N n j) := by
  rw [Anc]
  simp [h1, h2]

/-- The ancestor of a node is a ball of the tree at the ancestor's level. -/
lemma ancMem (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : Work.MassTransferenceAlt.TreeData d c ρ η)
    {N n i B : ℕ} (hi : i ∈ T.lev N) (h : Work.MassTransferenceAlt.Anc d c ρ η T N n i = some B) :
    B ∈ T.lev n := by
  classical
  induction N generalizing n i B with
  | zero =>
      rw [anc_level_zero] at h
      simp at h
  | succ N ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [anc_zero] at h
        simp at h
      · by_cases hn : n = N + 1
        · have h' : Anc d c ρ η T (N + 1) (N + 1) i = some B := by rwa [hn] at h
          rw [anc_self] at h'
          rw [← Option.some.inj h']
          rwa [hn]
        · have h1 : n ≠ 0 := by omega
          rw [anc_succ d c ρ η T h1 hn] at h
          obtain ⟨j, hj, hpar⟩ := T.par_mem N i hi
          rw [hpar] at h
          simp only [Option.bind_some] at h
          exact ih hj h

end Work.MassTransferenceAlt.Tree
