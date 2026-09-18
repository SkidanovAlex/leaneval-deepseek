import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-- A positive number `r ≤ 1` is at most its `d`-th power, for `0 < d` (and `d ≤ 1`). -/
private lemma self_le_rpow (d : ℝ) (_hd0 : 0 < d) (hd1 : d < 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) : r ≤ r ^ d := by
  have h := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (le_of_lt hd1)
  rwa [Real.rpow_one] at h

/-- **One step of nesting.**  The ball of a child is contained in the ball of its parent:
`IsLoc` puts the *enlarged* interval of a child inside the parent ball, and the enlarged
interval contains the ordinary one because the child radius is at most `Rabs d ≤ 1`. -/
private lemma ballSubsetPar (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) {n i j : ℕ} (hi : i ∈ T.lev (n + 1))
    (hpar : T.par (n + 1) i = some j) :
    Iv (c i) (ρ i) ⊆ Iv (c j) (ρ j) := by
  have hmem : i ∈ (T.lev (n + 1)).filter (fun i => T.par (n + 1) i = some j) :=
    Finset.mem_filter.mpr ⟨hi, hpar⟩
  obtain ⟨j', hj', hj'eq⟩ := T.par_mem n i hi
  rw [hpar] at hj'eq
  simp only [Option.some.injEq] at hj'eq
  subst hj'eq
  have hIv : Fenl d c ρ i ⊆ Iv (c j) (ρ j) := (T.loc n j hj').2.2.1 i hmem
  have hgood := T.good (n + 1) i hi
  have hle : ρ i ≤ (ρ i) ^ d :=
    self_le_rpow d hd0 hd1 hgood.1 (le_trans hgood.2.1 (Rabs_le_one hd1))
  calc Iv (c i) (ρ i) ⊆ Iv (c i) ((ρ i) ^ d) := Iv_mono hle
    _ = Fenl d c ρ i := rfl
    _ ⊆ Iv (c j) (ρ j) := hIv

/-- **Nesting.**  The ball of a node is contained in the ball of any of its ancestors. -/
lemma ballSubsetAnc (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) {N n i B : ℕ} (hi : i ∈ T.lev N)
    (hn0 : 0 < n) (hnN : n ≤ N)
    (h : Work.MassTransferenceAlt.Anc d c ρ η T N n i = some B) :
    Work.MassTransferenceAlt.Iv (c i) (ρ i) ⊆ Work.MassTransferenceAlt.Iv (c B) (ρ B) := by
  have key : ∀ N n i B : ℕ, 0 < n → n ≤ N → i ∈ T.lev N →
      Anc d c ρ η T N n i = some B → Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B) := by
    intro N
    induction N with
    | zero =>
        intro n i B hn0 hnN _
        omega
    | succ N ih =>
        intro n i B hn0 hnN hi h
        rcases lt_or_eq_of_le hnN with hlt | heq
        · -- `n ≤ N`: go up one level through the parent
          have hnN' : n ≤ N := by omega
          rw [anc_step d c ρ η T hn0 hnN'] at h
          cases hpar : T.par (N + 1) i with
          | none => rw [hpar] at h; simp at h
          | some j =>
              rw [hpar] at h
              simp only [Option.bind_some] at h
              obtain ⟨j', hj', hj'eq⟩ := T.par_mem N i hi
              rw [hpar] at hj'eq
              simp only [Option.some.injEq] at hj'eq
              subst hj'eq
              exact (ballSubsetPar d hd0 hd1 c ρ η T hi hpar).trans (ih n j B hn0 hnN' hj' h)
        · -- `n = N + 1`: the ancestor is the node itself
          subst heq
          rw [anc_self] at h
          simp only [Option.some.injEq] at h
          subst h
          exact subset_rfl
  exact key N n i B hn0 hnN hi h

end Work.MassTransferenceAlt.Tree
