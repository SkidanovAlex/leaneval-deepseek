import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.centralizer_sr_subset

namespace Work.L2F.Dihedral

open DihedralGroup

/-- A subgroup `V ≤ DihedralGroup m`, all of whose elements are involutions, cannot be contained
in the rotation subgroup `⟨r⟩`: indeed every element of `V` would be `r i` with `r (2 * i) = 1`,
i.e. `2 * i = 0`, so `i = 0` or `i = m / 2` (two-torsion of `ZMod m`), leaving at most the two
elements `1` and `r (m / 2)` in `V` — contradicting `Nat.card V = 4`. -/
private lemma not_le_rot_of_sq_eq_one {m : ℕ} (V : Subgroup (DihedralGroup m))
    (hcard : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1) : ¬ V ≤ Work.Dihedral.rot m := by
  intro hVrot
  -- Every element of `V` lies in `{1, r (m / 2)}`.
  have hsub : (V : Set (DihedralGroup m)) ⊆
      ({1, DihedralGroup.r ((m / 2 : ℕ) : ZMod m)} : Set (DihedralGroup m)) := by
    intro x hx
    obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp (hVrot hx)
    have h2 : DihedralGroup.r (i + i) = DihedralGroup.r (0 : ZMod m) := by
      have h := hsq (DihedralGroup.r i) hx
      rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def] at h
      exact h
    have hii : i + i = 0 := DihedralGroup.r.inj h2
    rcases zmod_add_self_eq_zero_or_eq_half i hii with h0 | hh
    · rw [h0]; simp
    · rw [hh]; simp
  -- hence `V` has at most two elements.
  have hle : Nat.card V ≤ 2 := by
    have hcoe : Nat.card V = (V : Set (DihedralGroup m)).ncard := by
      rw [← SetLike.coe_sort_coe V, Nat.card_coe_set_eq]
    rw [hcoe]
    calc (V : Set (DihedralGroup m)).ncard
        ≤ ({1, DihedralGroup.r ((m / 2 : ℕ) : ZMod m)} : Set (DihedralGroup m)).ncard :=
          Set.ncard_le_ncard hsub
            (Set.Finite.insert 1 (Set.finite_singleton
              (DihedralGroup.r ((m / 2 : ℕ) : ZMod m))))
      _ ≤ 2 := by
          calc ({1, DihedralGroup.r ((m / 2 : ℕ) : ZMod m)} : Set (DihedralGroup m)).ncard
              = (insert 1 {DihedralGroup.r ((m / 2 : ℕ) : ZMod m)} :
                  Set (DihedralGroup m)).ncard := rfl
            _ ≤ ({DihedralGroup.r ((m / 2 : ℕ) : ZMod m)} : Set (DihedralGroup m)).ncard + 1 :=
                Set.ncard_insert_le _ _
            _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem exists_sr_mem_of_card_four {m : ℕ} (V : Subgroup (DihedralGroup m))
    (hcard : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ i : ZMod m, DihedralGroup.sr i ∈ V := by
  by_contra h
  -- If `V` contained no reflection, it would lie in the rotation subgroup.
  refine not_le_rot_of_sq_eq_one V hcard hsq ?_
  intro x hx
  by_contra hxr
  obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hxr
  exact h ⟨i, hi ▸ hx⟩

end Work.L2F.Dihedral
