import Mathlib
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.ascIdx_mem
import Submission.Work.PL.Shell.exists_ascent

namespace Work.PL.Sd1

open Finset

/-- `toFinset` only depends on the permutation class of a list. -/
theorem toFinset_eq_of_perm {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : l₁.toFinset = l₂.toFinset := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y _ => simp [Finset.insert_comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- The index criterion of `NOTES_Shell.md` §1: if a face `J` of the flag `l` is not contained
in the "boundary `B`" and all ascent positions of `l` lie in `J`, then the last vertex of `l`
lies in `T` and the last index does not lie in `J`. -/
theorem crit_to_idx {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) {J : Finset ℕ}
    (hJ : J ⊆ Finset.range l.length) (hJne : J.Nonempty) :
    ((∃ w ∈ T, w ∉ Work.PL.Shell.prefAt l (J.max' hJne)) ∨
        ¬ (Work.PL.Shell.ascIdx rk l ⊆ J)) →
      (∃ i ∈ Work.PL.Shell.ascIdx rk l, i ∉ J) ∨
        ((∃ v, l.getLast? = some v ∧ v ∈ T) ∧ l.length - 1 ∉ J) := by
  classical
  intro h
  by_cases hsub : Work.PL.Shell.ascIdx rk l ⊆ J
  · right
    -- the hypothesis must be witnessed by the "boundary" disjunct
    have hV : ∃ w ∈ T, w ∉ Work.PL.Shell.prefAt l (J.max' hJne) := by
      rcases h with hh | hh
      · exact hh
      · exact absurd hsub hh
    obtain ⟨w, hwT, hwp⟩ := hV
    have hlperm : l.Perm vs := Work.PL.Shell.flagEnum_mem.mp hl
    have hl_toFinset : l.toFinset = Δ := by rw [toFinset_eq_of_perm hlperm, hvs]
    have hTΔ : T ⊆ Δ := hT₂.1
    have hwΔ : w ∈ Δ := hTΔ hwT
    have hw_mem_l : w ∈ l := by
      rw [← List.mem_toFinset, hl_toFinset]
      exact hwΔ
    obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem hw_mem_l
    have hm_lt : J.max' hJne < l.length :=
      Finset.mem_range.mp (hJ (Finset.max'_mem J hJne))
    -- `w` sits strictly after the maximal index of `J`
    have hjm : J.max' hJne < j := by
      by_contra hle
      have hle' : j ≤ J.max' hJne := le_of_not_gt hle
      apply hwp
      rw [Work.PL.Shell.prefAt, List.mem_toFinset, ← hj_eq]
      rw [List.mem_take_iff_getElem]
      exact ⟨j, Nat.lt_min.mpr ⟨by omega, hj_lt⟩, rfl⟩
    have hpos : 0 < l.length := lt_of_le_of_lt (Nat.zero_le _) hm_lt
    have hL : l.length - 1 < l.length := by omega
    constructor
    · refine ⟨l[l.length - 1]'hL, ?_, ?_⟩
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hL]
      · -- the last vertex must be in `T`
        by_contra hlast
        have hdΔ : l[l.length - 1]'hL ∈ Δ := by
          rw [← hl_toFinset, List.mem_toFinset]
          exact List.getElem_mem hL
        have hrkw : rk w < rk (l[l.length - 1]'hL) := hT w hwT _ hdΔ hlast
        have hjne : j ≠ l.length - 1 := by
          intro hje
          apply hlast
          have hv_eq_w : l[l.length - 1]'hL = w := by
            have h1 : l[l.length - 1]? = some (l[l.length - 1]'hL) :=
              List.getElem?_eq_getElem hL
            have h2 : l[j]? = some w := by
              rw [List.getElem?_eq_getElem hj_lt, hj_eq]
            have h3 : l[l.length - 1]? = l[j]? := by rw [hje]
            rw [h1, h2] at h3
            exact Option.some.inj h3
          rw [hv_eq_w]; exact hwT
        have hj_lt_d : j < l.length - 1 := by omega
        -- some ascent between `j` and the end, hence at an index `≤ max J`
        obtain ⟨s, hsj, hsd, hasc⟩ := Work.PL.Shell.exists_ascent
          (a := fun t => rk (l.getD t (default : PL.E N))) hj_lt_d (by
            rw [List.getD_eq_getElem l _ hj_lt, List.getD_eq_getElem l _ hL, hj_eq]
            exact hrkw)
        have hs_mem : s ∈ Work.PL.Shell.ascIdx rk l := by
          rw [Work.PL.Shell.ascIdx_mem]
          refine ⟨by omega, ?_⟩
          have e1 := List.getD_eq_getElem l (default : PL.E N) (show s < l.length by omega)
          have e2 := List.getD_eq_getElem l (default : PL.E N) (show s + 1 < l.length by omega)
          simp only [e1, e2] at hasc
          exact hasc
        have := Finset.le_max' J s (hsub hs_mem)
        omega
    · -- the last index is not in `J`
      intro hmem
      have hmax : J.max' hJne = l.length - 1 := by
        have h1 : l.length - 1 ≤ J.max' hJne := Finset.le_max' J _ hmem
        omega
      have : w ∈ Work.PL.Shell.prefAt l (J.max' hJne) := by
        rw [hmax, Work.PL.Shell.prefAt]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ l.length), List.take_length, hl_toFinset]
        exact hTΔ hwT
      exact hwp this
  · left
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hsub
    exact ⟨i, hi, hni⟩

end Work.PL.Sd1
