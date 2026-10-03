import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_colSupport

namespace Work.ORHughesFree.NaturalExtension

/-- The range of `i ↦ (Finset.equivFin S).symm i`, viewed back in the ambient type, is exactly
the finset `S`. -/
theorem range_equivFin_symm_coe {K : ℕ} (S : Finset (Fin K)) :
    Set.range (fun i : Fin S.card => ((Finset.equivFin S).symm i : Fin K)) = ↑S := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Finset.equivFin S).symm i).2
  · intro hx
    exact ⟨(Finset.equivFin S) ⟨x, hx⟩, by simp⟩

/-- If every column of `M` outside a finite set `S` of column indices vanishes, then
`rk M ≤ |S|`.

The map `i ↦ (Finset.equivFin S).symm i` is an injection `Fin S.card → Fin K` whose range is
exactly `S`; the claim is then `rk_le_card_of_colSupport` applied to that injection. -/
theorem rk_le_card_of_colSupport' {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {N K : ℕ} (S : Finset (Fin K)) (M : Matrix (Fin N) (Fin K) R)
    (hM : ∀ j, j ∉ S → ∀ i, M i j = 0) : rk.rk N K M ≤ (S.card : ℝ) := by
  have hinj : Function.Injective (fun i : Fin S.card => ((Finset.equivFin S).symm i : Fin K)) := by
    intro a b h
    exact (Finset.equivFin S).symm.injective (Subtype.ext h)
  exact rk_le_card_of_colSupport rk (fun i : Fin S.card => ((Finset.equivFin S).symm i : Fin K))
    hinj M (fun j hj i => hM j (fun hjs => hj (by rw [range_equivFin_symm_coe]; exact hjs)) i)

/-- The number of columns `j : Fin K` whose integer value satisfies `c < (j : ℤ)` is at most
`max 0 (K - 1 - c)`.  These are the columns `j ∈ {c+1, …, K-1}`, of which there are at most
`K - 1 - c` when this is non-negative. -/
theorem card_filter_col_gt_le_max (c : ℤ) (K : ℕ) :
    ((Finset.univ.filter (fun j : Fin K => ¬ ((j : ℤ) ≤ c))).card : ℤ) ≤
      max 0 ((K : ℤ) - 1 - c) := by
  set S : Finset (Fin K) := Finset.univ.filter (fun j => ¬ ((j : ℤ) ≤ c)) with hS
  set m : ℤ := (K : ℤ) - 1 - c with hm
  rcases lt_or_ge (0 : ℤ) m with hmpos | hm0
  · -- `0 < m`: the supporting columns inject into `Fin m.toNat` via `j ↦ j - (c+1)`.
    set d : ℕ := (c + 1).toNat with hd
    have hd_cast : (d : ℤ) = max 0 (c + 1) := by
      rw [hd]; exact (Int.toNat_eq_max (c + 1)).trans (max_comm _ _)
    have hmm : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
    have hbound : K - 1 - d < m.toNat := by
      have h1 : c + 1 ≤ (d : ℤ) := by rw [hd_cast]; exact le_max_right _ _
      omega
    have hmem : ∀ j ∈ S, d ≤ j.val := by
      intro j hj
      rw [hS, Finset.mem_filter] at hj
      have hj2 : c < (j : ℤ) := not_le.mp hj.2
      have h1 : 0 ≤ (j : ℤ) := Int.natCast_nonneg j.val
      have h2 : c + 1 ≤ (j : ℤ) := by omega
      have h3 : max 0 (c + 1) ≤ (j : ℤ) := max_le h1 h2
      have : (d : ℤ) ≤ (j.val : ℤ) := by rw [hd_cast]; exact h3
      exact_mod_cast this
    have hcard : S.card ≤ m.toNat := by
      have hle := Finset.card_le_card_of_injOn (fun j : Fin K => (⟨j.val - d, by
            have := hbound
            have hjle : j.val ≤ K - 1 := by omega
            omega⟩ : Fin m.toNat))
        (fun j _ => Finset.mem_univ _)
        (fun j hj j' hj' heq => by
          have h1 := hmem j hj
          have h2 := hmem j' hj'
          have hsub : j.val - d = j'.val - d := by simpa using congrArg Fin.val heq
          have : j.val = j'.val := by omega
          exact Fin.ext this)
      simpa using hle
    rw [max_eq_right (le_of_lt hmpos)]
    calc (S.card : ℤ) ≤ (m.toNat : ℤ) := by exact_mod_cast hcard
      _ = m := hmm
  · -- `m ≤ 0`: there is no supporting column at all.
    have hEmpty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [hS, Finset.mem_filter] at hj
      have hj2 : c < (j : ℤ) := not_le.mp hj.2
      have hj3 : (j : ℤ) ≤ (K : ℤ) - 1 := by
        have := j.isLt; omega
      omega
    rw [hEmpty, Finset.card_empty]
    exact le_max_left _ _

/-- If every column `j` of `M : Matrix (Fin N) (Fin K) R` with integer value `j ≤ c` is zero, then
`rk M ≤ max 0 (K - 1 - c)`.  (Columns live in `{0, …, K-1}`, so the supporting columns `j > c`
number at most `max 0 (K-1-c)`.) -/
theorem rk_le_of_colSupport_gt {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {N K : ℕ} (c : ℤ) (M : Matrix (Fin N) (Fin K) R)
    (hM : ∀ (i : Fin N) (j : Fin K), (j : ℤ) ≤ c → M i j = 0) :
    rk.rk N K M ≤ ((max 0 ((K : ℤ) - 1 - c) : ℤ) : ℝ) := by
  -- `S` is the set of columns supported by the hypothesis `hM`.
  set S : Finset (Fin K) := Finset.univ.filter (fun j => ¬ ((j : ℤ) ≤ c)) with hS
  -- (SMat2)-style bound: `rk M` is at most the number of supporting columns.
  have h1 : rk.rk N K M ≤ (S.card : ℝ) := by
    refine rk_le_card_of_colSupport' rk S M ?_
    intro j hj i
    exact hM i j
      (by by_contra h; exact hj (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  -- The supporting columns are exactly `{c+1, …, K-1}`, of which there are at most `max 0 (K-1-c)`.
  have h2 : (S.card : ℝ) ≤ ((max 0 ((K : ℤ) - 1 - c) : ℤ) : ℝ) := by
    rw [hS]
    have hh := card_filter_col_gt_le_max c K
    exact_mod_cast hh
  exact le_trans h1 h2

end Work.ORHughesFree.NaturalExtension
