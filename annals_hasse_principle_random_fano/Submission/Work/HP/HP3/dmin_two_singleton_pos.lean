import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP3.one_le_detL_of_rk_two

namespace Work.HP.HP3

/-- The least determinant of a rank-`2` sublattice of `ℤ^{n+1}` containing `x` is positive.
Suggested route: with `n ≥ 1` pick `j` with `x` and `e_j` linearly independent; then
`L := Submodule.span ℤ {x, e_j}` has `rk L = 2` and contains `x`, so the defining set of
`dmin 2 {x}` is nonempty; every one of its elements is `detL L' ≥ 1` by
`Work.HP.HP3.one_le_detL_of_rk_two`, so `1 ≤ sInf = dmin 2 {x}` by `le_csInf`. -/
theorem dmin_two_singleton_pos {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) :
    0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
  classical
  -- A nonzero coordinate of `x`.
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (funext h)
  -- A second coordinate, distinct from `j` (possible since `n ≥ 1`).
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ j := by
    refine Fintype.exists_ne_of_one_lt_card ?_ j
    rw [Fintype.card_fin]; omega
  -- The standard basis vector `e_k`.
  let e : Fin (n + 1) → ℤ := fun i => if i = k then 1 else 0
  have hej : e j = 0 := by simp [e, Ne.symm hk]
  have hek : e k = 1 := by simp [e]
  -- `x` and `e_k` are `ℤ`-linearly independent.
  have hli : LinearIndependent ℤ ![x, e] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hj0 : a * x j = 0 := by
      have h := congr_fun hab j
      simpa [hej] using h
    have ha : a = 0 := (mul_eq_zero.mp hj0).resolve_right hj
    refine ⟨ha, ?_⟩
    have hk0 : a * x k + b = 0 := by
      have h := congr_fun hab k
      simpa [hek] using h
    rw [ha, zero_mul, zero_add] at hk0
    exact hk0
  -- The rank-`2` lattice spanned by `x` and `e_k`.
  let L : Submodule ℤ (Fin (n + 1) → ℤ) := Submodule.span ℤ (Set.range ![x, e])
  have hLrk : rk L = 2 := by
    unfold Work.HP.rk
    change Module.finrank ℤ (Submodule.span ℤ (Set.range ![x, e])) = 2
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hxL : x ∈ L := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  have hsub : ({x} : Set (Fin (n + 1) → ℤ)) ⊆ L := Set.singleton_subset_iff.mpr hxL
  -- The defining set of `dmin 2 {x}` is nonempty.
  have hne : ({D : ℝ | ∃ L' : Submodule ℤ (Fin (n + 1) → ℤ),
      rk L' = 2 ∧ ({x} : Set (Fin (n + 1) → ℤ)) ⊆ L' ∧ detL L' = D}).Nonempty :=
    ⟨detL L, L, hLrk, hsub, rfl⟩
  -- Every element of that set is `≥ 1`, hence so is its infimum.
  have h1 : (1 : ℝ) ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
    unfold Work.HP.dmin
    exact le_csInf hne (fun D hD => by
      obtain ⟨L', hrk', -, hdet⟩ := hD
      rw [← hdet]
      exact one_le_detL_of_rk_two L' hrk')
  linarith

end Work.HP.HP3
