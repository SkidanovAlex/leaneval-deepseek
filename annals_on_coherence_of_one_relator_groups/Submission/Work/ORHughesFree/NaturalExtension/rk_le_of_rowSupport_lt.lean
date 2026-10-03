import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_rowSupport

namespace Work.ORHughesFree.NaturalExtension

/-- If every row `i` of `M : Matrix (Fin N) (Fin K) R` with integer value `i ≥ c` is zero, then
`rk M ≤ max 0 c`.  (Rows live in `{0, …, N-1}`, so the supporting rows `i < c` number at most
`max 0 c`.) -/
theorem rk_le_of_rowSupport_lt {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {N K : ℕ} (c : ℤ) (M : Matrix (Fin N) (Fin K) R)
    (hM : ∀ (i : Fin N) (j : Fin K), c ≤ (i : ℤ) → M i j = 0) :
    rk.rk N K M ≤ ((max 0 c : ℤ) : ℝ) := by
  -- Split off the empty case `c ≤ 0`: then every index `i : Fin N` satisfies `c ≤ (i : ℤ)`,
  -- so `M = 0` and the bound reads `0 ≤ 0`.
  rcases lt_or_ge c 0 with hc | hnc
  · have hzero : M = 0 := by
      ext i j
      exact hM i j (le_trans (le_of_lt hc) (Int.natCast_nonneg i.val))
    rw [hzero, rk.rk_zero, max_eq_left (le_of_lt hc)]
    norm_num
  · -- Now `0 ≤ c`.  Either all `N` rows are potentially nonzero (`N ≤ c.toNat`), and then the
    -- trivial bound `rk M ≤ N` suffices, or the rows `i < c.toNat` -- at most `c.toNat ≤ c` of
    -- them -- already carry everything.
    rcases Nat.lt_or_ge c.toNat N with hlt | hge
    · have htN : c.toNat ≤ N := le_of_lt hlt
      have hle : rk.rk N K M ≤ (c.toNat : ℝ) := by
        refine rk_le_card_of_rowSupport rk
          (Fin.castLE htN) (Fin.castLE_injective htN) M ?_
        intro i hi j
        -- Rows outside the range of `Fin.castLE htN` have index `≥ c.toNat`, hence `≥ c`.
        have hge' : c.toNat ≤ i.val := by
          by_contra hcon
          exact hi ⟨⟨i.val, lt_of_not_ge hcon⟩, Fin.ext rfl⟩
        exact hM i j (by
          have h1 : (c.toNat : ℤ) ≤ (i : ℤ) := by exact_mod_cast hge'
          rwa [Int.toNat_of_nonneg hnc] at h1)
      have hRHS : ((max 0 c : ℤ) : ℝ) = (c.toNat : ℝ) := by
        rw [max_eq_right hnc, ← Int.cast_natCast (R := ℝ) c.toNat,
          Int.toNat_of_nonneg hnc]
      rw [hRHS]
      exact hle
    · have hle : rk.rk N K M ≤ (N : ℝ) := Work.ORHughesFree.RankAPI.rk_le_left rk M
      have hRHS : ((max 0 c : ℤ) : ℝ) = (c : ℝ) := by
        rw [max_eq_right hnc]
      have hNc : (N : ℝ) ≤ (c : ℝ) := by
        have h1 : (N : ℤ) ≤ c := by
          calc (N : ℤ) ≤ (c.toNat : ℤ) := by exact_mod_cast hge
            _ = c := Int.toNat_of_nonneg hnc
        exact_mod_cast h1
      rw [hRHS]
      exact le_trans hle hNc

end Work.ORHughesFree.NaturalExtension
