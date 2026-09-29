import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_helpers

namespace Work.Haupt

theorem neg_part_tsum {q z : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    (∑' n : ℕ, sfTerm q z m (-((n : ℤ) + 1))) = Bfun q z m := by
  -- The negative-index terms all have index `-k` with `k ≥ 1`; those with `k ≥ m+1` vanish.
  have hzero : ∀ n : ℕ, n ∉ Finset.range m → sfTerm q z m (-((n : ℤ) + 1)) = 0 := by
    intro n hn
    have h : sfTerm q z m (-(((n + 1 : ℕ)) : ℤ)) = 0 :=
      sfTerm_neg_eq_zero hq (by simpa [Finset.mem_range] using hn)
    have hcast : (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rwa [hcast] at h
  rw [tsum_eq_sum hzero, Bfun]
  -- Reindex `Finset.Icc 1 m` as the image of `Finset.range m` under `n ↦ n + 1`.
  have hIcc : Finset.Icc 1 m = (Finset.range m).image (fun n => n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega
  have hinj : Set.InjOn (fun n : ℕ => n + 1) (↑(Finset.range m) : Set ℕ) :=
    fun a _ b _ h => Nat.succ.inj h
  rw [hIcc, Finset.sum_image hinj]
  -- Term by term, `sfTerm_neg_eq` gives the explicit value appearing in `Bfun`.
  apply Finset.sum_congr rfl
  intro n hn
  have hk : n + 1 ≤ m := by simpa [Finset.mem_range] using hn
  have h1 := sfTerm_neg_eq (q := q) (z := z) (m := m) (k := n + 1) hk
  have hcast : (-(((n + 1 : ℕ)) : ℤ)) = -((n : ℤ) + 1) := by push_cast; ring
  conv_lhs => rw [← hcast]
  exact h1

end Work.Haupt
