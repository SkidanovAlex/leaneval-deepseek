import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Peel

/-- Membership in the symmetric interval `symIcc R = [-R, R]` of integers is the condition
`|x| ≤ R`. -/
private lemma mem_symIcc_iff_natAbs_le {R : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc R ↔ x.natAbs ≤ R := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : (x.natAbs : ℤ) ≤ (R : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr ⟨h1, h2⟩
    exact_mod_cast h
  · intro h
    have h' : (x.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h'
    exact abs_le.mp h'

/-- The `ℓ²` mass of a function `h : ℤ → ℝ` supported in `[-N, N]`, computed as a `tsum`, equals
its finite sum over the (possibly larger) symmetric interval `[-R, R]`, for any `R ≥ N`. -/
theorem tsum_sq_eq_sum_symIcc {N R : ℕ} (h : ℤ → ℝ) (hNR : N ≤ R)
    (hsupp : ∀ x : ℤ, N < x.natAbs → h x = 0) :
    ∑' x : ℤ, (h x) ^ 2 = ∑ x ∈ Work.Peluse.symIcc R, (h x) ^ 2 := by
  rw [tsum_eq_sum (s := Work.Peluse.symIcc R)]
  intro x hx
  have hle : R < x.natAbs := by
    have hcon : ¬ x.natAbs ≤ R := fun h => hx (mem_symIcc_iff_natAbs_le.mpr h)
    exact not_le.mp hcon
  rw [hsupp x (lt_of_le_of_lt hNR hle)]
  norm_num

end Work.Peluse.Peel
