import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.exists_rk_two
import Submission.Work.HP.MDEstimates.detL_one_le

namespace Work.FM

open Work.HP

/-- The requested lemma: a primitive integer vector `x` (in `ℤ^{n+1}` with `n ≥ 1`) lies in some
rank-`2` sublattice of `ℤ^{n+1}` (nonemptiness of the defining set of `dmin`), and every integral
lattice has `detL ≥ 1`; hence `𝔡₂(x) = dmin 2 {x} ≥ 1`. -/
theorem dmin_two_singleton_ge_one (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) :
    1 ≤ Work.HP.dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
  classical
  -- a primitive vector is nonzero
  have hx0 : x ≠ 0 := by
    intro h
    have hg : Finset.univ.gcd x = 0 := by
      rw [Finset.gcd_eq_zero_iff]
      intro i _
      simp [h]
    rw [IsPrim] at hx
    rw [hg] at hx
    exact one_ne_zero hx.symm
  -- a nonzero vector in ≥ 2 coordinates lies in a rank-two sublattice
  obtain ⟨L, hLrk, hxL⟩ :=
    Lat.exists_rk_two x hx0 (by simp only [Fintype.card_fin]; omega)
  unfold Work.HP.dmin
  refine le_csInf ⟨detL L, L, hLrk, ?_, rfl⟩ ?_
  · exact Set.singleton_subset_iff.mpr hxL
  · rintro D ⟨L', -, -, rfl⟩
    exact MDEstimates.detL_one_le L'

end Work.FM
