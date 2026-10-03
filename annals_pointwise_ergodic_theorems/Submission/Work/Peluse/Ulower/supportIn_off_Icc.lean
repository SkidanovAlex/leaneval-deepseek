import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

/-- Membership in the symmetric interval `[-L, L]`, in terms of `Int.natAbs`.  This is the
`Finset`-form of the interval which the workspace's `symIcc` abbreviates, stated for
`Finset.Icc (-(L : ℤ)) (L : ℤ)` itself so that the lemma applies verbatim to the set appearing in
`SupportIn`. -/
lemma mem_Icc_neg_natAbs_iff {L : ℕ} {x : ℤ} :
    x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) ↔ x.natAbs ≤ L := by
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'

/-- A function supported in `L` (i.e. vanishing for `L < |x|`) vanishes off the interval
`[-L, L]`: if `x ∉ [-L, L]` then `L < x.natAbs`, so `F x = 0` by the support hypothesis. -/
theorem supportIn_off_Icc {L : ℕ} {F : ℤ → ℂ} (hF : Work.Peluse.SupportIn F L) :
    ∀ x : ℤ, x ∉ Finset.Icc (-(L : ℤ)) (L : ℤ) → F x = 0 := by
  intro x hx
  exact hF x (lt_of_not_ge fun hle => hx (mem_Icc_neg_natAbs_iff.mpr hle))

end Work.Peluse.Ulower
