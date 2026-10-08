import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.DSTR.DihHelp.cyclicSqOne
import Submission.Work.DSTR.DihHelp.dih_decomp_reflection
import Submission.Work.DSTR.DihHelp.dih_sr_conj_rot

namespace Work.CORE2A

/-- The center of a dihedral group `DihedralGroup k` with `k ≥ 3` has at most two elements:
it is trivial when `k` is odd (and `k ≠ 1`, which `k ≥ 3` gives) and is `⟨r (k/2)⟩ ≅ C₂`
when `k` is even.  This is Mathlib's `DihedralGroup.center_eq_bot_of_odd_ne_one` /
`DihedralGroup.center_eq_closure_of_even_ne_two`, together with the computation
`orderOf (r (k/2)) ∣ 2`. -/
lemma natCard_center_dihedralGroup_le_two (k : ℕ) (hk : 3 ≤ k) :
    Nat.card (Subgroup.center (DihedralGroup k)) ≤ 2 := by
  rcases Nat.even_or_odd k with he | ho
  · rw [DihedralGroup.center_eq_closure_of_even_ne_two he (by omega), Nat.card_zpowers]
    apply Nat.le_of_dvd (by norm_num)
    rw [orderOf_dvd_iff_pow_eq_one, DihedralGroup.r_pow]
    have h1 : ((k / 2 : ℕ) : ZMod k) * ((2 : ℕ) : ZMod k) = 0 := by
      rw [← Nat.cast_mul, Nat.div_two_mul_two_of_even he, ZMod.natCast_self]
    rw [h1, DihedralGroup.r_zero]
  · rw [DihedralGroup.center_eq_bot_of_odd_ne_one ho (by omega), Subgroup.card_bot]
    norm_num

theorem center_card_le_two_of_le_dihedral {m : ℕ} [NeZero m] (H : Subgroup (DihedralGroup m))
    (hnc : ¬ IsCyclic ↥H) (hH : 5 ≤ Nat.card H) :
    Nat.card (Subgroup.center ↥H) ≤ 2 := by
  -- Any subgroup of a finite dihedral group is cyclic or dihedral.
  rcases Work.RED.DihedralSubgroup m H with hcyc | ⟨k, ⟨e⟩⟩
  · exact absurd hcyc hnc
  · -- `H ≃* DihedralGroup k`, and `|H| ≥ 5` forces `k ≥ 3`.
    have hcard : Nat.card ↥H = Nat.card (DihedralGroup k) := Nat.card_congr e
    rw [hcard, DihedralGroup.nat_card] at hH
    have hk : 3 ≤ k := by omega
    -- An isomorphism carries the center to the center, so it suffices to bound the latter.
    calc Nat.card (Subgroup.center ↥H)
        = Nat.card (Subgroup.center (DihedralGroup k)) := Nat.card_congr (Subgroup.centerCongr e)
      _ ≤ 2 := natCard_center_dihedralGroup_le_two k hk

end Work.CORE2A
