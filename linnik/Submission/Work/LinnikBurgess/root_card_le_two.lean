import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

namespace Work.LinnikBurgess

/-- The congruence `p ∣ linCoeff β γ δ r` is a nonzero quadratic condition mod `p`:
at most two of the residues `0, …, p-1` can satisfy it.

The proof is the elementary three-root argument.  If `a ≠ b` are two roots in `[0, p)`,
then `p ∣ linCoeff a - linCoeff b = (a - b) * (2γ + 3δ(a+b))`, and `p ∤ (a - b)` because
`0 < |a - b| < p`; primeness of `p` therefore forces `p ∣ 2γ + 3δ(a+b)`.  Applying this
to the pairs `(x,y)` and `(x,z)` of three distinct roots and subtracting gives
`p ∣ 3δ(y - z)`, whence `p ∣ y - z` since `p ∤ 3δ`, which is impossible as before. -/
theorem root_card_le_two (p : ℕ) [Fact p.Prime] (β γ δ : ℤ) (h3δ : ¬ (p : ℤ) ∣ 3 * δ) :
    ((Finset.range p).filter (fun r => (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r)).card ≤ 2 := by
  classical
  have hp : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  -- `p` does not divide a nonzero difference of two elements of `[0, p)`.
  have not_dvd_sub : ∀ (a b : ℕ), a < p → b < p → a ≠ b → ¬ (p : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := by
    intro a b ha hb hab h
    have hcast : ((a : ZMod p)) = ((b : ZMod p)) := by
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a:ℤ) - (b:ℤ)) p).mpr h
      push_cast at h1
      exact sub_eq_zero.mp h1
    have h2 := (ZMod.natCast_eq_natCast_iff a b p).mp hcast
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact hab h2
  -- differencing two roots at `a ≠ b` in `[0, p)`.
  have dvd_shift : ∀ (a b : ℕ), a < p → b < p → a ≠ b →
      (p:ℤ) ∣ linCoeff β γ δ a → (p:ℤ) ∣ linCoeff β γ δ b →
      (p:ℤ) ∣ 2*γ + 3*δ*((a:ℤ) + (b:ℤ)) := by
    intro a b ha hb hab hra hrb
    have hdvd : (p:ℤ) ∣ linCoeff β γ δ a - linCoeff β γ δ b := dvd_sub hra hrb
    have hfac : linCoeff β γ δ a - linCoeff β γ δ b
        = ((a:ℤ) - (b:ℤ)) * (2*γ + 3*δ*((a:ℤ) + (b:ℤ))) := by
      simp only [linCoeff]; ring
    rw [hfac] at hdvd
    rcases hp.dvd_mul.mp hdvd with h1 | h2
    · exact absurd h1 (not_dvd_sub a b ha hb hab)
    · exact h2
  set S := (Finset.range p).filter (fun r => (p:ℤ) ∣ linCoeff β γ δ r) with hS
  by_contra hcon
  rw [not_le] at hcon
  -- three distinct roots would live in a 3-element subset
  obtain ⟨t, htS, htcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  rw [Finset.card_eq_three] at htcard
  obtain ⟨x, y, z, hxy, hxz, hyz, htxyz⟩ := htcard
  have hxS : x ∈ S := htS (by rw [htxyz]; simp)
  have hyS : y ∈ S := htS (by rw [htxyz]; simp)
  have hzS : z ∈ S := htS (by rw [htxyz]; simp)
  have mem : ∀ {r : ℕ}, r ∈ S → r < p ∧ (p:ℤ) ∣ linCoeff β γ δ r := by
    intro r hr
    rw [hS] at hr
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  obtain ⟨hxlt, hxroot⟩ := mem hxS
  obtain ⟨hylt, hyroot⟩ := mem hyS
  obtain ⟨hzlt, hzroot⟩ := mem hzS
  have hxy' := dvd_shift x y hxlt hylt hxy hxroot hyroot
  have hxz' := dvd_shift x z hxlt hzlt hxz hxroot hzroot
  have hdiff : (p:ℤ) ∣ 3*δ*((y:ℤ) - (z:ℤ)) := by
    have heq : (2*γ + 3*δ*((x:ℤ) + (y:ℤ))) - (2*γ + 3*δ*((x:ℤ) + (z:ℤ)))
        = 3*δ*((y:ℤ) - (z:ℤ)) := by ring
    rw [← heq]
    exact dvd_sub hxy' hxz'
  have hyz' : (p:ℤ) ∣ ((y:ℤ) - (z:ℤ)) := by
    rcases hp.dvd_mul.mp hdiff with hh | hh
    · exact absurd hh h3δ
    · exact hh
  exact not_dvd_sub y z hylt hzlt hyz hyz'

end Work.LinnikBurgess
