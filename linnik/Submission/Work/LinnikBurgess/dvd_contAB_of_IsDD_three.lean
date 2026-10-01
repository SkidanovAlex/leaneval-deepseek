import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.castHom_ddDefectK_three
import Submission.Work.LinnikBurgess.esymm_eq_of_three_powerSums

namespace Work.LinnikBurgess

/-- In `ZMod p`, equality of the reductions of two integers forces `p` to divide the natAbs of
their difference. -/
private lemma dvd_natAbs_sub_of_intCast_eq {p : ℕ} {m n : ℤ}
    (h : (m : ZMod p) = (n : ZMod p)) : p ∣ (m - n).natAbs := by
  have h' : (p : ℤ) ∣ n - m := (ZMod.intCast_eq_intCast_iff_dvd_sub m n p).mp h
  have h'' : ((p : ℤ)).natAbs ∣ (n - m).natAbs := Int.natAbs_dvd_natAbs.mpr h'
  rw [Int.natAbs_natCast] at h''
  rwa [show m - n = -(n - m) by ring, Int.natAbs_neg]

/-- **A DD class with vanishing third power-sum defect forces `p ∣ contAB a b`.**

`IsDD p e a b r` supplies a common residue `r` at which the two triples of inverses
`(r + a_l)^{-1}`, `(r + b_l)^{-1}` are all defined and have equal first and second power sums
modulo `p`.  The extra hypothesis `p ∣ (ddDefectK p e a b r 3).val` says the third power sums agree
modulo `p` as well.  Newton's identities (in the field `ZMod p`, where `2` and `3` are invertible
because `p ≥ 5`) then force the elementary symmetric functions `e₁, e₂, e₃` of the two triples to
agree modulo `p`; since `contAB a b` is their content `gcd(|e₁(a)-e₁(b)|, gcd(|e₂(a)-e₂(b)|,
|e₃(a)-e₃(b)|))`, this says exactly `p ∣ contAB a b`.

The hypothesis `p^2 ∣ ddDefect` carried by `IsDD` is not needed: the first and second power-sum
identities of `IsDD` are already congruences modulo `p`. -/
theorem dvd_contAB_of_IsDD_three {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hdd : Work.LinnikBurgess.IsDD p e a b r)
    (h3 : p ∣ (Work.LinnikBurgess.ddDefectK p e a b r 3).val) :
    p ∣ Work.LinnikBurgess.contAB a b := by
  -- the modulus `p^e` is a genuine prime power, so `p ∣ p^e`
  have hm : p ∣ p ^ e := dvd_pow_self p (by omega)
  -- unpack `IsDD`: units, and the first two power-sum identities mod `p`
  obtain ⟨hunit, h1, h2, _⟩ := hdd
  -- the third power-sum identity mod `p`, transported along `ZMod (p^e) → ZMod p`
  have hcast : ZMod.castHom hm (ZMod p) (ddDefectK p e a b r 3) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    exact h3
  have h3eq := castHom_ddDefectK_three hm a b r hunit
  rw [hcast] at h3eq
  have h3' : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 3)
      = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 3) := sub_eq_zero.mp h3eq.symm
  -- `2` and `3` are invertible in `ZMod p` because `p ≥ 5`
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      intro hd
      rw [ZMod.natCast_eq_zero_iff] at hd
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
      omega
    exact h
  have h3ne : (3 : ZMod p) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod p) ≠ 0 := by
      intro hd
      rw [ZMod.natCast_eq_zero_iff] at hd
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hd
      omega
    exact h
  -- Newton: equal power sums of order `1,2,3` ⟹ equal elementary symmetric functions
  have hesymm := esymm_eq_of_three_powerSums h2ne h3ne
    (fun l : Fin 3 => ((a l : ℕ) : ZMod p)) (fun l : Fin 3 => ((b l : ℕ) : ZMod p))
    r hunit h1 h2 h3'
  -- convert each of the three congruences to a divisibility of the content
  rw [contAB]
  refine Nat.dvd_gcd ?_ (Nat.dvd_gcd ?_ ?_)
  · refine dvd_natAbs_sub_of_intCast_eq ?_
    simp only [esymm3]
    push_cast
    exact hesymm.1
  · refine dvd_natAbs_sub_of_intCast_eq ?_
    simp only [esymm3]
    push_cast
    exact hesymm.2.1
  · refine dvd_natAbs_sub_of_intCast_eq ?_
    simp only [esymm3]
    push_cast
    exact hesymm.2.2

end Work.LinnikBurgess
