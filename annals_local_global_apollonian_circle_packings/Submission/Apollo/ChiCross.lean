/-
Cross-coordinate identities for the per-quadruple common χ₂ value.
-/
import Submission.Apollo.KR
import Submission.Apollo.Partner
import Submission.Apollo.PartnerEven
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Submission.Apollo.CLocal
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped NumberTheorySymbols

namespace Apollo

/-- Odd–odd reciprocity: for odd coordinates o₁, o₂ both ≡ 1 mod 4 with at
least one positive, the χ₂ value is symmetric: pairChi o₁ o₂ = pairChi o₂ o₁.
(In the Apollonian packing all odd values are ≡ 1 mod 4 and any coprime pair
of odd values contains a positive member, so this covers every coprime
odd–odd pair there.) -/
lemma pairChi_odd_odd_symm {o₁ o₂ : ℤ} (h₁ : o₁ % 4 = 1) (h₂ : o₂ % 4 = 1)
    (hpos : 0 < o₁ ∨ 0 < o₂) : pairChi o₁ o₂ = pairChi o₂ o₁ := by
  unfold pairChi
  have ho₁odd : Odd o₁.natAbs :=
    Commons.NumberTheory.Int.natAbs_odd_of_emod_two (Commons.NumberTheory.Int.emod_two_of_four_one h₁)
  have ho₂odd : Odd o₂.natAbs :=
    Commons.NumberTheory.Int.natAbs_odd_of_emod_two (Commons.NumberTheory.Int.emod_two_of_four_one h₂)
  rw [ksym_odd o₂ ho₁odd, ksym_odd o₁ ho₂odd]
  exact Commons.NumberTheory.JacobiSymbol.odd_odd_symm h₁ h₂ hpos

/-- an integer ≡ 5 mod 8 has odd absolute value. -/
lemma mod8five_natAbs_odd {o : ℤ} (h : o % 8 = 5) : Odd o.natAbs := by
  have h2 : o % 2 = 1 := by omega
  exact Commons.NumberTheory.Int.natAbs_odd_of_emod_two h2

/-- (2 | |o|) = −1 for o ≡ 5 mod 8. -/
lemma jacobi_two_neg_of_mod8_five {o : ℤ} (h : o % 8 = 5) : jacobiSym 2 o.natAbs = -1 := by
  rcases Commons.NumberTheory.Int.natAbs_mod8_of_mod8_five h with h3 | h5
  · exact Commons.NumberTheory.JacobiSymbol.two_neg_of_mod8_three_five (Or.inl h3)
  · exact Commons.NumberTheory.JacobiSymbol.two_neg_of_mod8_three_five (Or.inr h5)

/-- (o | 2) = −1 for o ≡ 5 mod 8. -/
lemma kronTwo_neg_of_mod8_five {o : ℤ} (h : o % 8 = 5) : kronTwo o = -1 := by
  unfold kronTwo
  have h2 : o % 2 = 1 := by omega
  have hnot1 : ¬ o % 8 = 1 := by omega
  have hnot7 : ¬ o % 8 = 7 := by omega
  rw [h2]
  simp [hnot1, hnot7]

/-- an odd coordinate o makes pairChi o e equal to the Jacobi symbol J(e | |o|). -/
lemma pairChi_odd_even_of_five {o : ℤ} (ho5 : o % 8 = 5) (e : ℤ) :
    pairChi o e = jacobiSym e o.natAbs := by
  unfold pairChi
  exact ksym_odd e (mod8five_natAbs_odd ho5)

/-- the absolute value of a negative integer is its negation. -/
lemma natAbs_eq_neg {x : ℤ} (h : x < 0) : (x.natAbs : ℤ) = -x := by
  rcases Int.natAbs_eq x with hx | hx
  · exfalso
    omega
  · omega

/-- Odd–even (mixed) reciprocity: pairChi o e = pairChi e o for coprime
o ≡ 5 mod 8 and e (any parity), provided at least one of o, e is positive.
In the Apollonian packing negative odd values are ≡ 0 mod 3, so every coprime
mixed co-occurring pair has a positive member and this applies. -/
lemma pairChi_mixed {o e : ℤ} (ho5 : o % 8 = 5)
    (hcop : o.gcd e = 1) (hpos : 0 < o ∨ 0 < e) :
    pairChi o e = pairChi e o := by
  have hoo : Odd o.natAbs := mod8five_natAbs_odd ho5
  have ho4 : o % 4 = 1 := by omega
  have hwf : WellFounded (fun x y : ℤ => x.natAbs < y.natAbs) :=
    (measure (fun x : ℤ => x.natAbs)).wf
  induction e using hwf.induction with
  | h e ih =>
    by_cases he0 : e = 0
    · exfalso
      have hno : o.natAbs ≠ 1 := by
        rcases Commons.NumberTheory.Int.natAbs_mod8_of_mod8_five ho5 with h3 | h5 <;> omega
      have hg : o.natAbs = 1 := by
        simpa [he0, Int.gcd_zero_right] using hcop
      exact hno hg
    · by_cases heven : 2 ∣ e
      · rcases heven with ⟨k, hk⟩
        have hk0 : k ≠ 0 := by
          intro hk0; subst k; simp at hk; exact he0 hk
        have hlt : k.natAbs < e.natAbs := by
          rw [hk]
          simp [Int.natAbs_mul]
          have hx : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
          omega
        have hcopk : o.gcd k = 1 := by
          rcases Int.natAbs_eq k with hk' | hk'
          · rw [hk] at hcop
            rw [hk'] at hcop
            apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_left (m := k.natAbs) (n := 2)
            simpa [mul_comm] using hcop
          · rw [hk] at hcop
            rw [hk'] at hcop
            have hsign : o.gcd (2 * (k.natAbs : ℤ)) = 1 := by
              rw [Int.gcd_eq_natAbs] at hcop ⊢
              simpa [Int.natAbs_mul] using hcop
            apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_left (m := k.natAbs) (n := 2)
            simpa [mul_comm] using hsign
        have hposk : 0 < o ∨ 0 < k := by
          rcases hpos with ho | he
          · exact Or.inl ho
          · right; omega
        have ihk : pairChi o k = pairChi k o := ih k hlt hcopk hposk
        calc
          pairChi o e = -pairChi o k := by
            rw [hk]
            rw [pairChi_odd_even_of_five ho5 (2 * k)]
            rw [jacobiSym.mul_left]
            rw [jacobi_two_neg_of_mod8_five ho5]
            rw [← pairChi_odd_even_of_five ho5 k]
            ring
          _ = -pairChi k o := by rw [ihk]
          _ = pairChi e o := by
            symm
            rw [hk]
            unfold pairChi
            have hkpos : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk0
            calc
              ksym o (2 * k).natAbs = ksym o (2 * k.natAbs) := by
                simp [Int.natAbs_mul]
              _ = ksym o k.natAbs * kronTwo o := by
                exact ksym_even_mul o (b := k.natAbs) hkpos
              _ = -(ksym o k.natAbs) := by rw [kronTwo_neg_of_mod8_five ho5]; ring
      · -- e odd: base
        have hodd : Odd e.natAbs := by
          have hne : e % 2 ≠ 0 := by
            intro hz
            exact heven (Int.dvd_iff_emod_eq_zero.mpr hz)
          have he1 : e % 2 = 1 := by
            rcases Int.emod_two_eq_zero_or_one e with h | h
            · exact False.elim (hne h)
            · exact h
          exact Commons.NumberTheory.Int.natAbs_odd_of_emod_two he1
        rw [pairChi_odd_even_of_five ho5 e]
        unfold pairChi
        rw [ksym_odd o hodd]
        have hsign : jacobiSym e o.natAbs = jacobiSym e.natAbs o.natAbs := by
          by_cases hepos : 0 ≤ e
          · conv_lhs => rw [← Int.natAbs_of_nonneg hepos]
          · have hneg : e < 0 := by omega
            have ho_pos : 0 < o := by
              rcases hpos with ho | he
              · exact ho
              · exfalso
                omega
            have hcast : (e.natAbs : ℤ) = -e := natAbs_eq_neg hneg
            have he_neg : e = -((e.natAbs : ℤ)) := by omega
            conv_lhs => rw [he_neg]
            have ho1 : o.natAbs % 4 = 1 := by
              have hcasto : (o.natAbs : ℤ) = o := Int.natAbs_of_nonneg (le_of_lt ho_pos)
              have ho4 : (o : ℤ) % 4 = 1 := by omega
              rw [← hcasto] at ho4
              have hrel : (↑(o.natAbs % 4 : ℕ) : ℤ) = (o.natAbs : ℤ) % (4 : ℤ) := by
                simpa using (Int.natCast_emod (m := o.natAbs) (n := 4))
              rw [← hrel] at ho4
              exact_mod_cast ho4
            rw [Commons.NumberTheory.JacobiSymbol.neg_eq_one_mod_four ho1]
        rw [hsign]
        exact (Commons.NumberTheory.JacobiSymbol.mixed_recip ho4 hodd).symm


/-- Even-coordinate partner consistency: for an even coordinate x ≡ 0 mod 4
with coprime odd partners y₁, y₂ in the same Descartes quadruple (whose
fourth coordinate z is also ≡ 0 mod 4), the χ₂ value does not depend on the
partner: pairChi x y₁ = pairChi x y₂. -/
lemma even_partner_consistency {x y₁ y₂ z : ℤ}
    (hD : (x + y₁ + y₂ + z) ^ 2 = 2 * (x ^ 2 + y₁ ^ 2 + y₂ ^ 2 + z ^ 2))
    (hx : x % 4 = 0) (hz : z % 4 = 0)
    (hg₁ : y₁.gcd x = 1) (hg₂ : y₂.gcd x = 1) :
    pairChi x y₁ = pairChi x y₂ := by
  have hx2 : 2 ∣ x := by
    have : x % 2 = 0 := by omega
    exact Int.dvd_iff_emod_eq_zero.mpr this
  have hy1 : y₁ % 2 = 1 := odd_mod_of_coprime_even hx2 hg₁
  have hy2 : y₂ % 2 = 1 := odd_mod_of_coprime_even hx2 hg₂
  have h8 : y₁ % 8 = y₂ % 8 := odd_partners_cong_mod8 hD hx hy1 hy2 hz
  have hk := ksym_partner_of_coprime hD hg₁ hg₂ h8 (k := x.natAbs) (dvd_rfl)
  unfold pairChi
  exact hk


end Apollo
