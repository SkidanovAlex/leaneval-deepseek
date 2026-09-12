/-
The non-stuck S-move step of the χ₂ constancy proof.

If an S-move at coordinate i produces the new value u i = 2·(sum of the other
three) − v i which is coprime to an old coordinate u j = v j, and the old
coordinate has a coprime partner v k among the other old coordinates, then the
per-quadruple partner-consistency lemmas (Partner, PartnerEven) applied inside
the new quadruple, together with quadratic reciprocity (ChiCross), show that
the new pair also has pairChi = -1.  (This closes the induction step of
"every coprime co-occurring pair has pairChi = -1" except for the "stuck"
configurations, which are handled by crack-family detours elsewhere.)
-/
import Submission.Apollo.Parity
import Submission.Apollo.Partner
import Submission.Apollo.PartnerEven
import Submission.Apollo.ChiCross
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
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- a value ≡ 5 mod 8 is odd. -/
lemma odd_of_mod8_five {t : ℤ} (h : t % 8 = 5) : ¬ 2 ∣ t := by
  intro h2
  have h0 : t % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2
  have h1 : t % 2 = 1 := by omega
  omega

/-- a value ≡ 5 mod 8 is ≡ 1 mod 4. -/
lemma mod4_one_of_mod8_five {t : ℤ} (h : t % 8 = 5) : t % 4 = 1 := by omega

/-- a value ≡ 5 mod 8 has |t| ≠ 1 (used to exclude zero partners). -/
lemma natAbs_ne_one_of_mod8_five {t : ℤ} (h : t % 8 = 5) : t.natAbs ≠ 1 := by
  rcases Commons.NumberTheory.Int.natAbs_mod8_of_mod8_five h with h3 | h5
  · intro h1; omega
  · intro h1; omega

/-- a coprime partner of a 5-mod-8 value is nonzero. -/
lemma not_zero_of_coprime_mod8five {w t : ℤ} (ht : t % 8 = 5) (h : w.gcd t = 1) : w ≠ 0 := by
  intro hw0
  subst w
  have hg : t.natAbs = 1 := by simpa using h
  exact natAbs_ne_one_of_mod8_five ht hg

/-- At most one negative gives positivity for a coprime pair of nonzero values. -/
lemma positive_of_coprime_at_most_one_neg {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hneg : ¬ (a < 0 ∧ b < 0)) : 0 < a ∨ 0 < b := by
  by_contra h
  push_neg at h
  have ha0 : a < 0 := by omega
  have hb0 : b < 0 := by omega
  exact hneg ⟨ha0, hb0⟩

/-- an odd residue from the disjunction (≡5 mod 8 or even). -/
lemma mod8_five_of_not_even {x : ℤ} (hx : x % 8 = 5 ∨ 2 ∣ x) (hodd : ¬ 2 ∣ x) : x % 8 = 5 := by
  rcases hx with h | he
  · exact h
  · exact False.elim (hodd he)

/-- an integer with x % 2 = 1 is odd. -/
lemma not_even_of_emod_two {x : ℤ} (h : x % 2 = 1) : ¬ 2 ∣ x := by
  intro h2
  have h0 : x % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2
  omega

/-- Non-stuck S-move step: moving coordinate i of v produces the new value
u i; if it is coprime to the old value u j = v j and v j has a coprime old
partner v k, then pairChi (u i) (u j) = -1.
The hypotheses collect exactly the facts (Descartes equation of u, residue
classes, positivity) that follow from the orbit structure at a call site. -/
theorem move_step (v : Fin 4 → ℤ) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hD4 : ((gen i • v) i + (gen i • v) j + (gen i • v) k + (gen i • v) l)^2 =
       2 * (((gen i • v) i)^2 + ((gen i • v) j)^2 + ((gen i • v) k)^2 + ((gen i • v) l)^2))
    (hP : ∀ a b : Fin 4, a ≠ b → (v a).gcd (v b) = 1 → pairChi (v a) (v b) = -1)
    (hcop : ((gen i • v) j).gcd ((gen i • v) i) = 1)
    (hold : (v j).gcd (v k) = 1)
    (ht5e : ((gen i • v) j) % 8 = 5 ∨ 2 ∣ (gen i • v) j)
    (hw5e : ((gen i • v) i) % 8 = 5 ∨ 2 ∣ (gen i • v) i)
    (hk5e : ((gen i • v) k) % 8 = 5 ∨ 2 ∣ (gen i • v) k)
    (hpos : 0 < (gen i • v) i ∨ 0 < (gen i • v) j) :
    pairChi ((gen i • v) i) ((gen i • v) j) = -1 := by
  let u : Fin 4 → ℤ := gen i • v
  have huj : u j = v j := by simpa [u] using other_coord_eq v i j hij.symm
  have huk : u k = v k := by simpa [u] using other_coord_eq v i k hik.symm
  have hDx : (u j + u i + u k + u l)^2 = 2 * ((u j)^2 + (u i)^2 + (u k)^2 + (u l)^2) := by
    rw [show (u j + u i + u k + u l) = (u i + u j + u k + u l) by ring]
    rw [show (u j)^2 + (u i)^2 + (u k)^2 + (u l)^2 = (u i)^2 + (u j)^2 + (u k)^2 + (u l)^2 by ring]
    exact hD4
  have hpos1 : 0 < u i ∨ 0 < u j := by simpa [u] using hpos
  have hpos2 : 0 < u j ∨ 0 < u i := by simpa [u, or_comm] using hpos
  have hg1 : (u i).gcd (u j) = 1 := by
    rw [Int.gcd_comm]
    simpa [u] using hcop
  have hg2 : (u k).gcd (u j) = 1 := by
    rw [Int.gcd_comm]
    simpa [huj, huk] using hold
  have hpjk : pairChi (u j) (u k) = -1 := by
    have h := hP j k hjk hold
    simpa [huj, huk] using h
  -- flip the ordered pair (only depends on parity of u i and u j):
  have hflip : pairChi (u i) (u j) = pairChi (u j) (u i) := by
    rcases ht5e with htj5 | htj2
    · -- u j odd ≡ 5 mod 8
      rcases hw5e with hwi5 | hwi2
      · exact pairChi_odd_odd_symm (o₁ := u i) (o₂ := u j) (mod4_one_of_mod8_five hwi5)
          (mod4_one_of_mod8_five htj5) hpos1
      · exact (pairChi_mixed (o := u j) (e := u i) htj5 hcop hpos2).symm
    · -- u j even: then u i is odd (coprime to an even number)
      have huj2 : 2 ∣ u j := by simpa [u] using htj2
      have hwi : u i % 2 = 1 := odd_mod_of_coprime_even huj2 hg1
      have hwi_odd : ¬ 2 ∣ u i := not_even_of_emod_two hwi
      have hwi5 : u i % 8 = 5 := mod8_five_of_not_even hw5e hwi_odd
      exact pairChi_mixed (o := u i) (e := u j) hwi5 hg1 hpos1
  -- consistency at the old coordinate u j:
  have hc : pairChi (u j) (u i) = -1 := by
    rcases ht5e with htj5 | htj2
    · -- u j odd: partner consistency without the mod-8 condition
      have hodd : ¬ 2 ∣ u j := odd_of_mod8_five htj5
      have h := pairChi_partner_consistency_odd (x := u j) (y₁ := u i) (y₂ := u k) (z := u l)
        hDx hodd hg1 hg2
      rw [h, hpjk]
    · -- u j even: both partners are odd ≡ 5 mod 8, hence congruent mod 8
      have huj2 : 2 ∣ u j := by simpa [u] using htj2
      have hwi : u i % 2 = 1 := odd_mod_of_coprime_even huj2 hg1
      have hwi_odd : ¬ 2 ∣ u i := not_even_of_emod_two hwi
      have hwi5 : u i % 8 = 5 := mod8_five_of_not_even hw5e hwi_odd
      have hwk : u k % 2 = 1 := odd_mod_of_coprime_even huj2 hg2
      have hwk_odd : ¬ 2 ∣ u k := not_even_of_emod_two hwk
      have hwk5 : u k % 8 = 5 := mod8_five_of_not_even hk5e hwk_odd
      have h8 : u i % 8 = u k % 8 := by rw [hwi5, hwk5]
      have h := pairChi_partner_consistency (x := u j) (y₁ := u i) (y₂ := u k) (z := u l)
        hDx hg1 hg2 h8
      rw [h, hpjk]
  calc
    pairChi ((gen i • v) i) ((gen i • v) j) = pairChi (u i) (u j) := by simp [u]
    _ = pairChi (u j) (u i) := hflip
    _ = -1 := hc

end Apollo
