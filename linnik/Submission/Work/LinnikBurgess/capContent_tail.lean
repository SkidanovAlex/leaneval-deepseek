import Mathlib
import Submission.Work.LinnikBurgess.card_hensel_le_sf

namespace Work.LinnikBurgess

open Polynomial

/-- If the `p`-adic valuation of `x.natAbs` is at least `k` then `p ^ k` divides `x` (as an
integer). -/
lemma pow_dvd_int_of_le_padicValNat {p : ℕ} [Fact p.Prime] {k : ℕ} {x : ℤ}
    (h : k ≤ padicValNat p x.natAbs) : ((p ^ k : ℕ) : ℤ) ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  · exact Int.natCast_dvd.mpr
      ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hx)).mpr h)

theorem capContent_tail {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ 4) (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    {A M : ℕ} (hA : 1 ≤ A) (hM : 1 ≤ M) (S : Finset ℕ)
    (hS : ∀ y ∈ S, ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ)
        ∧ M ≤ padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M) :
    S.card ≤ 3 := by
  classical
  -- Every element of `S` lies in the Hensel set of `Q'` at level `M`, with `ν = 0`.
  have hsub : S ⊆ henselSet p Q.derivative M := by
    intro y hy
    obtain ⟨-, hval, hQ2, hylt⟩ := hS y hy
    rw [henselSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hylt, 0, ?_, ?_, ?_⟩
    · simp
    · simpa using hQ2
    · have hmax : max (2 * 0 + 1) (M + 0) = M := by omega
      rw [hmax]
      exact pow_dvd_int_of_le_padicValNat hval
  by_cases hQ' : Q.derivative = 0
  · -- then `henselSet p Q' M` is empty, and so is `S`
    have hempty : henselSet p Q.derivative M = ∅ := by
      rw [hQ']
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      rw [henselSet, Finset.mem_filter] at hy
      obtain ⟨-, ν, -, h2, -⟩ := hy
      exact h2 (by simp)
    have hSempty : S = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun y hy => by
        have := hsub hy
        rw [hempty] at this
        exact Finset.notMem_empty y this)
    rw [hSempty]
    simp
  · calc S.card ≤ (henselSet p Q.derivative M).card := Finset.card_le_card hsub
      _ ≤ (Q.derivative).natDegree := card_hensel_le_sf Q.derivative hQ' M hM
      _ ≤ 3 := by
          have hle := Polynomial.natDegree_derivative_le Q
          omega

end Work.LinnikBurgess
