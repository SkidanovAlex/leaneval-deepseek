/-
# `FIArea2/R6/gcdBox_bound`

Bound for the gcd-box `gcdBox c X Y = Σ_{h₁ ∈ zPz X} Σ_{h₂ ∈ zPz Y} gcd(c, h₁², h₂²)`
(see `ndCountDefs`):

  `gcdBox c X Y ≤ 4 · X · Y · τ(c)`  for `1 ≤ c`, `1 ≤ X`, `1 ≤ Y`,

which is sharp at `c = 1`.

The proof goes through the totient expansion `gcd(c,a,b) = Σ_{d ∣ gcd(c,a,b)} φ(d)`, which
turns the double box sum into

  `gcdBox c X Y = Σ_{d ∣ c} φ(d) · #{h₁ ∈ zPz X : d ∣ h₁²} · #{h₂ ∈ zPz Y : d ∣ h₂²}`

(the defining identity `gcdBox_eq_sum_totient`).  Since `d ∣ h² ↔ ceilRoot 2 d ∣ h`, each count
is controlled by the number of multiples of `E = ceilRoot 2 d` in the box (`card_zPz_filter_dvd`),
and `φ(d) ≤ d ≤ E²`, the per-`d` term is `≤ 4XY`.  Summing over the `τ(c)` divisors gives the
claim.
-/
import Mathlib
import Submission.Work.FIArea2.R6.ndCountDefs
import Submission.Work.FIArea2.R6.card_zPz_filter_dvd
import Submission.Work.FIArea2.R6.gcdBox_eq_sum_totient

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable section

/-- `d ∣ (h^2).natAbs` forces `Nat.ceilRoot 2 d ∣ h`: the ceiling square root of `d` is the
minimal modulus whose square `d` divides. -/
lemma filter_sq_subset (X d : ℕ) :
    (zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)
      ⊆ (zPz X).filter (fun h => ((Nat.ceilRoot 2 d : ℕ) : ℤ) ∣ h) := by
  intro h hh
  simp only [Finset.mem_filter] at hh ⊢
  refine ⟨hh.1, ?_⟩
  rw [Int.natAbs_pow] at hh
  exact Int.natCast_dvd.mpr
    ((Nat.dvd_pow_iff_ceilRoot_dvd (by norm_num : (2:ℕ) ≠ 0)).mp hh.2)

/-- Per-divisor term bound: `φ(d) · #{h₁ : d ∣ h₁²} · #{h₂ : d ∣ h₂²} ≤ 4XY` for `d ∣ c`. -/
lemma gcdBox_term_bound (c X Y d : ℕ) (hd : d ∈ c.divisors) :
    Nat.totient d * ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
      * ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card ≤ 4 * X * Y := by
  obtain ⟨hdvd, hcne⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by
    intro h0
    exact hcne (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  set E := Nat.ceilRoot 2 d with hEdef
  have hE1 : 1 ≤ E := by
    rw [hEdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceilRoot_ne_zero.mpr ⟨by norm_num, hd0⟩)
  set N1 := ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card with hN1def
  set N2 := ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card with hN2def
  have hN1 : N1 * E ≤ 2 * X := by
    rw [hN1def]
    have hsub : (zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)
        ⊆ (zPz X).filter (fun h => (E:ℤ) ∣ h) := by
      rw [hEdef]; exact filter_sq_subset X d
    exact le_trans (Nat.mul_le_mul_right E (Finset.card_le_card hsub))
      (card_zPz_filter_dvd E X hE1)
  have hN2 : N2 * E ≤ 2 * Y := by
    rw [hN2def]
    have hsub : (zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)
        ⊆ (zPz Y).filter (fun h => (E:ℤ) ∣ h) := by
      rw [hEdef]; exact filter_sq_subset Y d
    exact le_trans (Nat.mul_le_mul_right E (Finset.card_le_card hsub))
      (card_zPz_filter_dvd E Y hE1)
  have hφ : Nat.totient d ≤ E ^ 2 := by
    have hdvd2 : d ∣ E ^ 2 := by
      rw [hEdef]; exact Nat.dvd_ceilRoot_pow (by norm_num : (2:ℕ) ≠ 0)
    have hEpos : 0 < E := by omega
    exact le_trans (Nat.totient_le d) (Nat.le_of_dvd (pow_pos hEpos 2) hdvd2)
  calc Nat.totient d * N1 * N2 ≤ E ^ 2 * N1 * N2 :=
        Nat.mul_le_mul_right N2 (Nat.mul_le_mul_right N1 hφ)
    _ = (N1 * E) * (N2 * E) := by ring
    _ ≤ (2 * X) * (2 * Y) := Nat.mul_le_mul hN1 hN2
    _ = 4 * X * Y := by ring

/-- Natural-number form of the bound: `gcdBox c X Y ≤ 4XY·τ(c)`. -/
theorem gcdBox_le (c X Y : ℕ) (hc : 1 ≤ c) :
    gcdBox c X Y ≤ 4 * X * Y * c.divisors.card := by
  rw [gcdBox_eq_sum_totient c X Y hc]
  calc c.divisors.sum (fun d => Nat.totient d
          * ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card)
      ≤ c.divisors.sum (fun _ => 4 * X * Y) :=
        Finset.sum_le_sum (fun d hd => gcdBox_term_bound c X Y d hd)
    _ = 4 * X * Y * c.divisors.card := by
        rw [Finset.sum_const_nat (f := fun _ => 4 * X * Y) (m := 4 * X * Y)
          (fun _ _ => rfl)]
        ring

theorem gcdBox_bound :
    ∀ (c X Y : ℕ), 1 ≤ c → 1 ≤ X → 1 ≤ Y →
      (Work.FIArea2.R6.gcdBox c X Y : ℝ)
        ≤ 4 * (X : ℝ) * (Y : ℝ) * ((c.divisors.card : ℝ)) := by
  intro c X Y hc hX hY
  have h := gcdBox_le c X Y hc
  have hcast : ((4 * X * Y * c.divisors.card : ℕ) : ℝ)
      = 4 * (X:ℝ) * (Y:ℝ) * (c.divisors.card:ℝ) := by push_cast; ring
  rw [← hcast]
  exact_mod_cast h

end

end Work.FIArea2.R6
