import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `SwapE` — truncation of `lawSum` at the slot box

`massHalf H M = 2HM` and `massBox d H M = [−2HM, 2HM]^d`.  If the slot coefficients satisfy
`|q₁|, |q₂| ≤ H` then every *difference* of two slot values `pdir q₁ q₂ ·` lies in
`[−2HM, 2HM]`: the two slot values differ by
`q₁((m₁+1) − (m₁'+1)) − q₂((m₂+1) − (m₂'+1))`, and each of the two coordinates is a difference of
two numbers of `[1,M]`, hence of modulus at most `M`.  Consequently the slot law vanishes off the
slot box, and the truncated sum `lawSum` (over `[±L]^d`) agrees with the sum over the slot box as
soon as `2HM ≤ L`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- Every difference of two slot values is bounded by `massHalf H M = 2HM` in modulus, as soon as
the slot coefficients are bounded by `H`. -/
theorem abs_pdir_sub_le (q₁ q₂ : ℤ) (H M : ℕ) (h1 : |q₁| ≤ (H : ℤ)) (h2 : |q₂| ≤ (H : ℤ))
    (m m' : Fin M × Fin M) :
    |pdir q₁ q₂ m - pdir q₁ q₂ m'| ≤ massHalf H M := by
  have hs : |((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1)| ≤ (M : ℤ) := by
    have h1lt : (m.1 : ℕ) < M := m.1.isLt
    have h2lt : (m'.1 : ℕ) < M := m'.1.isLt
    rw [show ((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1)
        = ((m.1 : ℕ) : ℤ) - ((m'.1 : ℕ) : ℤ) by ring]
    rw [abs_le]
    constructor <;> omega
  have ht : |((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1)| ≤ (M : ℤ) := by
    have h1lt : (m.2 : ℕ) < M := m.2.isLt
    have h2lt : (m'.2 : ℕ) < M := m'.2.isLt
    rw [show ((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1)
        = ((m.2 : ℕ) : ℤ) - ((m'.2 : ℕ) : ℤ) by ring]
    rw [abs_le]
    constructor <;> omega
  have hH : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
  have key : |q₁ * (((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1))
        - q₂ * (((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1))|
      ≤ (H : ℤ) * (M : ℤ) + (H : ℤ) * (M : ℤ) := by
    calc |q₁ * (((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1))
            - q₂ * (((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1))|
        ≤ |q₁ * (((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1))|
            + |q₂ * (((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1))| := by
          rw [sub_eq_add_neg, ← abs_neg (q₂ * _)]
          exact abs_add_le _ _
      _ = |q₁| * |((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1)|
            + |q₂| * |((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1)| := by
          rw [abs_mul, abs_mul]
      _ ≤ (H : ℤ) * (M : ℤ) + (H : ℤ) * (M : ℤ) := by
          apply add_le_add
          · exact mul_le_mul h1 hs (abs_nonneg _) hH
          · exact mul_le_mul h2 ht (abs_nonneg _) hH
  have hmh : massHalf H M = (H : ℤ) * (M : ℤ) + (H : ℤ) * (M : ℤ) := by
    simp [massHalf, Nat.cast_mul]
    ring
  have hpd : pdir q₁ q₂ m - pdir q₁ q₂ m'
      = q₁ * (((m.1 : ℕ) : ℤ) + 1 - (((m'.1 : ℕ) : ℤ) + 1))
        - q₂ * (((m.2 : ℕ) : ℤ) + 1 - (((m'.2 : ℕ) : ℤ) + 1)) := by
    simp only [pdir]
    ring
  rw [hpd, hmh]
  exact key

/-- The two-line count `slotCount q₁ q₂ M n` vanishes for `|n| > massHalf H M`, since no slot
difference can be that large. -/
theorem slotCount_eq_zero_of_massHalf_lt (q₁ q₂ : ℤ) (H M : ℕ)
    (h1 : |q₁| ≤ (H : ℤ)) (h2 : |q₂| ≤ (H : ℤ)) (n : ℤ) (hn : massHalf H M < |n|) :
    slotCount q₁ q₂ M n = 0 := by
  rw [slotCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  intro hp
  have h := abs_pdir_sub_le q₁ q₂ H M h1 h2 p.1 p.2
  rw [hp] at h
  exact absurd h (not_le.mpr hn)

/-- The slot law vanishes off the slot box. -/
theorem slotLaw_eq_zero_of_massHalf_lt (q₁ q₂ : ℤ) (H M : ℕ)
    (h1 : |q₁| ≤ (H : ℤ)) (h2 : |q₂| ≤ (H : ℤ)) (n : ℤ) (hn : massHalf H M < |n|) :
    slotLaw q₁ q₂ M n = 0 := by
  simp only [slotLaw, slotCount_eq_zero_of_massHalf_lt q₁ q₂ H M h1 h2 n hn, Nat.cast_zero,
    zero_div]

/-- **Truncation at the slot box.**  The `lawSum` (a sum over `[±L]^d`) agrees with the sum over
the slot box `massBox d H M = [−2HM, 2HM]^d`, provided `2HM ≤ L`: the summand vanishes outside the
slot box, and the slot box is contained in `[±L]^d`. -/
theorem lawSumEqMassBox (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M H L : ℕ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hb1 : ∀ k, |q₁ k| ≤ (H : ℤ)) (hb2 : ∀ k, |q₂ k| ≤ (H : ℤ))
    (hLm : Work.Peluse.SwapE.massHalf H M ≤ (L : ℤ)) :
    Work.Peluse.SwapE.lawSum d q₁ q₂ M S f L
      = ∑ n ∈ Work.Peluse.SwapE.massBox d H M,
          (∏ k : Fin d, (Work.Peluse.SwapE.slotLaw (q₁ k) (q₂ k) M (n k) : ℂ))
            * Work.Peluse.SwapE.boxMass d S f n := by
  have hsub : massBox d H M ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro n hn
    simp only [massBox, Fintype.mem_piFinset] at hn ⊢
    intro k
    have hk : |n k| ≤ massHalf H M := by
      have := hn k
      rwa [Finset.mem_Icc, ← abs_le] at this
    obtain ⟨hk1, hk2⟩ := abs_le.mp hk
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hvan : ∀ x ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)),
      x ∉ massBox d H M →
      (∏ k : Fin d, (slotLaw (q₁ k) (q₂ k) M (x k) : ℂ)) * boxMass d S f x = 0 := by
    intro x _ hx
    have hex : ∃ k, massHalf H M < |x k| := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      exact hx (by
        rw [massBox, Fintype.mem_piFinset]
        intro k
        rw [Finset.mem_Icc]
        exact ⟨neg_le_of_abs_le (hc k), le_of_abs_le (hc k)⟩)
    obtain ⟨k, hk⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ k)
      (by simpa using slotLaw_eq_zero_of_massHalf_lt (q₁ k) (q₂ k) H M (hb1 k) (hb2 k) (x k) hk),
      zero_mul]
  rw [lawSum]
  exact (Finset.sum_subset hsub hvan).symm

end

end Work.Peluse.SwapE
