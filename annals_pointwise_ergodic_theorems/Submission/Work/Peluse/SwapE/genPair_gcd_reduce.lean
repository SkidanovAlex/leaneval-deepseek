import Mathlib
import Submission.Work.Peluse.SwapE.slotDensityAux

/-!
# `SwapE` — the gcd reduction of a generic slot pair

This file is the arithmetic core of the slot-density step (KKL, arXiv:2407.08636,
Corollary 7.2 at `ℓ = 2`, see `SwapE/slotDensity.lean`).  A *generic* pair of slot
coefficients (`genPair H η`: both at least `ηH` in modulus, gcd at most `1/η`) is reduced
by the gcd to a *primitive* pair, and the reduction is controlled in two ways:

* the reduced pair `(slotA q₁ q₂, slotB q₁ q₂) = (q₁/g, q₂/g)` (`g = gcd q₁ q₂`) is coprime,
  both entries are nonzero, its direction is the *primitive* direction of the slot equation
  `q₁ X − q₂ Y = n`;
* the solution count of the slot equation in a box never increases under the reduction
  (`slotDiffCount q₁ q₂ K n ≤ slotDiffCount (q₁/g) (q₂/g) K (n/g)`), which is why the density
  estimate `slotDiffCount_le` may be quoted for the *primitive* form: every solution of the
  reduced equation lies in the same box and every solution of the original equation reduces
  to one of them;
* and the reduced pair still has a modulus comparable to `H`: `η² H ≤ max |q₁/g| |q₂/g|`,
  because `|qᵢ| ≥ ηH` and `g ≤ 1/η`.  This is exactly the bound `|a| ≥ η²H` used in
  `slotDensity`.

The two identities `mul_gcd_slotA`/`mul_gcd_slotB` (`qᵢ = slot*ᵢ · g`) are stated
unconditionally; the divisibility is `Int.gcd_dvd_left`/`Int.gcd_dvd_right` and the exactness
of the integer division `Int.ediv_mul_cancel`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 1. The exact gcd decomposition -/

/-- `g = gcd q₁ q₂` divides `q₁`, so `q₁ = (q₁/g)·g`: the exact decomposition of `q₁` along the
gcd.  In particular `slotA q₁ q₂ = q₁/g` is the coefficient of the *primitive* direction. -/
theorem mul_gcd_slotA (q₁ q₂ : ℤ) : slotA q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) = q₁ :=
  Int.ediv_mul_cancel (Int.gcd_dvd_left q₁ q₂)

/-- `q₂ = (q₂/g)·g`. -/
theorem mul_gcd_slotB (q₁ q₂ : ℤ) : slotB q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) = q₂ :=
  Int.ediv_mul_cancel (Int.gcd_dvd_right q₁ q₂)

/-- Every solution of `q₁ X − q₂ Y = n` in the box `[−K,K]²` is a solution of
`(q₁/g) X − (q₂/g) Y = n/g` in the same box: the gcd reduction of the slot equation is
injective on solutions. -/
theorem slotDiffSet_subset_gcd (q₁ q₂ : ℤ) (K : ℕ) (n : ℤ) (hg : 0 < Int.gcd q₁ q₂) :
    slotDiffSet q₁ q₂ K n ⊆
      slotDiffSet (slotA q₁ q₂) (slotB q₁ q₂) K (n / (Int.gcd q₁ q₂ : ℤ)) := by
  have hqa : q₁ = slotA q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) := (mul_gcd_slotA q₁ q₂).symm
  have hqb : q₂ = slotB q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) := (mul_gcd_slotB q₁ q₂).symm
  intro p hp
  rw [mem_slotDiffSet] at hp ⊢
  obtain ⟨h1, h2, heq⟩ := hp
  refine ⟨h1, h2, ?_⟩
  have hgZ : (0 : ℤ) < (Int.gcd q₁ q₂ : ℤ) := by exact_mod_cast hg
  have e1 : q₁ * p.1 = slotA q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) * p.1 := by
    nth_rewrite 1 [hqa]; ring
  have e2 : q₂ * p.2 = slotB q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) * p.2 := by
    nth_rewrite 1 [hqb]; ring
  have hmul : n = (slotA q₁ q₂ * p.1 - slotB q₁ q₂ * p.2) * (Int.gcd q₁ q₂ : ℤ) := by
    rw [← heq, e1, e2]; ring
  exact (Int.ediv_eq_of_eq_mul_left (ne_of_gt hgZ) hmul).symm

/-- The modulus identity behind the bound `|slotA|, |slotB| ≥ η²H`: multiplying the reduced
coefficient by the gcd returns the original coefficient, in absolute value. -/
theorem abs_slotA_mul_gcd (q₁ q₂ : ℤ) (hg : 0 < Int.gcd q₁ q₂) :
    |((slotA q₁ q₂ : ℤ) : ℝ)| * (Int.gcd q₁ q₂ : ℝ) = |((q₁ : ℤ) : ℝ)| := by
  have hgR : (0 : ℝ) < (Int.gcd q₁ q₂ : ℝ) := by exact_mod_cast hg
  have hcast : (q₁ : ℝ) = ((slotA q₁ q₂ : ℤ) : ℝ) * (Int.gcd q₁ q₂ : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (mul_gcd_slotA q₁ q₂)
    push_cast at h
    exact h.symm
  rw [hcast, abs_mul, abs_of_pos hgR]

/-- Same identity for the second reduced coefficient. -/
theorem abs_slotB_mul_gcd (q₁ q₂ : ℤ) (hg : 0 < Int.gcd q₁ q₂) :
    |((slotB q₁ q₂ : ℤ) : ℝ)| * (Int.gcd q₁ q₂ : ℝ) = |((q₂ : ℤ) : ℝ)| := by
  have hgR : (0 : ℝ) < (Int.gcd q₁ q₂ : ℝ) := by exact_mod_cast hg
  have hcast : (q₂ : ℝ) = ((slotB q₁ q₂ : ℤ) : ℝ) * (Int.gcd q₁ q₂ : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (mul_gcd_slotB q₁ q₂)
    push_cast at h
    exact h.symm
  rw [hcast, abs_mul, abs_of_pos hgR]

/-! ## 2. The gcd reduction for a generic pair -/

theorem genPair_gcd_reduce (q₁ q₂ : ℤ) (H : ℕ) (η : ℝ) (K : ℕ) (n : ℤ)
    (hH : 1 ≤ H) (hη : 0 < η) (hη1 : η ≤ 1) (hgen : Work.Peluse.LadderP.Swap.genPair H η q₁ q₂) :
    0 < Int.gcd q₁ q₂ ∧ IsCoprime (slotA q₁ q₂) (slotB q₁ q₂) ∧
      slotA q₁ q₂ ≠ 0 ∧ slotB q₁ q₂ ≠ 0 ∧
      slotDiffCount q₁ q₂ K n ≤
        slotDiffCount (slotA q₁ q₂) (slotB q₁ q₂) K (n / (Int.gcd q₁ q₂ : ℤ)) ∧
      η ^ 2 * (H : ℝ) ≤ max |(slotA q₁ q₂ : ℝ)| |(slotB q₁ q₂ : ℝ)| := by
  obtain ⟨hq1, hq2, hg_le⟩ := hgen
  -- The arithmetic core below uses only `η > 0`, `|qᵢ| ≥ ηH` and `gcd ≤ 1/η`; the hypothesis
  -- `η ≤ 1` is part of the generic-pair regime and is not needed for these estimates.
  have _hη1 : η ≤ 1 := hη1
  have hqa : q₁ = slotA q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) := (mul_gcd_slotA q₁ q₂).symm
  have hqb : q₂ = slotB q₁ q₂ * (Int.gcd q₁ q₂ : ℤ) := (mul_gcd_slotB q₁ q₂).symm
  -- `ηH > 0`, hence neither coefficient vanishes: only the zero pair has gcd zero.
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hηH : 0 < η * (H : ℝ) := by nlinarith
  have hq1ne : q₁ ≠ 0 := by
    intro h
    rw [h] at hq1
    simp at hq1
    linarith
  have hq2ne : q₂ ≠ 0 := by
    intro h
    rw [h] at hq2
    simp at hq2
    linarith
  have hgpos : 0 < Int.gcd q₁ q₂ := Int.gcd_pos_of_ne_zero_left q₂ hq1ne
  have hgposR : (0 : ℝ) < (Int.gcd q₁ q₂ : ℝ) := by exact_mod_cast hgpos
  -- The two structural facts: coprimality and non-vanishing of the reduced pair.
  have hcop : IsCoprime (slotA q₁ q₂) (slotB q₁ q₂) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hgpos)
  have ha : slotA q₁ q₂ ≠ 0 := by
    intro h
    exact hq1ne (by nth_rewrite 1 [hqa]; rw [h, zero_mul])
  have hb : slotB q₁ q₂ ≠ 0 := by
    intro h
    exact hq2ne (by nth_rewrite 1 [hqb]; rw [h, zero_mul])
  -- The count inequality: the reduced equation has at least the solutions of the original one.
  have hcount : slotDiffCount q₁ q₂ K n ≤
      slotDiffCount (slotA q₁ q₂) (slotB q₁ q₂) K (n / (Int.gcd q₁ q₂ : ℤ)) :=
    Finset.card_le_card (slotDiffSet_subset_gcd q₁ q₂ K n hgpos)
  -- The modulus bound `η²H ≤ max |q₁/g| |q₂/g|`, from `|q₁| ≥ ηH` and `g ≤ 1/η`.
  have habsA := abs_slotA_mul_gcd q₁ q₂ hgpos
  have hq1R : η * (H : ℝ) ≤ |((q₁ : ℤ) : ℝ)| := by simpa [Int.cast_abs] using hq1
  have hdiv : η * (H : ℝ) / (Int.gcd q₁ q₂ : ℝ) ≤ |((slotA q₁ q₂ : ℤ) : ℝ)| := by
    rw [div_le_iff₀ hgposR, habsA]
    exact hq1R
  have hgInv : η ≤ 1 / (Int.gcd q₁ q₂ : ℝ) := by
    rw [le_div_iff₀ hgposR]
    have h := mul_le_mul_of_nonneg_left hg_le hη.le
    rw [mul_one_div, div_self (ne_of_gt hη)] at h
    exact h
  have hmain : η ^ 2 * (H : ℝ) ≤ |((slotA q₁ q₂ : ℤ) : ℝ)| := by
    calc η ^ 2 * (H : ℝ) = η * (H : ℝ) * η := by ring
      _ ≤ η * (H : ℝ) * (1 / (Int.gcd q₁ q₂ : ℝ)) := mul_le_mul_of_nonneg_left hgInv hηH.le
      _ = η * (H : ℝ) / (Int.gcd q₁ q₂ : ℝ) := by ring
      _ ≤ |((slotA q₁ q₂ : ℤ) : ℝ)| := hdiv
  exact ⟨hgpos, hcop, ha, hb, hcount, le_trans hmain (le_max_left _ _)⟩

end

end Work.Peluse.SwapE
