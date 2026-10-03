/-
# The class sums of the adjacent differences of the unmodulated window

For `M ≥ 1`, `L ≥ 1` with `L ≤ M` and any residue `r`, consider the "class sum"

  `∑_j [ win M 0 (r + j L) − win M 0 (r + j L − 1) ]`

of the adjacent differences of the unmodulated reproducing window `win M 0`, taken along the
arithmetic progression `r + L ℤ`.

## Why it vanishes

The window is `win M 0 m = M⁻¹ ψ(m/M)` with `ψ = lipSchPsi` the inverse Fourier transform of the
bump `lipSchChi`, and `ψ` has the following *exact* periodization property
(`Work.KMTAreas.A4.lipSchPsi_periodization`): for `0 < λ ≤ 1`

  `∑_j ψ(y + j λ) = λ⁻¹`  for **every** `y ∈ ℝ`.

(The proof is Poisson summation: the Poisson dual of the `λ`-lattice sum is `λ⁻¹ ∑_n χ(n/λ) e(...)`,
and `χ` vanishes off `(-1,1)` while `λ ≤ 1`, so only `n = 0` survives.)

Now `λ = L/M ≤ 1`, and the two points of the `j`-th term differ by `1/M`:
`(r + jL)/M = r/M + j·(L/M)` and `(r + jL − 1)/M = (r−1)/M + j·(L/M)`.  Both are evaluations of the
*same* `λ`-periodization, at `y = r/M` and `y = (r−1)/M` respectively, so both sums equal `λ⁻¹`
and their difference is zero.  The only point of substance is that the step really is `L ≤ M`:
this is why the hypothesis on the lattice step is `L ≤ M` (and why the `⌊M⌋₊` of the A4 window
reduction, with `L = ⌊M⌋₊ ≤ M`, is legitimate), and it is *not* true without it.

The general step `L ≤ M` is what `Work.KMTAreas.A4.boxDecomp` consumes as its class-sum
hypothesis; the version for the lattice step `L = ⌊M⌋₊` used by the window reduction
(`Work.KMTAreas.A4.winSum_reduce`) is the special case `winZero_classSum_vanish` below.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.winBase

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **The two periodizations of `ψ` at the same scale have equal sums.**  For `0 < λ ≤ 1` and
arbitrary `y δ ∈ ℝ`, the difference of the two `λ`-lattice sums of `ψ` is `λ⁻¹ − λ⁻¹ = 0`; both
sums are absolutely convergent, and their summability is read off from the non-vanishing of the
common value `λ⁻¹`. -/
theorem tsum_lipSchPsi_shift_sub_eq_zero (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (y δ : ℝ) :
    (∑' j : ℤ, ((lipSchPsi (y + (j : ℝ) * lam) : ℂ)
      - (lipSchPsi (y + δ + (j : ℝ) * lam) : ℂ))) = 0 := by
  have hA := lipSchPsi_periodization lam h0 h1 y
  have hB := lipSchPsi_periodization lam h0 h1 (y + δ)
  have hne : (↑lam : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt h0))
  have hsA : Summable fun j : ℤ => (lipSchPsi (y + (j : ℝ) * lam) : ℂ) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hA
    exact hne hA.symm
  have hsB : Summable fun j : ℤ => (lipSchPsi (y + δ + (j : ℝ) * lam) : ℂ) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hB
    exact hne hB.symm
  rw [Summable.tsum_sub hsA hsB, hA, hB, sub_self]

/-- **The class sums of the adjacent differences of the unmodulated window vanish.**
For every lattice step `L` with `1 ≤ L ≤ M`, every residue class `r + L ℤ` of the window lattice
contributes zero to the sum of the adjacent differences `m ↦ win M 0 m − win M 0 (m−1)`, because the
corresponding `L`-periodization of the profile `ψ` is the constant `M/L`
(`lipSchPsi_periodization`, legitimate since `L/M ≤ 1`). -/
theorem win_classSum_vanish (M : ℝ) (hM : 1 ≤ M) (L : ℕ) (hL : 1 ≤ L) (hLM : (L : ℝ) ≤ M)
    (r : ℤ) :
    (∑' j : ℤ, (Work.KMTAreas.A4.win M (0 : FreqCircle)
        (r + j * (L : ℤ))
      - Work.KMTAreas.A4.win M (0 : FreqCircle)
        (r + j * (L : ℤ) - 1))) = 0 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlam0 : 0 < (L : ℝ) / M := div_pos hLpos hMpos
  have hlam1 : (L : ℝ) / M ≤ 1 := (div_le_one hMpos).mpr hLM
  -- Each term is `M⁻¹` times the difference of two evaluations of the profile `ψ`.
  have hterm : ∀ j : ℤ, (win M (0 : FreqCircle) (r + j * (L : ℤ))
        - win M (0 : FreqCircle) (r + j * (L : ℤ) - 1))
      = ((M : ℂ))⁻¹ * ((lipSchPsi ((r : ℝ) / M + (j : ℝ) * ((L : ℝ) / M)) : ℂ)
        - (lipSchPsi ((r : ℝ) / M + (-1 / M) + (j : ℝ) * ((L : ℝ) / M)) : ℂ)) := by
    intro j
    have harg1 : (((r + j * (L : ℤ) : ℤ) : ℝ) / M)
        = (r : ℝ) / M + (j : ℝ) * ((L : ℝ) / M) := by
      push_cast; ring
    have harg2 : (((r + j * (L : ℤ) - 1 : ℤ) : ℝ) / M)
        = (r : ℝ) / M + (-1 / M) + (j : ℝ) * ((L : ℝ) / M) := by
      push_cast; ring
    rw [win_zero_apply, win_zero_apply, harg1, harg2, mul_sub]
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_lipSchPsi_shift_sub_eq_zero ((L : ℝ) / M) hlam0 hlam1 ((r : ℝ) / M) (-1 / M), mul_zero]

/-- **The class sums of the adjacent differences of the unmodulated window vanish**, for the
lattice step `⌊M⌋₊` of the window reduction (`Work.KMTAreas.A4.winSum_reduce`). -/
theorem winZero_classSum_vanish (M : ℝ) (hM : 1 ≤ M) (r : ℤ) :
    (∑' j : ℤ, (Work.KMTAreas.A4.win M (0 : Work.Analysis.InverseTheory.FreqCircle)
        (r + j * (Nat.floor M : ℤ))
      - Work.KMTAreas.A4.win M (0 : Work.Analysis.InverseTheory.FreqCircle)
        (r + j * (Nat.floor M : ℤ) - 1))) = 0 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hL : 1 ≤ Nat.floor M := (Nat.one_le_floor_iff M).mpr hM
  have hLM : ((Nat.floor M : ℕ) : ℝ) ≤ M := Nat.floor_le hMpos.le
  exact win_classSum_vanish M hM (Nat.floor M) hL hLM r

end Work.KMTAreas.A4
