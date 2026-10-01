import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Work.ZeroDensity.Jutila.LzDiffAux
open Work.ZeroDensity.Jutila.BzCross

/-- Pointwise form of the `czFI` splitting: with `Y_t = y·t/w`, `γ_r = log(⌊y/r⌋·r/y)` and
`L_r = log(Y_t/r)`, the factor `czFI` equals `-(L_r−1) + (L_r−1)γ_r + (γ_r²−γ_r) + 1`. -/
lemma rowFI_point {w y : ℝ} {r t : ℕ} (hw : 0 < w) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y)
    (ht : 1 ≤ t) :
    czFI w y r t
      = -(Real.log (czY w y t / (r : ℝ)) - 1)
        + (Real.log (czY w y t / (r : ℝ)) - 1) * rowGam y r
        + (rowGam y r ^ 2 - rowGam y r) + 1 := by
  rw [rowFI_split hw hr hry ht]; ring

lemma rowMain_decomp {w y : ℝ} {t r1 : ℕ} (hw : 0 < w) (ht : 1 ≤ t) (hr1 : 1 ≤ r1)
    (hry : ∀ r ∈ Finset.Icc 1 r1, (r : ℝ) ≤ y) :
    Work.ZeroDensity.Jutila.LzDiffAux.rowMain w y t r1
      = y * (- Work.ZeroDensity.Jutila.LzDiffAux.rowS1 t r1
                (Work.ZeroDensity.Jutila.BzCross.czY w y t)
              + Work.ZeroDensity.Jutila.LzDiffAux.rowT2 y
                  (Work.ZeroDensity.Jutila.BzCross.czY w y t) t r1
              + Work.ZeroDensity.Jutila.LzDiffAux.rowT3 y t r1
              + Work.ZeroDensity.Jutila.LzDiffAux.rowS0 t r1)
          - Work.ZeroDensity.Jutila.LzDiffAux.rowX w y t r1 := by
  -- Pointwise splitting of the summand of `rowMain`.
  have key : ∀ r ∈ Finset.Icc 1 r1,
      rowCoef t r * ((r : ℝ) * ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * czFI w y r t)
        = rowCoef t r * (y * (-(Real.log (czY w y t / (r : ℝ)) - 1)
              + (Real.log (czY w y t / (r : ℝ)) - 1) * rowGam y r
              + (rowGam y r ^ 2 - rowGam y r) + 1))
          - rowCoef t r * (rowRem y r * czFI w y r t) := by
    intro r hr
    obtain ⟨hr1', _⟩ := Finset.mem_Icc.mp hr
    have hb : czFI w y r t
              = (-(Real.log (czY w y t / (r : ℝ)) - 1)
              + (Real.log (czY w y t / (r : ℝ)) - 1) * rowGam y r
              + (rowGam y r ^ 2 - rowGam y r) + 1) :=
      rowFI_point hw hr1' (hry r hr) ht
    rw [hb, rowRem]; ring
  -- `rowMain = y·(splitting sum) − rowX`.
  have hL : (∑ r ∈ Finset.Icc 1 r1,
        rowCoef t r * ((r : ℝ) * ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * czFI w y r t))
      = y * (∑ r ∈ Finset.Icc 1 r1,
          rowCoef t r * (-(Real.log (czY w y t / (r : ℝ)) - 1)
              + (Real.log (czY w y t / (r : ℝ)) - 1) * rowGam y r
              + (rowGam y r ^ 2 - rowGam y r) + 1))
        - ∑ r ∈ Finset.Icc 1 r1, rowCoef t r * (rowRem y r * czFI w y r t) := by
    have hFG := Finset.sum_congr rfl key
    rw [hFG, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  -- The splitting sum is `−rowS1 + rowT2 + rowT3 + rowS0`.
  have hA : (∑ r ∈ Finset.Icc 1 r1,
          rowCoef t r * (-(Real.log (czY w y t / (r : ℝ)) - 1)
              + (Real.log (czY w y t / (r : ℝ)) - 1) * rowGam y r
              + (rowGam y r ^ 2 - rowGam y r) + 1))
      = - rowS1 t r1 (czY w y t) + rowT2 y (czY w y t) t r1 + rowT3 y t r1 + rowS0 t r1 := by
    rw [rowS1, rowT2, rowT3, rowS0]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [rowMain, rowX]
  rw [hL]
  rw [hA]

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
