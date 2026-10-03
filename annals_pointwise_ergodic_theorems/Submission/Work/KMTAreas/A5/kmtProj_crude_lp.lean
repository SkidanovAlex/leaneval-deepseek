/-
# Area A5: the crude `ℓ^p` bound for the IW projections at the §5 scales

`Work.KMTContract.kmtProj ρ l k` is the Ionescu--Wainger projection `Π_{≤l,≤k}`, a convolution
with a kernel in `ℓ¹` (its Fourier coefficients decay like `j^{-2}`, `KMTContract.kmtKernel_decay`).
Young's inequality at the endpoint `1` therefore gives the crude bound
`‖Π_{≤l,≤k} u‖_{ℓ^p} ≤ C(l,k) ‖u‖_{ℓ^p}` for every `1 < p < ∞`
(`Work.KMTAreas.A7.KmtProjCrude`); the constant depends on `l,k` but is finite for each pair.

The two families of parameters appearing in §5 of Krause--Mirek--Tao are
`k = -Log N + l_{(N)}` and `k = -d Log N + d l_{(N)}` with `l_{(N)} = C₀ LogLog N`.  Only
*finitely many* of them occur below a fixed `Nmax`, so taking the sum of the individual constants
over `n ≤ Nmax` produces the single constant requested here.  (No uniformity in `k` is claimed:
the decay constant of `kmtKernel_decay` grows with `2^k`.)
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A7.KmtProjCrude

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem kmtProj_crude_lp {ρ : ℝ} {p : ℝ} (hp : 1 < p) (C₀ Nmax d : ℕ) :
    ∃ C : ℝ≥0, ∀ n : ℕ, n ≤ Nmax → ∀ u : ℤ → ℂ,
      (eLpNorm (Work.KMTContract.kmtProj ρ (Work.Analysis.EndVar.heightScale C₀ n)
            (-(Work.Analysis.EndVar.logN n) + (Work.Analysis.EndVar.heightScale C₀ n : ℤ)) u)
          (ENNReal.ofReal p) Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p) Measure.count) ∧
      (eLpNorm (Work.KMTContract.kmtProj ρ (Work.Analysis.EndVar.heightScale C₀ n)
            (-((d : ℤ) * Work.Analysis.EndVar.logN n) + (d : ℤ) * (Work.Analysis.EndVar.heightScale C₀ n : ℤ)) u)
          (ENNReal.ofReal p) Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p) Measure.count) := by
  -- The crude `ℓ^p` bound of area A7 for a *single* pair of parameters `(l,k)`.
  have hsingle : ∀ (l : ℕ) (k : ℤ), ∃ C : ℝ≥0, ∀ u : ℤ → ℂ,
      eLpNorm (Work.KMTContract.kmtProj ρ l k u) (ENNReal.ofReal p) Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p) Measure.count := by
    intro l k
    obtain ⟨C, _hCpos, hC⟩ := Work.KMTAreas.A7.KmtProjCrude (ρ := ρ) l k hp
    exact ⟨C, fun u => by
      simpa only [ENNReal.ofReal_coe_nnreal] using hC u⟩
  classical
  -- Combine the two constants of the two parameter families at each `n`.
  have htwo : ∀ n : ℕ, ∃ C : ℝ≥0,
      (∀ u : ℤ → ℂ,
        eLpNorm (Work.KMTContract.kmtProj ρ (Work.Analysis.EndVar.heightScale C₀ n)
              (-(Work.Analysis.EndVar.logN n) + (Work.Analysis.EndVar.heightScale C₀ n : ℤ)) u)
            (ENNReal.ofReal p) Measure.count
          ≤ (C : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p) Measure.count) ∧
      (∀ u : ℤ → ℂ,
        eLpNorm (Work.KMTContract.kmtProj ρ (Work.Analysis.EndVar.heightScale C₀ n)
              (-((d : ℤ) * Work.Analysis.EndVar.logN n)
                + (d : ℤ) * (Work.Analysis.EndVar.heightScale C₀ n : ℤ)) u)
            (ENNReal.ofReal p) Measure.count
          ≤ (C : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p) Measure.count) := by
    intro n
    obtain ⟨C₁, hC₁⟩ := hsingle (Work.Analysis.EndVar.heightScale C₀ n)
      (-(Work.Analysis.EndVar.logN n) + (Work.Analysis.EndVar.heightScale C₀ n : ℤ))
    obtain ⟨C₂, hC₂⟩ := hsingle (Work.Analysis.EndVar.heightScale C₀ n)
      (-((d : ℤ) * Work.Analysis.EndVar.logN n)
        + (d : ℤ) * (Work.Analysis.EndVar.heightScale C₀ n : ℤ))
    refine ⟨C₁ + C₂, fun u => (hC₁ u).trans ?_, fun u => (hC₂ u).trans ?_⟩
    · exact mul_le_mul' (ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)) le_rfl
    · exact mul_le_mul' (ENNReal.coe_le_coe.mpr (le_add_of_nonneg_left bot_le)) le_rfl
  choose Cf hCf using htwo
  -- A single constant for all `n ≤ Nmax`: the sum of the finitely many individual ones.
  refine ⟨∑ n ∈ Finset.range (Nmax + 1), Cf n, fun n hn u => ⟨?_, ?_⟩⟩
  · have hle := Finset.single_le_sum (f := Cf) (s := Finset.range (Nmax + 1))
      (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact (hCf n).1 u |>.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hle) le_rfl)
  · have hle := Finset.single_le_sum (f := Cf) (s := Finset.range (Nmax + 1))
      (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact (hCf n).2 u |>.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hle) le_rfl)

end Work.KMTAreas.A5
