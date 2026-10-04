import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Λ^1 = - Δ` on the flat torus: `lapPow 1 = -lapC`

The symbol-calculus layer of B3 computes with the **flat Laplacian power** `Λ^k`, defined as the
Fourier multiplier with symbol `flatLam m ^ k` (`Work.Diff.STE.B3.SymCalcStep5.lapPow`), while the
geometric side of the development writes the second-order operator itself, `lapC = Σᵢ ∂ᵢ∂ᵢ`
(`Work.Diff.STE.B3.SymCalc.lapC`).  This file records the dictionary between the two for the case
`k = 1`, which is where both notations meet:

  `Λ w = - Δ w`,  i.e.  `lapPow 1 w x = - lapC w x`  for every `x`.

The content is the Fourier multiplier of the second derivative: for the characters
`e_m(x) = exp (2πi m·x)` one has `∂ᵢ e_m = (2πi mᵢ) e_m`, so

  `∂ᵢ∂ᵢ` acts as `(2πi mᵢ)² = -(2π mᵢ)²`,  and  `Σᵢ (2π mᵢ)² = flatLam m`,

hence `Δ` is the multiplier with symbol `-flatLam`, i.e. `Δ = -Λ`.  Everything is proved from the
Layer-A toolkit:

* `Work.Diff.STE.fourierCoeff_pd` : `fourierCoeff (∂ᵢ f) m = (2πi mᵢ) · û(m)` (integration by
  parts on the torus), applied twice;
* `Work.Diff.STE.flat.seriesFun_fourierCoeff` : Fourier inversion for smooth `1`-periodic
  functions, which turns the coefficient identity into a pointwise one;
* `Work.Diff.STE.ste_contDiff_pd` / `Work.Diff.STE.ste_periodicIn_pd` : `∂ᵢ` preserves smoothness
  and periodicity, so `lapC w` is again smooth and `1`-periodic (the two hypotheses of inversion).

The four helper lemmas below (`lapC_contDiff`, `lapC_periodic`, `fourierCoeff_lapC`,
`flatLam_eq_neg_sum_sq`) are the pieces of that computation.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lapC = Σᵢ ∂ᵢ∂ᵢ` is smooth as soon as `w` is: each `∂ᵢ∂ᵢ w` is smooth
(`Work.Diff.STE.ste_contDiff_pd`, applied twice) and the sum is finite. -/
lemma lapC_contDiff {w : (ι → ℝ) → ℂ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.lapC w) := by
  show ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ι → ℝ => ∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x)
  exact ContDiff.sum fun i _ =>
    Work.Diff.STE.ste_contDiff_pd i (Work.Diff.STE.ste_contDiff_pd i hw)

/-- `lapC w` is `1`-periodic whenever `w` is: `∂ᵢ∂ᵢ w` is periodic in every coordinate
(`Work.Diff.STE.ste_periodicIn_pd`, applied twice), and a finite sum of such functions is
periodic. -/
lemma lapC_periodic {w : (ι → ℝ) → ℂ} (hwp : Work.Diff.STE.Periodic1 w) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.lapC w) := by
  intro j x
  show (∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i w) (x + Pi.single j 1))
      = ∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Work.Diff.STE.ste_periodicIn_pd j i (Work.Diff.STE.ste_periodicIn_pd j i (hwp j)) x

omit [DecidableEq ι] in
/-- `-(2πi m)² = (2π m)²` as complex numbers, summed over the coordinates: the symbol of `lapC` is
`-flatLam`. -/
lemma flatLam_eq_neg_sum_sq (k : ι → ℤ) :
    (∑ i : ι, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2)
      = - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ) := by
  have hterm : ∀ i : ι, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2
      = - ((((2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ)) : ℂ) := by
    intro i
    have h2 : (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) ^ 2
        = -(((2 * (Real.pi : ℝ) * (k i : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [show (2 * ↑Real.pi * Complex.I * ↑(k i)) ^ 2
          = ((2 * ↑Real.pi * ↑(k i) : ℂ)) ^ 2 * Complex.I ^ 2 by ring]
      rw [Complex.I_sq]
      ring
    simpa using h2
  calc ∑ i : ι, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2
      = ∑ i : ι, - ((((2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ)) : ℂ) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = - (((∑ i : ι, (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ)) : ℂ) := by
        rw [Finset.sum_neg_distrib, Complex.ofReal_sum]
    _ = - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ) := rfl

/-- **The Fourier coefficients of `lapC`.**  For smooth `1`-periodic `w`,

  `fourierCoeff (lapC w) m = -flatLam m · û(m)`.

Indeed `fourierCoeff` is linear over the finite sum `Σᵢ`, `∂ᵢ` multiplies the `m`-th coefficient by
`2πi mᵢ` (`fourierCoeff_pd`), and `Σᵢ (2πi mᵢ)² = -flatLam m`. -/
lemma fourierCoeff_lapC {w : (ι → ℝ) → ℂ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwp : Work.Diff.STE.Periodic1 w) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.lapC w) k
      = - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
          * Work.Diff.STE.fourierCoeff w k := by
  have hC1 : ∀ i : ι, ContDiff ℝ (1 : WithTop ℕ∞) (Work.Diff.STE.pd i w) :=
    fun i => (Work.Diff.STE.ste_contDiff_pd i hw).of_le (by norm_num)
  have hper : ∀ i : ι, Work.Diff.STE.PeriodicIn i (Work.Diff.STE.pd i w) :=
    fun i => Work.Diff.STE.ste_periodicIn_pd i i (hwp i)
  -- linearity of `fourierCoeff` over the finite sum defining `lapC`
  have hlin : Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.lapC w) k
      = ∑ i, Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i (Work.Diff.STE.pd i w)) k := by
    change Work.Diff.STE.fourierCoeff
      (fun x : ι → ℝ => ∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x) k = _
    have hpt : ∀ x : ι → ℝ, Work.Diff.STE.fourierExp (-k) x
        * (∑ i, Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x)
        = ∑ i, Work.Diff.STE.fourierExp (-k) x
            * Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x :=
      fun x => Finset.mul_sum _ _ _
    have hInt : ∀ i ∈ (Finset.univ : Finset ι), Integrable
        (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x
          * Work.Diff.STE.pd i (Work.Diff.STE.pd i w) x)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := fun i _ =>
      Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
        ((Work.Diff.STE.continuous_fourierExp (-k)).mul
          (Work.Diff.STE.continuous_pd (hC1 i) i))
    simp only [Work.Diff.STE.fourierCoeff]
    rw [funext hpt, MeasureTheory.integral_finsetSum (s := Finset.univ) hInt]
  calc Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.lapC w) k
      = ∑ i, Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i (Work.Diff.STE.pd i w)) k := hlin
    _ = ∑ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2
          * Work.Diff.STE.fourierCoeff w k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Work.Diff.STE.fourierCoeff_pd i (Work.Diff.STE.pd i w) k (hC1 i) (hper i),
            Work.Diff.STE.fourierCoeff_pd i w k (hw.of_le (by norm_num)) (hwp i)]
        ring
    _ = (∑ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2) * Work.Diff.STE.fourierCoeff w k :=
        (Finset.sum_mul ..).symm
    _ = - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
          * Work.Diff.STE.fourierCoeff w k := by
        rw [flatLam_eq_neg_sum_sq]

/-- **`Λ = -Δ` on the flat torus.**  The Fourier multiplier `Λ` with symbol `flatLam` and the
second-order operator `Δ = Σᵢ ∂ᵢ∂ᵢ` are negatives of each other on smooth `1`-periodic functions.

Both sides are identified with the same Fourier series: `lapPow 1 w` is *by definition* the series
with coefficients `flatLam m · û(m)`, and `lapC w` is the series with coefficients
`-flatLam m · û(m)` (`fourierCoeff_lapC` + Fourier inversion `seriesFun_fourierCoeff`), which is
the negative of the former by `tsum_neg`. -/
theorem lapPow_one_eq_neg_lapC
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwp : Work.Diff.STE.Periodic1 w) :
    ∀ x : ι → ℝ, Work.Diff.STE.B3.SymCalcStep5.lapPow 1 w x
      = - Work.Diff.STE.B3.SymCalc.lapC w x := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.lapC w) := lapC_contDiff hw
  have hper : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.lapC w) := lapC_periodic hwp
  intro x
  -- `lapC w` is the Fourier series with coefficients `-flatLam m · û(m)`
  have h1 : Work.Diff.STE.B3.SymCalc.lapC w x
      = Work.Diff.STE.seriesFun
          (fun k => - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
            * Work.Diff.STE.fourierCoeff w k) x := by
    rw [← Work.Diff.STE.flat.seriesFun_fourierCoeff (Work.Diff.STE.B3.SymCalc.lapC w) hsm hper x]
    congr 1
    funext k
    exact fourierCoeff_lapC hw hwp k
  -- `lapPow 1 w` is the Fourier series with coefficients `flatLam m · û(m)`
  have h2 : Work.Diff.STE.B3.SymCalcStep5.lapPow 1 w x
      = Work.Diff.STE.seriesFun
          (fun k => (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
            * Work.Diff.STE.fourierCoeff w k) x := by
    rw [show Work.Diff.STE.B3.SymCalcStep5.lapPow 1 w = Work.Diff.STE.seriesFun
        (fun k => ((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ 1 : ℝ)) : ℂ)
          * Work.Diff.STE.fourierCoeff w k) from rfl]
    congr 1
    funext k
    rw [pow_one]
  -- the two coefficient families are negatives of each other
  have h3 : Work.Diff.STE.seriesFun
        (fun k => - (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
          * Work.Diff.STE.fourierCoeff w k) x
      = - Work.Diff.STE.seriesFun
          (fun k => (((Work.Diff.STE.B3.SymCalc.flatLam k : ℝ)) : ℂ)
            * Work.Diff.STE.fourierCoeff w k) x := by
    simp only [Work.Diff.STE.seriesFun]
    rw [← tsum_neg]
    exact tsum_congr fun k => by ring
  rw [h2, h1, h3, neg_neg]

end Work.Diff.STE.B3.SymCalcStep6
