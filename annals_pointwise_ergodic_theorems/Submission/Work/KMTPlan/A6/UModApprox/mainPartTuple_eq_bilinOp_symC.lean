/-
# The concrete column of the large-scale low case is the bilinear convolution with `coeff2 symC`

`Work.KMTPlan.A6.UModApprox.mainPartTuple_eq_bilinOp_symC`: on the guard
`loGuard ρ C₀ a l₁ l₂ k₁ k₂ n` (the common `if`-test of `mainPartTuple` and `mdlPart`), the
concrete large-scale column `mainPartTuple` — the §5 halved average `Ã_N(F^{0,l₁,k₁}_N f,
G^{0,l₂,k₂}_N g)` of the two exact-height pieces — is the bilinear convolution operator
(`Work.KMTAreas.A7.bilinOp`) with the coefficient kernel `coeff2 (symC ρ P ⌊a n⌋ l₁ l₂ k₁ k₂)`.

This is the general-`(l₁,l₂)` companion of `Work.KMTAreas.A7.loMainPart_eq_bilinOp_symC` (the
`l₁ = 0` case): the proof is the same replay of
`mainPartTuple_apply` → `varpPiece_eq_bilinOp_hiKconc` → `hiKconc_eq` → `cesb_kernComp_eq_coeff2_symC`
(all stated for general heights), with the boundedness of the two inputs supplied by
`Work.KMTAreas.A5.boundedZ_of_memLp` instead of being assumed.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedWinDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

theorem mainPartTuple_eq_bilinOp_symC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (h : Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ n) :
    Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp (fun u v => Work.KMTPlan.A6.coeff2
          (Work.KMTPlan.A6.symC ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) u v) f g x := by
  have hfBd : Work.KMTAreas.A5.BoundedZ f :=
    Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hf
  have hgBd : Work.KMTAreas.A5.BoundedZ g :=
    Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hg
  have hk : Work.KMTAreas.A7.hiKconc ρ P a l₁ l₂ k₁ k₂ n
      = Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) := by
    rw [Work.KMTAreas.A7.hiKconc_eq ρ hρ hρ1 P a l₁ l₂ k₁ k₂ n]
    show Work.KMTAreas.A7.kernComp (Work.KMTAreas.A7.khalf (Nat.floor (a n)) P)
        (Work.KMTAreas.A7.hiKer ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) k₁))
        (Work.KMTAreas.A7.hiKer ρ l₂
          (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) k₂))
      = Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂)
    exact Work.KMTPlan.A6.cesb_kernComp_eq_coeff2_symC ρ hρ hρ1 P l₁ l₂ k₁ k₂
      (Nat.floor (a n))
  rw [Work.KMTAreas.A7.mainPartTuple_apply, if_pos h,
    Work.KMTAreas.A7.varpPiece_eq_bilinOp_hiKconc ρ P a l₁ l₂ k₁ k₂ n hfBd hgBd x,
    hk]

end

end Work.KMTPlan.A6.UModApprox
