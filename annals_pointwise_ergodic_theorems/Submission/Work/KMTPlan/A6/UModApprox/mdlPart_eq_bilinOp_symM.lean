/-
# The model half of the large-scale single-scale model approximation

`Work.KMTPlan.A6.UModApprox.mdlPart_eq_bilinOp_symM`: on the guard, the §6 model operator
`mdlPart` is the bilinear convolution with the coefficient kernel of the model symbol `symM`.

The proof composes the two ingredients proved elsewhere:

* `Work.KMTPlan.A6.mdlPart_eq_bilinOp_maeKmod` — the model operator is `bilinOp` with the
  `t`-integral of the composition of the cumulative-height arithmetic kernel with the two
  exact-height bump kernels (the §6 functional calculus `bn-ident` in kernel form, which needs the
  non-aliasing of `(lᵢ, -u)` and the two `SupportedInArc` plateau conditions);
* `Work.KMTPlan.A6.UModApprox.maeKmod_eq_coeff2_symM` — that kernel is the coefficient kernel of
  `symM` (the arithmetic fibre collapse).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.mdlPart_eq_bilinOp_maeKmod
import Submission.Work.KMTPlan.A6.UModApprox.maeKmod_eq_coeff2_symM

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-- **The model half.**  On the guard `loGuard`, with the two `SupportedInArc` plateau conditions
and the non-aliasing of each arithmetic-frequency set at the window scale, the §6 model operator
`mdlPart` is the bilinear convolution with `coeff2 (symM …)`. -/
theorem mdlPart_eq_bilinOp_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hN : 1 ≤ Nat.floor (a n))
    (hcore : Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ n)
    (hnA₁ : Work.Analysis.IonescuWainger.NonAliasing
      (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hnA₂ : Work.Analysis.IonescuWainger.NonAliasing
      (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hΦ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
      (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1)
      (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)))
    (hΦ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)))
    (hnAc₁ : Work.Analysis.IonescuWainger.NonAliasing
      (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hnAc₂ : Work.Analysis.IonescuWainger.NonAliasing
      (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hs₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc
          (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))))
    (hs₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc
          (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))) :
    Work.KMTPlan.A6.mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp (fun u v => Work.KMTPlan.A6.coeff2
          (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) u v) f g x := by
  rw [Work.KMTPlan.A6.mdlPart_eq_bilinOp_maeKmod ρ hρ hρ1 P hd C₀ a l₁ l₂ k₁ k₂ n f g
    hf hg hnA₁ hnA₂ hcore hΦ₁ hΦ₂ x]
  rw [UModApprox.maeKmod_eq_coeff2_symM ρ hρ hρ1 P (le_trans (by norm_num) hd) a l₁ l₂ k₁ k₂ n
    hN hnAc₁ hnAc₂ hs₁ hs₂]

end

end Work.KMTPlan.A6.UModApprox
