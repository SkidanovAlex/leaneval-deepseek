/-
# `Btwist_eq_fiberSum`: the twisted bilinear multiplier as an average of fibre products

This module proves the paper's `form-1` factorisation of the twisted bilinear multiplier of
Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), §8, in the form in which the large-scale estimate consumes it:

  `Btwist ρ P l₁ l₂ m₁ m₂ h k x = q⁻¹ ∑_{n₀ < q} (fiberOp ρ l₁ m₁ n₀ h x) · (fiberOpP ρ P l₂ m₂ n₀ k x)`,

with `q = arithQ ρ (max l₁ l₂)` the common period of the arithmetic frequencies of height
`≤ max l₁ l₂`.  In words: the twisted bilinear multiplier is the average over the residues
`n₀ ∈ ℤ/qℤ` (the "fibres" of the adelic integers) of the *products of the two linear fibres*
`fiberOp ρ lᵢ mᵢ n₀`, so that a bilinear estimate for `Btwist` follows from a *linear* estimate
for the fibres together with Hölder's inequality in the fibre variable `n₀` (this is exactly how
`Work.KMTAreas.A7.fiberVarSampling` / `residueLp_mul_le` use it).

## Structure of the proof

`Btwist` is the double `tsum` over `(j₁,j₂) ∈ ℤ²` of the kernel
`arithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂ · h (x-j₁) · k (x-j₂)`.  Two ingredients:

* *pointwise* (`Work.KMTAreas.A7.arithKernel_fiberTerm`, from `arithKernel_eq_arithChar`): the
  kernel is the finite average over the residues `n₀ < q` of the products of the two **fibre
  terms** `(arithChar ρ l₁ (n₀-j₁) · cw m₁ j₁ · h (x-j₁)) · (arithChar ρ l₂ (P(n₀)-j₂) · cw m₂ j₂ · k (x-j₂))`;
* *summability bookkeeping* (`tsum_tsum_finset_factor` below): for a double `tsum` of a finite sum
  of products `∑_{n∈S} u n j₁ · v n j₂`, where each `u n` and each `v n` is summable, the sums may
  be interchanged, giving `∑_{n∈S} (∑' j₁, u n j₁) · (∑' j₂, v n j₂)`.

The summability hypotheses of the statement (`h₁`, `h₂`) are precisely the summability of the two
fibre families at each residue, i.e. they are exactly what the second step needs (the individual
fibres `fiberOp ρ l₁ m₁ n₀ h x`, `fiberOpP ρ P l₂ m₂ n₀ k x` are the `tsum`s appearing there).
Note that no *absolute* summability of the *product* kernel family is assumed: the identity is
proved by pushing the constant `q⁻¹` and the finite residue sum out of the two `tsum`s separately,
which is legitimate as soon as each of the two one-variable fibres is summable.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.A7.arithKernel_fiberTerm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **Interchange of a double `tsum` with a finite sum of products.**  If `u n` and `v n` are
summable for every `n ∈ S`, then

  `∑' j₁, ∑' j₂, ∑_{n∈S} u n j₁ · v n j₂ = ∑_{n∈S} (∑' j₁, u n j₁) · (∑' j₂, v n j₂)`.

The proof is the finite-sum exchange `hasSum_sum` in each of the two `tsum`s (`tsum_sum` is not
available under that name in this Mathlib), together with `tsum_mul_left`/`tsum_mul_right`. -/
lemma tsum_tsum_finset_factor (S : Finset ℕ) (u v : ℕ → ℤ → ℂ)
    (hu : ∀ n ∈ S, Summable (u n)) (hv : ∀ n ∈ S, Summable (v n)) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, (∑' j₁ : ℤ, u n j₁) * (∑' j₂ : ℤ, v n j₂) := by
  have inner : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, u n j₁ * (∑' j₂ : ℤ, v n j₂) := by
    intro j₁
    rw [((hasSum_sum (fun n hn => ((hv n hn).mul_left (u n j₁)).hasSum)).tsum_eq)]
    exact Finset.sum_congr rfl fun n _ => tsum_mul_left
  rw [tsum_congr inner]
  rw [((hasSum_sum (fun n hn => (((hu n hn).mul_right (∑' j₂ : ℤ, v n j₂))).hasSum)).tsum_eq)]
  exact Finset.sum_congr rfl fun n _ => tsum_mul_right

theorem Btwist_eq_fiberSum (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ)
    (x : ℤ)
    (h₁ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j) * Work.KMTAreas.A7.cw m₁ j * h (x - j)))
    (h₂ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j) * Work.KMTAreas.A7.cw m₂ j * k (x - j))) :
    Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k x
      = (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℂ)⁻¹ *
          ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
            Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) m₁ (n₀ : ℤ) h x
              * Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) m₂ (n₀ : ℤ) k x := by
  classical
  -- The double `tsum` of the pointwise fibre form equals the finite sum of fibre products.
  have hfin : (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
        (arithChar ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
          * (arithChar ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
      = ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          fiberOpSet (iwArithFreqs ρ l₁) m₁ (n₀ : ℤ) h x
            * fiberOpPSet P (iwArithFreqs ρ l₂) m₂ (n₀ : ℤ) k x := by
    rw [tsum_tsum_finset_factor (Finset.range (arithQ ρ (max l₁ l₂)))
        (fun n j => arithChar ρ l₁ ((n : ℤ) - j) * cw m₁ j * h (x - j))
        (fun n j => arithChar ρ l₂ (P.eval (n : ℤ) - j) * cw m₂ j * k (x - j))
        (fun n _ => h₁ (n : ℤ)) (fun n _ => h₂ (n : ℤ))]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [fiberOpSet, fiberOpPSet, arithCharSet_iwArithFreqs]
  simp only [Btwist]
  rw [tsum_congr (fun j₁ => tsum_congr (fun j₂ =>
    arithKernel_fiberTerm ρ P l₁ l₂ m₁ m₂ h k x j₁ j₂))]
  simp only [tsum_mul_left]
  rw [hfin]

end

end Work.KMTAreas.A7
