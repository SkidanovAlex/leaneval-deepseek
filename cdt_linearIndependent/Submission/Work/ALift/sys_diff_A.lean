import Mathlib
import Submission.Work.ALift.defs

/-!
# Area ALift — holomorphy of the pulled-back system on the annulus

On the annulus `1/31 < ‖z‖ < 1` the lift `Φ` of `φ_A` stays away from the singularities
`0, 1, 1/9` of the Zagier operator (`Phi_avoid`), so both matrix entries `-R(Φ z)/P(Φ z)`,
`-Q(Φ z)/P(Φ z)` and the inhomogeneity entry `(b + c/(1-Φ z))/P(Φ z)` are holomorphic there
(they are rational functions in `Φ z`, and `Φ` is holomorphic because the annulus lies inside the
unit disc).  Together with the prefactor `deriv Φ z` this gives the hypotheses required by
`OdeContinuation`.
-/

open Metric

namespace Work.ALift

open Submission.CDTPlan

noncomputable section

/-- Holomorphy of the pulled-back system on the annulus `r₀ < ‖z‖ < 1`. -/
theorem sys_diff_A (b c : ℤ) (Φ : ℂ → ℂ)
    (hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1))
    (hav : ∀ z : ℂ, 1 / 31 < ‖z‖ → ‖z‖ < 1 → Pd (Φ z) ≠ 0 ∧ (1 - Φ z) ≠ 0) :
    DifferentiableOn ℂ (sysA Φ) {z : ℂ | 1 / 31 < ‖z‖ ∧ ‖z‖ < 1} ∧
      DifferentiableOn ℂ (sysb b c Φ) {z : ℂ | 1 / 31 < ‖z‖ ∧ ‖z‖ < 1} := by
  set s : Set ℂ := {z : ℂ | 1 / 31 < ‖z‖ ∧ ‖z‖ < 1} with hs
  have hmem : ∀ z ∈ s, z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [hs] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.2
  have hΦs : DifferentiableOn ℂ Φ s := hΦdiff.mono hmem
  have hder : DifferentiableOn ℂ (deriv Φ) s := (hΦdiff.deriv isOpen_ball).mono hmem
  have hPd : DifferentiableOn ℂ (fun z => Pd (Φ z)) s := by
    simp only [Pd]
    exact (hΦs.mul ((differentiableOn_const 1).sub hΦs)).mul
      ((differentiableOn_const 1).sub (hΦs.const_mul 9))
  have hQd : DifferentiableOn ℂ (fun z => Qd (Φ z)) s := by
    simp only [Qd]
    exact ((differentiableOn_const 1).sub (hΦs.const_mul 20)).add
      ((hΦs.pow 2).const_mul 27)
  have hRd : DifferentiableOn ℂ (fun z => Rd (Φ z)) s := by
    simp only [Rd]
    simpa only [add_comm] using (hΦs.const_mul 9).add_const (-3)
  have hne : ∀ z ∈ s, Pd (Φ z) ≠ 0 := by
    intro z hz
    rw [hs] at hz
    exact (hav z hz.1 hz.2).1
  have hne1 : ∀ z ∈ s, (1 - Φ z) ≠ 0 := by
    intro z hz
    rw [hs] at hz
    exact (hav z hz.1 hz.2).2
  have h21 : DifferentiableOn ℂ (fun z => -Rd (Φ z) / Pd (Φ z)) s := hRd.neg.div hPd hne
  have h22 : DifferentiableOn ℂ (fun z => -Qd (Φ z) / Pd (Φ z)) s := hQd.neg.div hPd hne
  have hrhs : DifferentiableOn ℂ (fun z => rhsA b c (Φ z) / Pd (Φ z)) s := by
    have hnum : DifferentiableOn ℂ (fun z => rhsA b c (Φ z)) s := by
      simp only [rhsA]
      exact (differentiableOn_const ((b : ℂ))).add
        ((differentiableOn_const ((c : ℂ))).div ((differentiableOn_const 1).sub hΦs) hne1)
    exact hnum.div hPd hne
  constructor
  · unfold sysA
    rw [differentiableOn_pi]
    intro i
    rw [differentiableOn_pi]
    intro j
    fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
      reduceIte, Pi.zero_apply, sub_eq_add_neg]
    · exact hder.mul_const 0
    · exact hder.mul_const 1
    · exact hder.mul h21
    · exact hder.mul h22
  · unfold sysb
    rw [differentiableOn_pi]
    intro i
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, reduceIte]
    · exact hder.mul_const 0
    · exact hder.mul hrhs

end

end Work.ALift
