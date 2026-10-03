/-
# Parseval for a character sum over a subset of `ZMod Q`

The first sub-lemma of the `(lin-1)`/`(lin-2)` pair of the §8 adelic form
(`Work.KMTPlan.A6.AdelicFormPropRange`'s clauses (5)–(8)): the `ℓ²(ZMod Q)`-norm of a *subset* of the
characters of `ZMod Q`, with arbitrary coefficients, is the `ℓ²`-norm of the coefficients.  This is
what turns the `ℓ²(ZMod Q)`-variational datum `VrLiftDataP R Q` of the §8 packet
`u n X θ = Σ_{α} e(-θ.val·α)·W α X` into the *residue datum* of the amplitude family `n ↦ (α ↦ W_{α,n})`,
whose bound is the paper's `(lin-1)`/`(lin-2)`.

The `ℝ`-valued form proved here is
`∑_{θ : ZMod Q} ‖∑_{a ∈ A} e(-aθ)·c a‖² = Q · ∑_{a ∈ A} ‖c a‖²`;
the `eLpNorm`-valued wrapper (with `Work.KMTPlan.A6.zmodProb Q`) is a short `ENNReal` conversion
using `Work.KMTPlan.A6.eLpNorm_two_zmodProb`.

Proof: extend `c` by zero to `c'` on all of `ZMod Q` (via `Finset.sum_ite_mem`), so that the character
sum is `ZMod.dft c'` (`Work.KMTPlan.Bile.dft_expand`); then the sesquilinear Plancherel identity
`Work.KMTPlan.Bile.dft_mul_star_sum` gives `∑_θ dft c' θ · star (dft c' θ) = Q · ∑_j c' j · star (c' j)`,
and `‖z‖² = (z · star z).re` (`Complex.mul_conj`, `Complex.normSq_eq_norm_sq`).
-/
import Mathlib
import Submission.Work.KMTPlan.Bile.sum_bileCoeff_norm_sq

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- `‖z‖² = (z * star z).re` for `z : ℂ`. -/
private lemma normSq_eq_re_mul_star (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  rw [show (z * star z).re = ‖z‖ ^ 2 from by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]]

/-- **Parseval for a character sum over a subset of `ZMod Q`.** -/
theorem sum_normSq_charSum (Q : ℕ) [NeZero Q] (A : Finset (ZMod Q)) (c : ZMod Q → ℂ) :
    ∑ θ : ZMod Q, ‖∑ a ∈ A, (ZMod.stdAddChar (-(a * θ)) : ℂ) * c a‖ ^ 2
      = (Q : ℝ) * ∑ a ∈ A, ‖c a‖ ^ 2 := by
  classical
  set c' : ZMod Q → ℂ := fun a => if a ∈ A then c a else 0 with hc'
  -- `g` is the DFT of `c'`
  have hfun : ∀ θ : ZMod Q, (∑ a ∈ A, (ZMod.stdAddChar (-(a * θ)) : ℂ) * c a)
      = ZMod.dft c' θ := by
    intro θ
    calc (∑ a ∈ A, (ZMod.stdAddChar (-(a * θ)) : ℂ) * c a)
        = ∑ a : ZMod Q, (if a ∈ A then (ZMod.stdAddChar (-(a * θ)) : ℂ) * c a else 0) := by
          rw [Finset.sum_ite_mem Finset.univ A, Finset.univ_inter]
      _ = ∑ a : ZMod Q, ZMod.stdAddChar (-(a * θ)) * c' a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hc']
          by_cases ha : a ∈ A <;> simp [ha]
      _ = ZMod.dft c' θ := (Work.KMTPlan.Bile.dft_expand (Q := Q) c' θ).symm
  -- the `ℓ²`-sum of `c'` restricted to `A`
  have hc'sum : (∑ j : ZMod Q, c' j * star (c' j)) = ∑ a ∈ A, c a * star (c a) := by
    calc (∑ j : ZMod Q, c' j * star (c' j))
        = ∑ j : ZMod Q, (if j ∈ A then c j * star (c j) else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hc']
          by_cases hj : j ∈ A <;> simp [hj]
      _ = ∑ a ∈ A, c a * star (c a) := by
          rw [Finset.sum_ite_mem Finset.univ A, Finset.univ_inter]
  have hdft : (∑ θ : ZMod Q, ZMod.dft c' θ * star (ZMod.dft c' θ))
      = (Q : ℂ) * ∑ a ∈ A, c a * star (c a) := by
    rw [Work.KMTPlan.Bile.dft_mul_star_sum, hc'sum]
  calc ∑ θ : ZMod Q, ‖∑ a ∈ A, (ZMod.stdAddChar (-(a * θ)) : ℂ) * c a‖ ^ 2
      = ∑ θ : ZMod Q, ‖ZMod.dft c' θ‖ ^ 2 :=
        Finset.sum_congr rfl fun θ _ => by rw [hfun θ]
    _ = ∑ θ : ZMod Q, (ZMod.dft c' θ * star (ZMod.dft c' θ)).re :=
        Finset.sum_congr rfl fun θ _ => normSq_eq_re_mul_star _
    _ = (∑ θ : ZMod Q, ZMod.dft c' θ * star (ZMod.dft c' θ)).re :=
        (map_sum Complex.reCLM (fun θ : ZMod Q => ZMod.dft c' θ * star (ZMod.dft c' θ))
          Finset.univ).symm
    _ = (((Q : ℂ) * ∑ a ∈ A, c a * star (c a))).re := by rw [hdft]
    _ = (Q : ℝ) * ∑ a ∈ A, ‖c a‖ ^ 2 := by
        have hre := Complex.re_ofReal_mul (Q : ℝ) (∑ a ∈ A, c a * star (c a))
        rw [show ((Q : ℂ) * (∑ a ∈ A, c a * star (c a))).re
            = (Q : ℝ) * (∑ a ∈ A, c a * star (c a)).re from by simpa using hre]
        congr 1
        exact (calc Complex.reCLM (∑ a ∈ A, c a * star (c a))
            = ∑ a ∈ A, Complex.reCLM (c a * star (c a)) :=
              map_sum Complex.reCLM (fun a : ZMod Q => c a * star (c a)) A
          _ = ∑ a ∈ A, ‖c a‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              rw [Complex.reCLM_apply, normSq_eq_re_mul_star])

end Work.KMTPlan.A6Clean
