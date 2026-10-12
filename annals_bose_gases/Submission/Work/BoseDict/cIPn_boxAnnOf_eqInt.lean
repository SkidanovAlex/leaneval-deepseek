import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.cIPn_boxAnnOf_eq_prodInt
import Submission.Work.BoseDict.cIPn_term_eq_prodInt
import Submission.Work.BoseDict.integrable_termOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.cIPn_boxAnnOf_eqInt`

The box ↔ model dictionary identity expressing the **adjointness** of the box annihilator
`boxAnnOf e w d` and the (symmetrised) box creator `boxCreOf e w d`:

`cIPn d (boxAnnOf e w d Θ) Θ' = cIPn (d + 1) Θ (boxCreOf e w d Θ')`

for `Θ : Xn (d+1) → ℂ` symmetric under permutations of the `d+1` coordinates.

Without the hypothesis `hInt` (integrability of `η_w(z) · conj (Θ (cons z y)) · Θ' y` on
`Sp × Xn d`) the statement is FALSE, see `Submission/Work/BoseDict/_FALSE_cIPn_boxAnnOf_eq.lean`:
the `d`-particle side is an honest iterated integral while `MeasureTheory.integral` is `0` on
non-integrable functions.

The proof is the standard change of variables / Fubini computation, split into the pieces
`cIPn_boxAnnOf_eq_prodInt` (the `d`-particle side), `cIPn_term_eq_prodInt` and
`integrable_termOf` (the per-slot step on the `(d+1)`-particle side, using the symmetry of `Θ`
through `Fin.insertNth_comp_cycleRange_symm`), together with the measure preserving change of
variables `integral_insertNth` / `integrable_insertNth`
(`MeasureTheory.measurePreserving_piFinSuccAbove`).  All of them evaluate both sides at the
common product integral

`V = ∫_{Sp × Xn d} η(p₁) · conj (Θ (cons p₁ p₂)) · Θ'(p₂)`

and the last step is the arithmetic `(√(d+1))² = d+1`.

* LHS: `conj (√(d+1) ∫_z conj(η z) Θ(z,y)) = √(d+1) ∫_z η z conj(Θ(z,y))` (`integral_conj`),
  then Fubini (`integral_prod_symm`) and `integral_mul_const` give `√(d+1) · V`
  (`cIPn_boxAnnOf_eq_prodInt`);
* RHS: `boxCreOf e w d Θ' = (1/√(d+1)) Σ_j η(x_j) Θ'(x ∖ j)`; each slot-`j` integral equals `V`
  (`cIPn_term_eq_prodInt`), the sum has `d+1` terms, and `1/√(d+1) · (d+1) = √(d+1)`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

theorem cIPn_boxAnnOf_eqInt {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Θ : Work.BoseDict.Xn (d + 1) → ℂ) (hΘ : MeasureTheory.Integrable Θ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)),
      Θ (x ∘ σ) = Θ x)
    (Θ' : Work.BoseDict.Xn d → ℂ) (hΘ' : MeasureTheory.Integrable Θ')
    (hInt : MeasureTheory.Integrable
      (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d =>
        Work.BoseDict.etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2)) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e w d Θ) Θ'
      = Work.BoseDict.cIPn (d + 1) Θ (Work.BoseDict.boxCreOf e w d Θ') := by
  classical
  -- Both sides are expressed through the common product integral `V`.
  set V : ℂ := ∫ p : Sp × Xn d,
    etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2 with hV
  have hL : cIPn d (boxAnnOf e w d Θ) Θ' = (Real.sqrt ((d : ℝ) + 1) : ℂ) * V :=
    cIPn_boxAnnOf_eq_prodInt w Θ Θ' hInt
  have hR : cIPn (d + 1) Θ (boxCreOf e w d Θ')
      = (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) * (((d : ℂ) + 1) * V) := by
    rw [cIPn]
    simp only [boxCreOf]
    calc ∫ x : Xn (d + 1), (starRingEnd ℂ) (Θ x) *
            ((1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
              ∑ j : Fin (d + 1), etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i)))
        = (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
            ∫ x : Xn (d + 1), (starRingEnd ℂ) (Θ x) *
              ∑ j : Fin (d + 1), etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i)) := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      _ = (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
            ∑ j : Fin (d + 1), ∫ x : Xn (d + 1), (starRingEnd ℂ) (Θ x) *
              (etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i))) := by
          congr 1
          refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_)))
            (integral_finsetSum Finset.univ (f := fun j x =>
              (starRingEnd ℂ) (Θ x) * (etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i))))
              (fun j _ => integrable_termOf w j Θ Θ' hΘsym hInt))
          simp only [Finset.mul_sum]
      _ = (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) * ∑ _j : Fin (d + 1), V := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => cIPn_term_eq_prodInt w j Θ Θ' hΘsym)
      _ = (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) * (((d : ℂ) + 1) * V) := by
          congr 1
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [hL, hR]
  -- `(√(d+1))² = d+1` finishes the arithmetic.
  have hsq : (Real.sqrt ((d : ℝ) + 1) : ℂ) * (Real.sqrt ((d : ℝ) + 1) : ℂ)
      = ((d : ℂ) + 1) := by
    have h : Real.sqrt ((d : ℝ) + 1) * Real.sqrt ((d : ℝ) + 1) = (d : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    rw [← Complex.ofReal_mul, h]
    push_cast
    ring
  have hne : (Real.sqrt ((d : ℝ) + 1) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hx : (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
        (((Real.sqrt ((d : ℝ) + 1) : ℂ) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) * V)
      = (Real.sqrt ((d : ℝ) + 1) : ℂ) * V := by
    calc (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
          (((Real.sqrt ((d : ℝ) + 1) : ℂ) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) * V)
        = ((1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
            ((Real.sqrt ((d : ℝ) + 1) : ℂ) * V) := by ring
      _ = 1 * ((Real.sqrt ((d : ℝ) + 1) : ℂ) * V) := by rw [one_div_mul_cancel hne]
      _ = (Real.sqrt ((d : ℝ) + 1) : ℂ) * V := by ring
  rw [← hsq, hx]

end Work.BoseDict
