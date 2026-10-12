import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
import Submission.Work.BoseDict.modeProd_cIPn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `conj (η_w) · M_α` against the last-particle insertion

The dictionary needs the integrability of the `z`-integrand which appears when the box
annihilation `Work.BoseDict.boxAnnOf e w d` is applied to a mode product:

  `z ↦ conj (η_w z) · M_α (Fin.cons z y)`,   `M_α = modeProd e (d+1) α`,  `η_w = Σ_l w_l e_l`.

The point is that the insertion `z ↦ (Fin.cons z y)` puts `z` in the *first* slot and the
remaining `d` slots carry the fixed configuration `y`; expanding the symmetric mode product
over labellings `σ : Fin (d+1) → Fin m` therefore leaves exactly *one* mode factor depending
on `z`, namely `e (σ 0)`.  Hence each summand of the expansion is a constant (in `z`) times
the two-mode factor `conj (e l) * e (σ 0)`, which is integrable because the modes are
essentially bounded and supported in the finite-measure box (`modeAux.integrable_star_mul`).

* `integrable_star_modeProd_cons` — the single-mode version `conj (e l) · M_α (Fin.cons · y)`;
* `integrable_conj_etaOf_mul` — the superposition `conj (η_w) · g` for any `g` whose mode
  products `conj (e l) · g` are integrable.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDictC

set_option linter.unusedVariables false

/-- The single-mode integrand: `conj (e l) · M_α (Fin.cons · y)` is integrable.  Expanding
`M_α` over labellings, only the `σ 0` slot is evaluated at the variable `z`. -/
lemma integrable_star_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (α : Fin m →₀ ℕ) (y : Work.BoseDict.Xn d) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Sp =>
      (starRingEnd ℂ) (e l z) * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)) := by
  have hpt : (fun z : Work.BoseDict.Sp =>
        (starRingEnd ℂ) (e l z) * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y))
      = fun z : Work.BoseDict.Sp => ∑ σ : Fin (d + 1) → Fin m,
          ((if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ i : Fin d, e (σ i.succ) (y i))
            * ((starRingEnd ℂ) (e l z) * e (σ 0) z) := by
    funext z
    rw [Work.BoseDict.modeProd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  rw [hpt]
  exact integrable_finsetSum _ fun σ _ =>
    (Work.BoseDict.modeAux.integrable_star_mul hbdd hsupp l (σ 0)).const_mul _

/-- The superposition: `conj (η_w) · g` is integrable as soon as every single-mode product
`conj (e l) · g` is.  Indeed `η_w = Σ_l w_l e_l` with real coefficients `w_l`. -/
lemma integrable_conj_etaOf_mul {m : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} {w : Fin m → ℝ}
    {g : Work.BoseDict.Sp → ℂ}
    (hg : ∀ l, MeasureTheory.Integrable (fun z : Work.BoseDict.Sp =>
      (starRingEnd ℂ) (e l z) * g z)) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Sp =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * g z) := by
  have hpt : (fun z : Work.BoseDict.Sp =>
        (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * g z)
      = fun z : Work.BoseDict.Sp =>
          ∑ l : Fin m, (w l : ℂ) * ((starRingEnd ℂ) (e l z) * g z) := by
    funext z
    rw [Work.BoseDict.etaOf, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [hpt]
  exact integrable_finsetSum _ fun l _ => (hg l).const_mul _

theorem integrable_conj_etaOf_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {α : Fin m →₀ ℕ} (hα : α.sum (fun _ k => k) = d + 1) (y : Work.BoseDict.Xn d) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Sp =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e w z)
        * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)) := by
  refine integrable_conj_etaOf_mul (w := w)
    (g := fun z : Work.BoseDict.Sp =>
      Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)) (fun l => ?_)
  exact integrable_star_modeProd_cons hbdd hsupp l α y

end Work.BoseDictC
