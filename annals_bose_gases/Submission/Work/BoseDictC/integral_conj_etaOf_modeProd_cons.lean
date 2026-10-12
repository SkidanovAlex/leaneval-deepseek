import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.modeProd_cIPn
import Submission.Work.BoseDictC.modeProd_cons_expand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDictC.integral_conj_etaOf_modeProd_cons`

The box-side annihilation of the *superposed* one-particle function `η_w = Σ_l w_l e_l`
against the symmetric mode product `M_α = modeProd e (d+1) α`:

`∫_z conj(η_w z) M_α(z, y) = Σ_k w_k M_{α - e_k}(y)`,  `y ∈ Xn d`, `|α| = d+1`.

This is the box-side shadow of the model identity `annOf (x^α) = Σ_k w_k α_k x^{α - e_k}`
(the first-quantised form of `Work.BoseB4.annOf`), i.e. the "annihilation" row of the
box ↔ model dictionary, written in the joint (first-coordinate) form used by the a-priori
layer.

## Proof

* `modeProd_cons_expand` (module `Submission.Work.BoseDictC.modeProd_cons_expand`)
  expands the integrand pointwise as `Σ_k e_k(z) · M_{α - e_k}(y)`;
* `integral_conj_etaOf_mul_mode` (below) evaluates the only one-particle integral that
  survives, `∫_z conj(η_w z) e_k(z) = w_k`;
* the finite sum over `k` is pulled out of the Bochner integral with
  `integral_finsetSum`, the integrability of each term coming from
  `modeAux.integrable_star_mul` (each mode is bounded with support in the finite box
  `boxL ℓ`), and the `y`-dependent factor is pulled out with `integral_mul_const`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDictC

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Expanding `conj η_w` in the modes -/

/-- The conjugate of the superposed one-particle function, expanded in the modes
(the coefficients `w l` are real, so they survive conjugation unchanged). -/
lemma conj_etaOf {m : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ)
    (z : Work.BoseDict.Sp) :
    (starRingEnd ℂ) (Work.BoseDict.etaOf e w z)
      = ∑ l : Fin m, (w l : ℂ) * (starRingEnd ℂ) (e l z) := by
  rw [Work.BoseDict.etaOf, map_sum]
  exact Finset.sum_congr rfl (fun l _ => by rw [map_mul, Complex.conj_ofReal])

/-! ## 2. Integrability of `conj η_w · e_k` -/

/-- `conj η_w · e_k` is integrable: it is the finite sum `Σ_l w_l conj(e_l) e_k` of
integrable two-mode factors (`modeAux.integrable_star_mul`). -/
lemma integrable_conj_etaOf_mul_mode {m : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (k : Fin m) :
    Integrable (fun z : Work.BoseDict.Sp
      => (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * e k z) := by
  have hpt : (fun z : Work.BoseDict.Sp
        => (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * e k z)
      = fun z : Work.BoseDict.Sp =>
          ∑ l : Fin m, (w l : ℂ) * ((starRingEnd ℂ) (e l z) * e k z) := by
    funext z
    rw [conj_etaOf, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hpt]
  refine integrable_finsetSum _ (fun l _ => ?_)
  exact (Work.BoseDict.modeAux.integrable_star_mul (e := e) hbdd hsupp l k).const_mul _

/-! ## 3. The one-particle orthonormality integral -/

/-- Orthonormality of the modes against the superposed function: `∫_z conj(η_w z) e_k(z)
= w_k`.  The sum over `l` is pulled out of the Bochner integral (each summand is the
integrable product `conj(e_l) e_k`) and collapses onto `l = k` by `he`. -/
theorem integral_conj_etaOf_mul_mode {m : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp,
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (k : Fin m) :
    (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * e k z)
      = (w k : ℂ) := by
  classical
  have hpt : (∫ z : Work.BoseDict.Sp,
        (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * e k z)
      = ∫ z : Work.BoseDict.Sp,
          ∑ l : Fin m, (w l : ℂ) * ((starRingEnd ℂ) (e l z) * e k z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [conj_etaOf, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hpt, integral_finsetSum _
    (fun l _ => (Work.BoseDict.modeAux.integrable_star_mul (e := e) hbdd hsupp l k).const_mul _)]
  rw [Finset.sum_eq_single k]
  · rw [integral_const_mul, he k k, if_pos rfl, mul_one]
  · intro l _ hlk
    rw [integral_const_mul, he l k, if_neg (fun h : l = k => hlk h), mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ## 4. The assembly -/

/-- The assembly of the target from the pointwise expansion `hB` of the mode product. -/
private theorem main_of_modeProd_cons_expand {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp,
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {α : Fin m →₀ ℕ} (hα : α.sum (fun _ k => k) = d + 1)
    (y : Work.BoseDict.Xn d)
    (hB : ∀ z : Work.BoseDict.Sp,
      Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y)
        = ∑ k : Fin m, e k z * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y) :
    (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e w z)
        * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y))
      = ∑ k : Fin m, (w k : ℂ) * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y := by
  classical
  -- push the pointwise expansion into the integrand
  have hstep : (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e w z)
        * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y))
      = ∫ z : Work.BoseDict.Sp, ∑ k : Fin m,
          ((starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * e k z)
            * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hB z, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hstep, integral_finsetSum _ (fun k _ =>
    (integrable_conj_etaOf_mul_mode (e := e) hbdd hsupp w k).mul_const _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_mul_const, integral_conj_etaOf_mul_mode (e := e) he hbdd hsupp w k]

theorem integral_conj_etaOf_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {α : Fin m →₀ ℕ} (hα : α.sum (fun _ k => k) = d + 1) (y : Work.BoseDict.Xn d) :
    (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (Work.BoseDict.etaOf e w z)
        * Work.BoseDict.modeProd e (d + 1) α (Fin.cons z y))
      = ∑ k : Fin m, (w k : ℂ) * Work.BoseDict.modeProd e d (α - Work.BoseB4.e m k) y := by
  exact main_of_modeProd_cons_expand he hbdd hsupp w hα y
    (fun z => modeProd_cons_expand hα y z)

end Work.BoseDictC
