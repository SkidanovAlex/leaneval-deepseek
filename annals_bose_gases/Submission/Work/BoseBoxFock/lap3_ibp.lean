import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Submission.Work.BoseBoxFock.AliasClosedAux
import Submission.Work.BoseBoxFock.NormSymAux
import Submission.Work.BoseFixR.LocaliseProof.GradientIBP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary properties of `dIter` -/

/-- Iterated directional derivatives of a smooth function are smooth. -/
lemma contDiff_dIter {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f) (L : List E3) :
    ContDiff ℝ (⊤ : ENat) (dIter f L) := by
  induction L with
  | nil => simpa using hf
  | cons v L ih =>
    have h : ContDiff ℝ (⊤ : ENat) (fun p : E3 => fderiv ℝ (dIter f L) p v) :=
      (ih.fderiv_right (by simp)).clm_apply contDiff_const
    simpa only [dIter_cons] using h

/-- Iterated directional derivatives of a compactly supported function are compactly supported
(their support is contained in the support of the function). -/
lemma hasCompactSupport_dIter {g : E3 → ℂ} (hg : HasCompactSupport g) (L : List E3) :
    HasCompactSupport (dIter g L) := by
  induction L with
  | nil => simpa using hg
  | cons v L ih =>
    refine HasCompactSupport.intro' (K := tsupport (dIter g L)) ih
      (isClosed_tsupport (dIter g L)) (fun x hx => ?_)
    show fderiv ℝ (dIter g L) x v = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp

/-- A product of a continuous function with a continuous compactly supported function is
integrable. -/
lemma integrable_mul_of_continuous {h H : E3 → ℂ} (hh : Continuous h) (hH : Continuous H)
    (hHc : HasCompactSupport H) : Integrable (fun p => h p * H p) :=
  Continuous.integrable_of_hasCompactSupport (hh.mul hH) (hHc.mul_left)

/-! ## Integration by parts, one directional derivative at a time -/

/-- **Iterated integration by parts.**  For smooth `f` and smooth compactly supported `g` and any
two lists `L`, `M` of directions,

    ∫ (∂_M f) · (∂_L g) = (-1)^{|L|} ∫ (∂_{L.reverse ++ M} f) · g ,

where `∂_L` is `dIter` (the head of the list is the *outermost* derivative).  The proof is an
induction on `L`: each step moves the leading derivative of `∂_L g` across with
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, producing one minus sign and prepending that
direction to the accumulated list `M`. -/
theorem integral_dIter_mul_eq (L M : List E3) {f g : E3 → ℂ}
    (hf : ContDiff ℝ (⊤ : ENat) f) (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    ∫ p, dIter f M p * dIter g L p
      = (-1 : ℂ) ^ L.length * ∫ p, dIter f (L.reverse ++ M) p * g p := by
  induction L generalizing M with
  | nil =>
    rw [List.reverse_nil, List.nil_append]
    simp only [dIter_nil, List.length_nil, pow_zero, one_mul]
  | cons v L' ih =>
    have hstep : (∫ p, dIter f M p * dIter g (v :: L') p)
        = -∫ p, dIter f (v :: M) p * dIter g L' p := by
      have h1 : Continuous (fun p : E3 => fderiv ℝ (dIter f M) p v) :=
        (contDiff_dIter hf (v :: M)).continuous
      have h2 : Continuous (fun p : E3 => fderiv ℝ (dIter g L') p v) :=
        (contDiff_dIter hg (v :: L')).continuous
      have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := dIter f M) (g := dIter g L') (v := v) (μ := volume)
        (integrable_mul_of_continuous h1 (contDiff_dIter hg L').continuous
          (hasCompactSupport_dIter hgc L'))
        (integrable_mul_of_continuous (contDiff_dIter hf M).continuous h2
          (hasCompactSupport_dIter hgc (v :: L')))
        (integrable_mul_of_continuous (contDiff_dIter hf M).continuous
          (contDiff_dIter hg L').continuous (hasCompactSupport_dIter hgc L'))
        (fun x _ => (contDiff_dIter hf M).differentiable (by simp) x)
        (fun x _ => (contDiff_dIter hg L').differentiable (by simp) x)
      show (∫ p, dIter f M p * (fderiv ℝ (dIter g L') p) v)
        = -∫ p, (fderiv ℝ (dIter f M) p) v * dIter g L' p
      exact hIBP
    rw [hstep, ih (v :: M)]
    have hrev : (v :: L').reverse ++ M = L'.reverse ++ (v :: M) := by
      rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    have hC : (-1 : ℂ) ^ (v :: L').length = -((-1 : ℂ) ^ L'.length) := by
      rw [show (v :: L').length = L'.length + 1 from rfl, pow_succ]
      ring
    rw [hrev, hC]
    ring

/-! ## The index set of the `27` directional derivatives, and the reversal identity -/

/-- The index type for the `27 = 3³` sixth-order derivatives of `lap3`. -/
abbrev LapIdx : Type := Fin 3 × Fin 3 × Fin 3

/-- `lap3` as a single sum over the product index type `LapIdx`. -/
lemma lap3_eq_sum (f : E3 → ℂ) :
    lap3 f = fun p => ∑ t : LapIdx, dIter f (lap3List t.1 t.2.1 t.2.2) p := by
  funext p
  simp only [lap3, Fintype.sum_prod_type]

/-- Reversing the list of directions `[e_a,e_a,e_b,e_b,e_c,e_c]` gives
`[e_c,e_c,e_b,e_b,e_a,e_a]`. -/
lemma lap3List_reverse (a b c : Fin 3) :
    (lap3List a b c).reverse = lap3List c b a := by
  simp only [lap3List, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]

/-- The involution of `LapIdx` that swaps the outer and inner indices; it implements the passage
from the reversed direction list back to the original one. -/
def lapIdxSwap : LapIdx ≃ LapIdx where
  toFun t := (t.2.2, (t.2.1, t.1))
  invFun t := (t.2.2, (t.2.1, t.1))
  left_inv := by rintro ⟨a, b, c⟩; rfl
  right_inv := by rintro ⟨a, b, c⟩; rfl

@[simp] lemma lapIdxSwap_apply (t : LapIdx) :
    lapIdxSwap t = (t.2.2, (t.2.1, t.1)) := rfl

/-- The direction list attached to `lapIdxSwap t` is the reverse of the one attached to `t`. -/
lemma lap3List_lapIdxSwap (t : LapIdx) :
    lap3List (lapIdxSwap t).1 (lapIdxSwap t).2.1 (lapIdxSwap t).2.2
      = (lap3List t.1 t.2.1 t.2.2).reverse := by
  simp only [lapIdxSwap_apply]
  exact (lap3List_reverse t.1 t.2.1 t.2.2).symm

/-! ## The main theorem -/

/-- `Δ³` is self-adjoint against a compactly supported test function: `∫ f · lap3 g = ∫ lap3 f · g`
for `f` smooth (no decay needed) and `g` smooth with compact support.
Route: `lap3 f = ∑_{a,b,c} ∂_a∂_a∂_b∂_b∂_c∂_c f` (`NormSymAux.dIter`/`lap3List`), and each of the
six directional derivatives is moved across with the single-step integration-by-parts
`MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (all test-function side
derivatives are compactly supported, so every integrability hypothesis is automatic); the sign is
`(-1)^6 = +1`. A useful auxiliary is `NormSymAux.fderiv_iteratedFDeriv_apply_eval`. -/
theorem lap3_ibp {f g : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f)
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    ∫ p, f p * Work.BoseBoxFock.lap3 g p = ∫ p, Work.BoseBoxFock.lap3 f p * g p := by
  have hA : (∫ p, f p * lap3 g p)
      = ∑ t : LapIdx, ∫ p, f p * dIter g (lap3List t.1 t.2.1 t.2.2) p := by
    rw [lap3_eq_sum]
    simp only [Finset.mul_sum]
    exact integral_finsetSum _ (fun t _ => integrable_mul_of_continuous hf.continuous
      (contDiff_dIter hg (lap3List t.1 t.2.1 t.2.2)).continuous
      (hasCompactSupport_dIter hgc (lap3List t.1 t.2.1 t.2.2)))
  have hB : (∑ t : LapIdx, ∫ p, f p * dIter g (lap3List t.1 t.2.1 t.2.2) p)
      = ∑ t : LapIdx, ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2).reverse p * g p := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have h := integral_dIter_mul_eq (L := lap3List t.1 t.2.1 t.2.2) (M := []) hf hg hgc
    simp only [length_lap3List, List.append_nil, dIter_nil] at h
    rw [show (-1 : ℂ) ^ (6 : ℕ) = 1 by norm_num, one_mul] at h
    exact h
  have hC : (∑ t : LapIdx, ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2).reverse p * g p)
      = ∑ t : LapIdx, ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2) p * g p := by
    have hcomp : (∑ t : LapIdx, ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2).reverse p * g p)
        = ∑ t : LapIdx, ∫ p, dIter f (lap3List (lapIdxSwap t).1 (lapIdxSwap t).2.1
            (lapIdxSwap t).2.2) p * g p := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [lap3List_lapIdxSwap]
    rw [hcomp]
    exact Equiv.sum_comp lapIdxSwap
      (fun t : LapIdx => ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2) p * g p)
  have hD : (∫ p, lap3 f p * g p)
      = ∑ t : LapIdx, ∫ p, dIter f (lap3List t.1 t.2.1 t.2.2) p * g p := by
    rw [lap3_eq_sum]
    simp only [Finset.sum_mul]
    exact integral_finsetSum _ (fun t _ => integrable_mul_of_continuous
      (contDiff_dIter hf (lap3List t.1 t.2.1 t.2.2)).continuous hg.continuous hgc)
  rw [hA, hB, hC, hD]

end

end Work.BoseBoxFock
