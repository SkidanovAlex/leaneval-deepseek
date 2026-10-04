import Mathlib
import Submission.Work.Diff.EXT.ricPhiPartialDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart-Ricci `Φ` (area `EXT`)

`Work.Diff.EXT.chartRicPhi` is the coordinate (Christoffel/Koszul) expression for the Ricci matrix
of a metric as a function of the scalar `2`-jet of its chart matrix: it is a *polynomial* in the
entries of the metric coefficients, their first and second coordinate partials, and the entries of
the **inverse** Gram matrix.  The only non-polynomial ingredient is the matrix inverse, which (by
Cramer's rule, `Matrix.inv_def`) is `(det A)⁻¹ • A.adjugate`, hence smooth exactly on the open set
where `det A ≠ 0`.

This file proves that `chartRicPhi` is `C^∞` on that set.  The proof is purely algebraic/analytic:

* `det` and the entries of the adjugate are polynomial functions of the entries of the matrix
  (`Matrix.det_apply` / `Matrix.adjugate_apply` + `fun_prop`);
* on `det ≠ 0` the inverse is `(det)⁻¹ • adjugate`, a product of the smooth scalar `(det)⁻¹`
  (`ContDiffOn.inv`) with the smooth adjugate, and smoothness is closed under finite sums, products
  and the projection `z ↦ z.2.1` (`ContDiffOn.comp`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped ContDiff BigOperators
open Bundle ContDiff Set

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- The domain of `chartRicPhi`. -/
private abbrev PhiDom : Type _ :=
  E × (MatE (E := E) × (Fin (Module.finrank ℝ E) → MatE (E := E)) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E)))

/-- The open set on which `chartRicPhi` is smooth: the Gram matrix is invertible. -/
private abbrev PhiSet : Set (PhiDom (E := E)) := {z | (Matrix.of z.2.1).det ≠ 0}

/-- The determinant is a smooth (indeed polynomial) function of the entries of a matrix. -/
private lemma contDiff_det_coord :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- The determinant of a matrix whose `j`-th row has been replaced by a *fixed* vector is a
polynomial in the remaining entries (this is the adjugate entry, by Cramer's rule). -/
private lemma updateRow_det_eq (A : MatE (E := E)) (j : Fin (Module.finrank ℝ E))
    (b : Fin (Module.finrank ℝ E) → ℝ) :
    ((Matrix.of A).updateRow j b).det =
      ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)), Equiv.Perm.sign σ •
        ∏ i, (if σ i = j then b i else A (σ i) i) := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Matrix.updateRow_apply, Matrix.of_apply]

/-- Smoothness of the determinant of a matrix with one row replaced by a fixed vector. -/
private lemma contDiff_updateRow_det (j : Fin (Module.finrank ℝ E))
    (b : Fin (Module.finrank ℝ E) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun A : MatE (E := E) => ((Matrix.of A).updateRow j b).det) := by
  simp only [updateRow_det_eq]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul (Equiv.Perm.sign σ) ?_
  refine contDiff_prod fun i _ => ?_
  by_cases h : σ i = j
  · simp only [h, ↓reduceIte]; exact contDiff_const
  · simp only [h, ↓reduceIte]; fun_prop

/-- The entries of the adjugate matrix are smooth (polynomial) functions of the entries. -/
private lemma contDiff_adjugate_coord (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  exact contDiff_updateRow_det j (Pi.single i (1 : ℝ))

/-- The entries of the inverse matrix are smooth on the open set where the determinant does not
vanish: there the inverse is `(det)⁻¹ • adjugate` (Cramer's rule). -/
private lemma contDiffOn_inv_coord (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A)⁻¹ k l)
      {A | (Matrix.of A).det ≠ 0} := by
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => ((Matrix.of A).det)⁻¹)
      {A | (Matrix.of A).det ≠ 0} :=
    contDiff_det_coord.contDiffOn.inv (fun A hA => hA)
  have hadj : ContDiffOn ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).adjugate k l)
      {A | (Matrix.of A).det ≠ 0} := (contDiff_adjugate_coord k l).contDiffOn
  refine (hdet.mul hadj).congr (fun A hA => ?_)
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- The Koszul (lowered Christoffel) pairing is a smooth function of the first partials. -/
private lemma contDiff_sKz_coord (a b c : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => sKz z.2.2.1 a b c) := by
  unfold sKz
  fun_prop

/-- The derivative of the Koszul pairing is a smooth function of the second partials. -/
private lemma contDiff_sKzD_coord (m a b c : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => sKzD z.2.2.2 m a b c) := by
  unfold sKzD
  fun_prop

theorem chartRicPhi_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : E × (Work.Diff.EXT.MatE (E := E) ×
          (Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E))) =>
        Work.Diff.EXT.chartRicPhi z)
      {z | (Matrix.of z.2.1).det ≠ 0} := by
  have hproj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => z.2.1) (PhiSet (E := E)) :=
    (contDiffOn_fst (s := Set.univ)).comp contDiffOn_snd (fun _ _ => trivial)
  have hInv : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => sInv z.2.1 k l) (PhiSet (E := E)) :=
    fun k l => (contDiffOn_inv_coord k l).comp hproj (fun z hz => hz)
  have hKz : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => sKz z.2.2.1 a b c) (PhiSet (E := E)) :=
    fun a b c => (contDiff_sKz_coord a b c).contDiffOn
  have hKzD : ∀ m a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : PhiDom (E := E) => sKzD z.2.2.2 m a b c)
        (PhiSet (E := E)) :=
    fun m a b c => (contDiff_sKzD_coord m a b c).contDiffOn
  have hRm : ∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : PhiDom (E := E) => sRm z.2.1 z.2.2.1 z.2.2.2 a b c d) (PhiSet (E := E)) := by
    intro a b c d
    have h : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : PhiDom (E := E) =>
          sKzD z.2.2.2 a b d c - sKzD z.2.2.2 b a d c
            - (∑ r, ∑ s, sInv z.2.1 r s * sKz z.2.2.1 b d r * sKz z.2.2.1 a c s)
            + (∑ r, ∑ s, sInv z.2.1 r s * sKz z.2.2.1 a d r * sKz z.2.2.1 b c s))
        (PhiSet (E := E)) := by
      refine ContDiffOn.add ?_ ?_
      · refine ContDiffOn.sub ?_ ?_
        · exact (hKzD a b d c).sub (hKzD b a d c)
        · refine ContDiffOn.sum fun r _ => ContDiffOn.sum fun s _ => ?_
          exact ((hInv r s).mul (hKz b d r)).mul (hKz a c s)
      · refine ContDiffOn.sum fun r _ => ContDiffOn.sum fun s _ => ?_
        exact ((hInv r s).mul (hKz a d r)).mul (hKz b c s)
    exact h.congr (fun z hz => rfl)
  unfold chartRicPhi
  refine contDiffOn_pi.2 (fun i => contDiffOn_pi.2 (fun j => ?_))
  refine ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ => ?_
  exact (hInv k l).mul (hRm k i l j)

end Work.Diff.EXT
