/-
# Auxiliary coordinate machinery for `transfer_rho_theta`

This file contains the change-of-coordinates plumbing used by
`Submission/Work/FTS/FireFix/Clauses/transfer_rho_theta.lean`:

* `pt3 a b t` — the point of `ℝ³` with coordinates `(a, b, t)`;
* `cx` — the measurable equivalence `ℝ³ ≃ᵐ ℝ × (ℝ × ℝ)`, `x ↦ (x 2, (x 0, x 1))` (axis coordinate
  first, then the coordinates spanning the plane), which is measure preserving;
* `lintegral_eucl3_eq_prod` — iterated-integral (Fubini) form of the same statement.
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Work.FTS.FireFix.Clauses

/-- The point of `ℝ³` (coordinates `0,1` span the plane, coordinate `2` is the axis) with
coordinates `(a, b, t)`. -/
def pt3 (a b t : ℝ) : EuclideanSpace ℝ (Fin 3) := !₂[a, b, t]

@[simp] lemma pt3_zero (a b t : ℝ) : pt3 a b t 0 = a := by simp [pt3]
@[simp] lemma pt3_one (a b t : ℝ) : pt3 a b t 1 = b := by simp [pt3]
@[simp] lemma pt3_two (a b t : ℝ) : pt3 a b t 2 = t := by simp [pt3]

@[simp] lemma pt3_prodCongr {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (e₁ : α ≃ᵐ β) (e₂ : γ ≃ᵐ δ) (a : α) (b : γ) :
    (e₁.prodCongr e₂) (a, b) = (e₁ a, e₂ b) := rfl

/-- The coordinate equivalence `ℝ³ ≃ᵐ ℝ × (ℝ × ℝ)`: `x ↦ (x 2, (x 0, x 1))`. -/
noncomputable def cx : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.finTwoArrow (α := ℝ))))

lemma cx_apply_eq (x : EuclideanSpace ℝ (Fin 3)) : cx x = (x 2, (x 0, x 1)) := by
  simp only [cx, MeasurableEquiv.trans_apply]
  rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
  simp only [pt3_prodCongr, MeasurableEquiv.refl_apply, MeasurableEquiv.finTwoArrow_apply,
    Fin.removeNth_apply]
  simp [Fin.succAbove]

/-- The inverse coordinate map. -/
lemma cx_symm_pt3 (a b t : ℝ) : cx.symm (t, (a, b)) = pt3 a b t := by
  rw [← cx.symm_apply_apply (pt3 a b t)]
  congr 1

lemma cx_symm_pt3' (t : ℝ) (v : ℝ × ℝ) : cx.symm (t, v) = pt3 v.1 v.2 t := by
  obtain ⟨a, b⟩ := v
  exact cx_symm_pt3 a b t

theorem measurePreserving_cx : MeasurePreserving cx MeasureTheory.volume MeasureTheory.volume := by
  refine MeasurePreserving.trans (μb := MeasureTheory.volume) ?_ ?_
  · exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (PiLp.volume_preserving_toLp (Fin 3))
  · refine MeasurePreserving.trans (μb := MeasureTheory.volume) ?_ ?_
    · exact volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    · exact (MeasurePreserving.id MeasureTheory.volume).prod
        (volume_preserving_finTwoArrow ℝ)

/-- **Fubini in the coordinates `(t, v)`**: an integral over `ℝ³` is an iterated integral over the
axis coordinate `t` and the plane coordinates `v`. -/
theorem lintegral_eucl3_eq_prod {g : EuclideanSpace ℝ (Fin 3) → ENNReal} (hg : Measurable g) :
    ∫⁻ x : EuclideanSpace ℝ (Fin 3), g x
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (pt3 v.1 v.2 t) := by
  have h1 : ∫⁻ p : ℝ × (ℝ × ℝ), g (cx.symm p) = ∫⁻ x : EuclideanSpace ℝ (Fin 3), g x :=
    (MeasurePreserving.symm cx measurePreserving_cx).lintegral_comp_emb
      cx.symm.measurableEmbedding g
  have h2 : ∫⁻ p : ℝ × (ℝ × ℝ), g (cx.symm p)
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (cx.symm (t, v)) := by
    rw [show (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ)))
        = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure (ℝ × ℝ))
        from rfl]
    exact lintegral_prod (fun a : ℝ × (ℝ × ℝ) => g (cx.symm a))
      (hg.comp cx.symm.measurable).aemeasurable
  rw [← h1, h2]
  exact lintegral_congr fun t => lintegral_congr fun v => congrArg g (cx_symm_pt3' t v)

end Work.FTS.FireFix.Clauses
