import Mathlib
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.Gluing3
import Submission.Work.Stems.Hur2b.WedgeArr
import Submission.Work.Stems.Hur2b.PsiCancel
import Submission.Work.Stems.Hur2b.psiFunCancel_seam_agree
import Submission.Work.Stems.Hur2b.psiFunCancel_boundary
import Submission.Work.Stems.Hur2b.homotopic_const_of_boundary_const
import Submission.Work.Stems.CollapseDefs
import Submission.Work.Stems.exists_collapsingMap
import Submission.Work.Stems.Hur2b.WedgeArr
import Submission.Work.Stems.Hur2b.CutLemma
import Submission.Work.Stems.Hur2b.GluingCancel
import Submission.Work.Stems.Hur2b.GluingModel
import Submission.Work.Stems.Hur2b.collapseModel_class_eq_one
import Submission.Work.Stems.Hur2b.cl_cut_vertical
import Submission.Work.Stems.Hur2b.collapse_model_class_eq_prod6

/-!
# The pinch: `cl (G ∘ ψ) = ∏ cl (layer_k)`

The status of this file and the remaining work is recorded in `PLAN_HAC.md` (SESSION 6 section).
In short:

* `assembly_class_prod` (Assembly.lean): `cl (assembly x₀ τ) = ∏_k cl (layer_k)`;
* `collapseModel_class_eq_one` : `cl (gluingMap x₀ τ ∘ ψ_collapse) = 1`;
* the missing "sum of the faces" identity `cl (G ∘ ψ) = Σ_k ε_k cl (L_k)` for the *collapse* `ψ`
  is Hutchings 2.2(b).  The designed route is the T-net model described in `PLAN_HAC.md`; the class
  machinery it needs (`cl_cut_vertical` and the two reading lemmas) is in `CutLemma.lean`
  (the reading lemmas are proved; `cl_cut_vertical` is the one remaining brick, with its proof
  plan recorded).
-/

namespace Work.Stems.Hur2b

theorem assembly_homotopic_const {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    GenLoop.Homotopic (Work.Stems.Hur2b.assembly x₀ τ) GenLoop.const := by
  -- The pinch: for a suitable collapse `ψ`, the class of the cube model of the gluing is the
  -- *inverse* of the product of the six face classes.
  obtain ⟨ψ, hψ, hmodel⟩ := collapse_model_class_eq_prod6 x₀ τ
  -- The cancellation: the same cube model is null (the second half of Hutchings' `(2.5)`).
  have hone : cl x₀ (model x₀ τ ψ hψ) = 1 := model_class_eq_one' x₀ τ ψ hψ
  -- Hence the product of the six face classes is trivial.
  have hprod : prod6 x₀ τ = 1 := by
    refine inv_eq_one.mp (Eq.symm ?_)
    rw [← hone, hmodel]
  -- So the class of the assembly is trivial, hence the assembly is based-homotopic to the constant.
  have hcl : (⟦assembly x₀ τ⟧ : HomotopyGroup (Fin 2) X x₀) = ⟦GenLoop.const⟧ := by
    have : cl x₀ (assembly x₀ τ) = 1 := by rw [assembly_class_prod, hprod]
    exact this.trans HomotopyGroup.one_def
  exact Quotient.exact hcl

end Work.Stems.Hur2b
