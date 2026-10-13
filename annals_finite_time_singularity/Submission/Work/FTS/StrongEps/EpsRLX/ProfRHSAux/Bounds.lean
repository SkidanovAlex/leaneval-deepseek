/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/Bounds` — the pointwise bounds on `ℛ(Φ̃_tot)`, `U(Φ̃_tot)`, `V(Φ̃_tot)`

At fixed `z > 0`, the operators `ℛ` and `V` applied to the total stream function are bounded on
the open quadrant, and `U(Φ̃_tot)` is divisible by `sin 2θ` with a bounded quotient.  These are the
inputs to the vanishing of the term `N` of the profile right-hand side at the angular boundary.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Extract
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamOps
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise bounds on `ℛ(Φ̃_tot)`, `U(Φ̃_tot)`, `V(Φ̃_tot)` -/

/-- **`ℛ(Φ̃_tot)` is bounded on the open quadrant** (at fixed `z > 0`). -/
theorem RopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (PsiTot α Φs W Φg) z θ| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Rop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).1
  have h2 := (hC₂ hz hθ0 hθ1).1
  calc |Work.Construction.Rop α (PsiStar α Φs) z θ
        + Work.Construction.Rop α (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Rop α (PsiStar α Φs) z θ|
        + |Work.Construction.Rop α (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add h1 h2

/-- **`V(Φ̃_tot)` is bounded on the open quadrant** (at fixed `z > 0`). -/
theorem VopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (PsiTot α Φs W Φg) z θ| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Vop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).2.1
  have h2 := (hC₂ hz hθ0 hθ1).2.1
  calc |Work.Construction.Vop (PsiStar α Φs) z θ
        + Work.Construction.Vop (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Vop (PsiStar α Φs) z θ|
        + |Work.Construction.Vop (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add h1 h2

/-- **`U(Φ̃_tot)` is divisible by `sin 2θ`, with a bounded quotient** (at fixed `z > 0`). -/
theorem UopPsiBound {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : ℝ → ℝ → ℝ}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ| ≤ C * |Work.Construction.s2 θ| := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := star_op_bounds hstar
  obtain ⟨C₂, hC₂0, hC₂⟩ := ell_op_bounds hα.1 hα.2 hell
  have hWm : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro θ hθ0 hθ1
  rw [Uop_PsiTot_eq hα.1 hα.2 hstar.smooth hW.reg hWm hell.smooth hz hθ0 hθ1]
  have h1 := (hC₁ hz hθ0 hθ1).2.2
  have h2 := (hC₂ hz hθ0 hθ1).2.2
  calc |Work.Construction.Uop α (PsiStar α Φs) z θ
        + Work.Construction.Uop α (PsiEll α W Φg) z θ|
      ≤ |Work.Construction.Uop α (PsiStar α Φs) z θ|
        + |Work.Construction.Uop α (PsiEll α W Φg) z θ| := abs_add_le _ _
    _ ≤ C₁ * |Work.Construction.s2 θ| + C₂ * |Work.Construction.s2 θ| := add_le_add h1 h2
    _ = (C₁ + C₂) * |Work.Construction.s2 θ| := by ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
