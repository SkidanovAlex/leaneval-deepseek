import Mathlib
import Submission.Work.StemsB.collarClutch
import Submission.Work.StemsB.serreSphere_collar_les_degenerates

/-!
# The two clutching maps at a point of the collar

`Work.StemsB.collarClutchG : C × F_G → O × F_O` and `collarClutchO : C × F_O → G × F_G` compare the
two trivialisations of `p` over the collar.  Evaluating them at a fixed point `x₀` of the collar
(`x₀ = collarShellPt`, the shell point, which lies in `sphLoopCollar b`) gives two maps between the
**fibres** of `p`:

  `collarLambdaPat  : F_G = p⁻¹{d_G.1} ⟶ F_O = p⁻¹{∞}`,
  `collarLambdaOat  : F_O ⟶ F_G`,

whose induced maps on cohomology are the two specific ring maps used in the derivation argument
(`D2_PLAN_SESSION_NEXT.md` §1 Step 2 and Step 4): `ρ = collarLambdaOat^*` is the transport from the
collar's fibre `Y` to the fibre `Fsp = WangCohFsp`, and `λ_pt^* = collarLambdaPat^*` is the
`1 ⊗`-component (`α`) of the clamping map.  The homotopy `λ_pt ∘ λ_O-pt ≃ id` is what makes
`ρ ∘ λ_pt^* = id`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The shell point, viewed as a point of the outer piece. -/
def collarShellPtOuter (b : ℕ) (hb : 1 ≤ b) : ↥(sphLoopOuter b) :=
  ⟨sphShellPt b, (sphShellPt_mem_sphLoopCollar b hb).1⟩

/-- The shell point lies in the collar, as a membership of the product collar
`↥(sphLoopOuter b) × F_O`. -/
theorem collarShellPtOuter_mem (b : ℕ) (hb : 1 ≤ b) :
    ((collarShellPtOuter b hb : ↥(sphLoopOuter b)) : SphModel b) ∈ sphLoopCollar b :=
  sphShellPt_mem_sphLoopCollar b hb

/-- The section of the product collar cut out by the *outer* piece:
`F_O → {z : O × F_O | z.1 ∈ C}`. -/
def collarSectionOuter (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) :
    C(↥(p ⁻¹' {(dOuter b).1}), ↥(sphLoopCollarProdOuter b ↥(p ⁻¹' {(dOuter b).1}))) :=
  ⟨fun y => ⟨(collarShellPtOuter b hb, y), collarShellPtOuter_mem b hb⟩, by fun_prop⟩

/-- **The clutching map at the shell point** `λ_pt : F_G → F_O`. -/
def collarLambdaPat (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' {d_G.1}), ↥(p ⁻¹' {(dOuter b).1})) :=
  (collarLambdaG b p d_G hT_G hT_O).comp
    (collarSection (Y := ↥(p ⁻¹' {d_G.1})) b hb)

/-- **The inverse clutching map at the shell point** `λ_O-pt : F_O → F_G`. -/
def collarLambdaOat (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' {(dOuter b).1}), ↥(p ⁻¹' {d_G.1})) :=
  (collarLambdaO b p d_G hT_G hT_O).comp (collarSectionOuter (E := E) b hb p)

end

end Work.StemsB
