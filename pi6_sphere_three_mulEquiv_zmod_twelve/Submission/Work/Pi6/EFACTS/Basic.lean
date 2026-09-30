import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.StemsB.WangE4
import Submission.Work.StemsB.CollarModel
import Submission.Work.Rat.coverFibreDataSerre
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Cohomology.PairSequence
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area EFACTS: the 3-connected cover `E = S³⟨3⟩` — the geometric setup

For a Postnikov section `g3 : S³ → P₃` (`PostnikovData 3 12`, i.e. a `K(ℤ,3)`-model through `12`),
the cover `E = Ecov g3 = hofib(g3)` is `S³⟨3⟩`.  This file transports the homotopy-fibre projection
to the one-point model `SphModel 3 = OnePoint ℝ³` (where the library's Wang sequence over a sphere
lives, `Work.StemsB.wangSphereE4`), and records the fibre over `∞` together with the two fibrewise
trivialities over the contractible pieces.

Everything downstream (the Wang data, the transgression computations, the `K(ℤ,2)`-structure of the
fibre) phrases its statements in terms of the objects of this file.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

/-- The one-point model of `S³` used by the Wang sequence, as a homeomorphism to the challenge's
sphere. -/
def sHomeo : Work.StemsB.SphModel 3 ≃ₜ S3 := Work.Stems.onePointSphereHomeo 3

/-- The projection of the cover `E = hofib(g3)` to the sphere model (the transport of
`homotopyFibreFst g3 s3` along `sHomeo`). -/
def proj {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : C(Ecov g3, Work.StemsB.SphModel 3) :=
  Work.Rat.coverProj sHomeo g3 s3

/-- The fibre of the transported projection over `∞`; this is `Ω P₃` up to homeomorphism. -/
abbrev fib {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : Type :=
  ↥((proj g3) ⁻¹' ({OnePoint.infty} : Set (Work.StemsB.SphModel 3)))

/-- `proj` is a Hurewicz fibration (composite of a homeomorphism and the projection of the
homotopy fibre). -/
theorem isHurewiczFibration_proj {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    Work.StemsB.IsHurewiczFibration (proj g3) :=
  (Work.Rat.homeomorph_isHurewiczFibration sHomeo.symm).comp
    (Work.Stems.isHurewiczFibration_homotopyFibreFst g3 s3)

/-- The fibrewise triviality of `proj` over the outer disc. -/
theorem fibrewiseTrivial_proj_outer {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    Work.StemsB.FibrewiseTrivial (proj g3) (Work.StemsB.sphLoopOuter 3)
      (Work.StemsB.dOuter 3) := by
  refine Work.StemsB.fibrewiseTrivial_of_contraction (proj g3) (isHurewiczFibration_proj g3)
    (Work.StemsB.sphLoopOuter 3) (Work.StemsB.dOuter 3) (Work.StemsB.sphLoopOuterContr 3)
    (fun w => Work.StemsB.sphLoopOuterContr_zero 3 w) ?_ ?_
  · intro w
    exact Work.StemsB.sphLoopOuterContr_one 3 w
  · intro t
    exact Work.StemsB.sphLoopOuterContr_fixes 3 t

/-- The shell point of the inner cube, the base point of the second trivialisation. -/
def shellPt : ↥(Work.StemsB.sphLoopBig 3) :=
  ⟨Work.StemsB.sphShellPt 3, (Work.StemsB.serreSphere_sets 3 (by norm_num)).2.2.2.2⟩

/-- The fibrewise triviality of `proj` over the inner cube. -/
theorem fibrewiseTrivial_proj_big {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    Work.StemsB.FibrewiseTrivial (proj g3) (Work.StemsB.sphLoopBig 3) shellPt := by
  obtain ⟨c, hc0, hc1, hcb⟩ := Work.StemsB.serreSphere_contract_big 3 (by norm_num) shellPt.2
  exact Work.StemsB.fibrewiseTrivial_of_contraction (proj g3) (isHurewiczFibration_proj g3)
    (Work.StemsB.sphLoopBig 3) shellPt c hc0 hc1 hcb

/-- The fibre of `proj g3` over `∞` is nonempty (`S³` is path connected, so a path from the base
point to `sHomeo ∞` exists, and its image under `g3` gives a point of the fibre). -/
theorem nonempty_fib {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : Nonempty (fib g3) := by
  obtain ⟨γ⟩ := (Work.Serre.pathConnectedSpace_sph 3 (by norm_num)).joined s3
    (sHomeo OnePoint.infty)
  let δ : Path (g3 s3) (g3 (sHomeo OnePoint.infty)) := γ.map g3.continuous
  have hδsrc : (δ : C(unitInterval, P3)) 0 = g3 s3 := δ.source
  refine ⟨Subtype.mk (Subtype.mk (sHomeo OnePoint.infty,
    (⟨δ.1, hδsrc⟩ : Work.StemsB.PathSpace P3 (g3 s3))) ?_) ?_⟩
  · show (δ : C(unitInterval, P3)) 1 = g3 (sHomeo OnePoint.infty)
    exact δ.target
  · show sHomeo.symm (sHomeo OnePoint.infty) = OnePoint.infty
    exact sHomeo.symm_apply_apply _

/-- The base point of the fibre used by the `K(ℤ,2)`-structure statements. -/
def fibPt {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : fib g3 :=
  Classical.choice (nonempty_fib g3)

end

end Work.Pi6.EFACTS
