import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQASM.Defs
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.Stems.Engine.C2EvenRange
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.SQASM

noncomputable section

/-- **The fibre of the first projection of a base-changed path–loop fibration.**  For a space `X`,
a point `x₀`, a parameter space `D` and a map `s : C(D,X)`, the fibre of the projection
`bundlePullbackFst : bundlePullback X x₀ D s → D` over `d₀` is canonically homeomorphic to the
fibre of the path–loop fibration `evalOne X x₀` over `s d₀`: a point of the former is a pair
`((d₀, γ), h)` and `γ ↦ ((d₀,γ),h)` is inverse to `((u,γ),h) ↦ γ`. -/
def fibreBundlePullbackFstHomeo {X : Type} [TopologicalSpace X] {x₀ : X} {D : Type}
    [TopologicalSpace D] (s : C(D, X)) (d₀ : D) :
    Work.StemsB.fibre (Work.StemsB.bundlePullbackFst (x₀ := x₀) D s) d₀ ≃ₜ
      Work.StemsB.fibre (Work.StemsB.evalOne X x₀) (s d₀) where
  toFun p := ⟨p.1.1.2, by
    have h : Work.StemsB.evalOne X x₀ p.1.1.2 = s p.1.1.1 := p.1.2
    rw [show p.1.1.1 = d₀ from p.2] at h
    exact h⟩
  invFun γ := ⟨⟨(d₀, γ.1), γ.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext p.2.symm rfl))
  right_inv γ := Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ (fun γ => γ.2)) (fun γ => rfl)
    exact continuous_const.prodMk continuous_subtype_val

/-- The inverse of `Work.StemsB.fibreEvalOneHomeo`, explicitly. -/
theorem fibreEvalOneHomeo_symm_apply (X : Type) [TopologicalSpace X] (x₀ : X)
    (p : Path x₀ x₀) :
    (Work.StemsB.fibreEvalOneHomeo X x₀).symm p =
      (⟨⟨p.toContinuousMap, p.source'⟩, p.target'⟩ : Work.StemsB.fibre
        (Work.StemsB.evalOne X x₀) x₀) := rfl

/-- The inverse of `fibreBundlePullbackFstHomeo`, explicitly. -/
theorem fibreBundlePullbackFstHomeo_symm_apply {X : Type} [TopologicalSpace X] {x₀ : X}
    {D : Type} [TopologicalSpace D] (s : C(D, X)) (d₀ : D)
    (γ : Work.StemsB.fibre (Work.StemsB.evalOne X x₀) (s d₀)) :
    (fibreBundlePullbackFstHomeo (x₀ := x₀) s d₀).symm γ =
      (⟨⟨(d₀, γ.1), γ.2⟩, rfl⟩ : Work.StemsB.fibre
        (Work.StemsB.bundlePullbackFst (x₀ := x₀) D s) d₀) := rfl

/-- **The model homeomorphism.**  The loop space `Ω P₄ = Path (g₄ e₀) (g₄ e₀)` is homeomorphic to
the fibre `Kfib g₃ g₄` of `homotopyFibreFst g₄ : Y → E` over `e₀`; it is the composite of the
inverse of `fibreEvalOneHomeo` (the fibre of the path–loop fibration is the loop space) with the
inverse of `fibreBundlePullbackFstHomeo` (base change does not change the fibre). -/
def fibreModelHomeo {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    {P4 : Type} [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4)) :
    Path (g4 (Work.Pi6.e0 g3)) (g4 (Work.Pi6.e0 g3)) ≃ₜ Work.Pi6.SQASM.Kfib g3 g4 :=
  (Work.StemsB.fibreEvalOneHomeo P4 (g4 (Work.Pi6.e0 g3))).symm.trans
    (fibreBundlePullbackFstHomeo (x₀ := g4 (Work.Pi6.e0 g3)) g4 (Work.Pi6.e0 g3)).symm

/-- `fibreModelHomeo` sends the constant loop at the base point to the base point `kfibPt` of the
fibre. -/
theorem fibreModelHomeo_refl {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    {P4 : Type} [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4)) :
    fibreModelHomeo g3 g4 (Path.refl (g4 (Work.Pi6.e0 g3))) = Work.Pi6.SQASM.kfibPt g3 g4 := by
  simp only [fibreModelHomeo]
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- **The fibre `Kfib` of `homotopyFibreFst g₄ : Y → E` over `e₀` is a model of `K(ℤ/2,3)`
through degree 11.**  Here `Ecov g₃` and `Ycov g₃ g₄` are the homotopy fibres of the killing tower,
`Kfib g₃ g₄` is the fibre of `Work.RatHurewicz.homotopyFibreFst g₄ (e₀ g₃) : Y → E` over `e₀` with
base point `kfibPt g₃ g₄ = ⟨y₀, rfl⟩` (`Pi6/SQASM/Defs.lean`), and the hypothesis is that `P₄` is a
range model of `K(ℤ/2,4)` through degree 12.

Route: `homotopyFibreFst` is the base change of the path–loop fibration `evalOne P₄ (g₄ e₀)` along
`g₄`, so its fibre over `e₀` is homeomorphic to the fibre of `evalOne` over its own base point,
which is the loop space `Path (g₄ e₀) (g₄ e₀)` (`Work.StemsB.fibreEvalOneHomeo`,
`Work.RatHurewicz.homotopyFibre`); the loop space of a range model of `K(ℤ/2,4)` through 12 is a
range model of `K(ℤ/2,3)` through `11` (`Work.Stems.isEMSpaceUpTo_loop`), and `IsEMSpaceUpTo` is a
homeomorphism invariant (`Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph`). -/
theorem fibreModel {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    {P4 : Type} [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (hP4 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (Work.Pi6.e0 g3))) :
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) 11
      (Work.Pi6.SQASM.Kfib g3 g4) (Work.Pi6.SQASM.kfibPt g3 g4) := by
  have hloop := Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 4) (M := 12)
    (by norm_num) (g4 (Work.Pi6.e0 g3)) hP4
  have h := Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph (A := ZMod 2) (k := 3) (N := 11)
    (by norm_num) (fibreModelHomeo g3 g4) (Path.refl (g4 (Work.Pi6.e0 g3))) hloop
  rw [fibreModelHomeo_refl] at h
  exact h

end

end Work.Pi6.SQASM
