import Mathlib
import Submission.Work.WilCrux.Defs
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilCrux.contDiffAt_finAppend_iff
import Submission.Work.WilCrux.contDiffAt_sheetPt_add_iff

namespace Work.WilCrux

/-- **N3a (the shear is a `C^1` change of coordinates).**  Where `φ` is `C^1`, the joint
function of the sheared family is `C^1` at `(v,u)` iff the joint function of `g` is `C^1` at the
corresponding sheet point.

Proof: `famFun_shearFam` writes `famFun (shearFam g e φ) = (famFun g) ∘ Φ` with
`Φ(v,u) = sheetPt e v (φ v + u)`; when `ContDiffAt ℝ 1 φ v`, `Φ` is a local `C^1`-diffeomorphism
at `(v,u)` (its inverse recovers `v` from the parameter/band coordinates and subtracts `φ v`),
and `ContDiffAt` is preserved by composition with a local `C^1`-diffeomorphism in both
directions. -/
theorem ShearDiff {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (hφ : ContDiffAt ℝ 1 φ v) :
    ContDiffAt ℝ 1 (Work.WilG4c.famFun (Work.WilCrux.shearFam g e φ)) (Fin.append v u) ↔
      ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Work.WilCrux.sheetPt e v (φ v + u)) := by
  have hkey : (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
        Work.WilG4c.famFun (Work.WilCrux.shearFam g e φ) (Fin.append p.1 p.2))
      = fun p => Work.WilG4c.famFun g (Work.WilCrux.sheetPt e p.1 (φ p.1 + p.2)) := by
    funext p
    exact Work.WilCrux.famFun_shearFam g e φ p.1 p.2
  rw [Work.WilCrux.contDiffAt_finAppend_iff, hkey,
    ← Work.WilCrux.contDiffAt_sheetPt_add_iff e φ (Work.WilG4c.famFun g) v u hφ]

end Work.WilCrux
