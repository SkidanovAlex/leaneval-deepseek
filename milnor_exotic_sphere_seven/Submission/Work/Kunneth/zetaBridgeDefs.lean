import Mathlib
import Submission.Work.LerayHirsch.Chapter
import Submission.Work.Kunneth.continuous_projClass_trivCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The "class of the fibre coordinate" for the trivial bundle, and the tautological pullback

Let `Z_B = trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit` and
`Z_pt = Work.LerayHirsch.trivCore m` (the same bundle over the one-point base).  This module builds
the continuous map

`Work.Kunneth.qTriv m B : C(P(ε^m over B), P(ε^m over pt))`

sending the class of a punctured vector to the class of its *fibre coordinate*, together with its
defining equation on representatives (`qTriv_mkProj`).

It is the geometric input of the bridge `qTriv^*(ζ(ε^m over pt)) = ζ(ε^m over B)`
(`Work.Kunneth.zeta_qTriv`, whose proof needs the bundle isomorphism
`tautLine Z_B ≅ bundleComap (tautLine Z_pt) (qTriv m B)` and
`Work.LerayHirsch.zeta_comap`), which is what lets the Künneth decomposition of
`H^*(B × P(ε^m over pt))` be read as the Leray–Hirsch decomposition of `H^*(P(ε^m over B))` along
the (homeomorphic) `(projMap Z_B, qTriv m B) : P(ε^m over B) → B × P(ε^m over pt)`.
-/

namespace Work.Kunneth

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ}

/-- **The class of the fibre coordinate is continuous** on the whole projectivisation of the
trivial bundle (the workspace only has the fibre restriction,
`Work.LerayHirsch.continuous_projClass_subtype`; the point-base case is
`Work.LerayHirsch.continuous_projClass_trivCore`). -/
theorem continuous_projClass_trivial (m : ℕ) (B : Type) [TopologicalSpace B] :
    Continuous (Work.LerayHirsch.projClass
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)) :=
  Work.Kunneth.continuous_projClass_trivCore m B

/-- **The class of the fibre coordinate**, from the trivial bundle over `B` to the trivial bundle
over the point: the composite `projUniv ∘ projClass`. -/
noncomputable def qTriv (m : ℕ) (B : Type) [TopologicalSpace B] :
    C(Work.LerayHirsch.ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit),
      Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore m)) :=
  (Work.LerayHirsch.projUniv m).comp
    ⟨Work.LerayHirsch.projClass
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit),
      continuous_projClass_trivial m B⟩

/-- **The defining equation of `qTriv`**: the class of a punctured vector `(b, v)` is sent to the
class of the punctured vector `(unit, v)` of the trivial bundle over the point. -/
theorem qTriv_mkProj (m : ℕ) (B : Type) [TopologicalSpace B]
    (p : ↥(Work.Thom.zeroComplement
      (Work.Thom.realification
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)))) :
    qTriv m B (Work.LerayHirsch.mkProj
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) p)
      = Work.LerayHirsch.mkProj (Work.LerayHirsch.trivCore m)
          ⟨(⟨PUnit.unit, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ :
              (Work.Thom.realification (Work.LerayHirsch.trivCore m)).TotalSpace),
            by rw [Work.Thom.mem_zeroComplement]; exact (Work.Thom.mem_zeroComplement p.1).mp p.2⟩ := by
  show (Work.LerayHirsch.projUniv m) ((Work.LerayHirsch.projClass
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit))
          (Work.LerayHirsch.mkProj _ p)) = _
  rw [Work.LerayHirsch.projClass_mkProj]
  exact Work.LerayHirsch.projUniv_mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
    (Work.Thom.mem_zeroComplement p.1).mp p.2⟩

end

end Work.Kunneth
