import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing

/-!
# The twisted Möbius upper picture (definitions for the upper-certificate assembly)

`mobiusTwisted D η S ε εp Dp` is the Möbius window drawing of `MobiusPacket` twisted by the two slab
twists `twistY S.a' (-1)`, `twistX ε (-1)` and pushed by `pushY Dp εp 1`.  The upper certificate
(`Work.Drive.N2Lead.mobiusUpperCertified`) is proved by transferring the certificate of this picture
back along the three ambient paths `ambientPath_twistY`, `ambientPath_twistX`, `ambientPath_pushY`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- **The twisted Möbius upper picture**: the drawing twisted by `twistY a' (-1)` and `twistX ε (-1)`
and pushed by `pushY Dp εp 1`. -/
def mobiusTwisted {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (η : ℝ)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (ε εp Dp : ℝ) : M → E3 :=
  fun y => pushY Dp εp 1 (twistX ε (-1) (twistY S.a' (-1) (mobiusWindowDrawing D η S y)))

end

end Work.Drive.N2Lead
