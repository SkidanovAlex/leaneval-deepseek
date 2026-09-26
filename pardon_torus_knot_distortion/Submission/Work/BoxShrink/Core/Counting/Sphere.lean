import Submission.Work.BoxShrink.Core.Bubble.Defs
import Submission.Work.BoxShrink.Core.Counting.Basic
import Submission.Work.BoxBubble.mustbeinessentialBox

/-!
# The sphere count: the boundary of Pardon's box carries no essential loop

The sweep `Work.BoxSweep.sweep` produces a level `s` of the box norm at which the knot meets the
boundary sphere `∂PBox s c σ` in at most `10(1+ε)/ε · d` parameters.  By Pardon's Lemma 4.2
(`Work.BoxBubble.mustbeinessentialBox`, whose geometric input is the classical innermost-disc
datum `Work.InnermostDisk.CleansInSphere`) this is fewer than `I(F, β) = min p q` points, provided
`countConst * d < min p q`; hence the boundary sphere carries no essential loop of the torus.

This is the first of the two counting consequences consumed by Pardon's double bubble: it is what
makes the cut curves `F ∩ ∂PBox s c σ` inessential in `F`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Core

noncomputable section

/-- **The boundary sphere of the box contains no essential loop** (from the sweep's count at the
level `s` and the classical innermost-disc input at that sphere). -/
theorem not_containsEssentialLoop_sphereSet (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hclean : Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (sphereSet c σ s))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (sphereSet c σ s) := by
  have hn : Nat.min p q ≠ 0 := ne_of_gt (lt_min hp hq)
  have hlt := encard_lt_of_coe_le_ofReal (n := Nat.min p q) hn hcount
    (ten_coeff_mul_lt_min hp hq hd hsmall)
  exact Work.BoxBubble.mustbeinessentialBox p q hp hq hc ψ.toHomeomorph K himg hs c σ hclean hlt

/-- The same, with the classical innermost-disc input at the sphere *derived* from the general
position of the sphere (`Work.InnermostDisk.SphereSlicing`, whose nonemptiness is
`Work.BoxShrink.SlicedSphere`) and from Pardon's cut-and-paste step at the surface
(`Work.InnermostDisk.CleansDiscs`).  These are exactly the two hypotheses of
`Work.BoxShrink.CruxCore`, so the sphere count is available there without further input. -/
theorem not_containsEssentialLoop_sphereSet_of_slicing (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (sphereSet c σ s)))
    (hcl : Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (sphereSet c σ s) :=
  not_containsEssentialLoop_sphereSet p q hp hq hc ψ K hd himg hsmall hs c σ
    (cleansInSphere_of_slicedSphere_and_cleansDiscs (P :=
      Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) hslice hcl) hcount

end

end Work.BoxShrink.Core
