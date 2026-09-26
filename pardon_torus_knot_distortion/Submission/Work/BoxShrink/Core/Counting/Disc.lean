import Submission.Work.BoxShrink.Core.Counting.Basic
import Submission.Work.InnermostDisk.Reduction
import Submission.Work.CoreTopology.pardonsI_mapHomeomorph
import Submission.Work.Topology.SphereSlicing.Assembly

/-!
# The plane count: the slicing disc carries no essential loop

The sweep produces, for the same level `s`, a level `u` of the cutting plane at which the knot meets
the flat disc `cutDisc s c σ u = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` in at most `5(1+ε)/ε · d`
parameters.  By Pardon's Lemma 4.2 applied to that *disc* — the planar innermost-disc argument, whose
geometric input is `Work.InnermostDisk.CleansInSphere` at the disc — this is fewer than
`I(F, β) = min p q` points, so no loop of `F` inside the disc is essential.

This is the second counting consequence consumed by Pardon's double bubble.  Pardon needs it
because the plane slice *can* carry essential loops (a plane through the origin meets the standard
torus in a longitude), and only the count rules them out.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Core

noncomputable section

/-- **The slicing disc contains no essential loop of the torus** (from the sweep's count at the
plane level `u` and the classical innermost-disc input at that disc). -/
theorem not_containsEssentialLoop_sliceRegion (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (_hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hclean : Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (cutDisc s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (sliceRegion (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) s c σ u) := by
  have hn : Nat.min p q ≠ 0 := ne_of_gt (lt_min hp hq)
  have hlt := encard_lt_of_coe_le_ofReal (n := Nat.min p q) hn hcount
    (five_coeff_mul_lt_min hp hq hd hsmall)
  set P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph with hP
  have hβ : Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ cutDisc s c σ u) <
      Work.CoreTopology.pardonsI P (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) := by
    rw [Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph]
    refine lt_of_le_of_lt ?_ hlt
    calc Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
            (Work.CoreTopology.standardCurve p q)).γ ∩ cutDisc s c σ u)
        = Set.encard (Set.range K.curve ∩ cutDisc s c σ u) := by rw [← himg]
      _ ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ cutDisc s c σ u} :=
          Work.Topology.SphereSlicing.encard_range_inter_le_encard_param_of_periodic
            K.periodic (cutDisc s c σ u)
      _ ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u} := by
          apply Set.encard_mono
          rintro t ⟨ht, hmem⟩
          exact ⟨ht, hmem.1, mem_cutPlane.mp hmem.2⟩
  have hno := Work.InnermostDisk.mustbeinessential_of_cleansInSphere P
    (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
      (Work.CoreTopology.standardCurve p q)) (cutDisc s c σ u) hclean hβ
  rintro ⟨γ, he, hm⟩
  exact hno γ (fun t => ⟨(hm t).1.2, mem_cutPlane.mp (hm t).2⟩) he

end

end Work.BoxShrink.Core
