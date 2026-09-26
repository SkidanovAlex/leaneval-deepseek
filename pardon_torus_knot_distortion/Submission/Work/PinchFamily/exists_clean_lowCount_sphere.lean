import Mathlib
import Submission.Work.PinchFamily.Defs
import Submission.Work.PinchCounted.Pardon3
import Submission.Work.PinchCounted.Counting

namespace Work.PinchFamily

theorem exists_clean_lowCount_sphere (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot) (d : ℝ) (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    (r : ℝ) (hr : 0 < r) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hbox : Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ)
    (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s})
    (u : ℝ) (hu : |u| < Submission.eps * r)
    (hS : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hU : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    ∃ S : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ) S ∧
      Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ ∩ S) <
        Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
          (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
            (Work.CoreTopology.standardCurve p q)) := by
  -- The degenerate witness: the empty sphere is cleaned, and it meets the knot in no point.
  -- (This is the ∃S half of `NeckCollarBody`; it carries no geometry.)
  refine ⟨(∅ : Set LeanEval.KnotTheory.PardonDistortion.R3), Work.PinchCounted.cleansInSphere_empty (Work.Smooth.Morse.torus ψ), ?_⟩
  have hpid : Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) = (Nat.min p q : ℕ∞) :=
    Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph
  rw [Set.inter_empty, Set.encard_empty, hpid]
  exact_mod_cast (lt_min hp hq)

end Work.PinchFamily
