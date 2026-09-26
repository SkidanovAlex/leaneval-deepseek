import Mathlib
import Submission.Work.BoxShrink.Pinch.Defs

/-!
# Drive interfaces (written by the project lead, 2026-09-24): the WEAK-DISC route for field 1

`Work.CoreTopology.BoundsDiskInComplement` asks for an INJECTIVE disc.  Its consumer
(`CoreTopology/compressing_winding_dichotomy`) never uses injectivity, and without it the cut-and-paste
step of Pardon's Lemma 2 is elementary (induction on nesting: collar push + null-homotopy of an
inessential curve, glued on closed sets), with no Alexander theorem, isotopy extension or wild spheres.

* `IsBoundingDiskW`, `BoundsDiskInComplementW` — a continuous disc map with boundary `α` and open disc off `F`;
* `CleansDiscsW`, `CleansDiscsAllW` — the weak cut-and-paste inputs;
* `CountingHalfW` — `Work.BoxShrink.Pinch.CountingHalf` verbatim, except that its cut-and-paste hypothesis is
  the WEAK `CleansDiscsW`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Work.CoreTopology

/-- A continuous (not necessarily injective) disc bounded by `α` whose open disc misses `F`. -/
def IsBoundingDiskW (P : ParamTorus) (α : ClosedCurve P)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3)) : Prop :=
  (∀ θ : ℝ, e (circlePoint θ) = α.γ θ) ∧
    (∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → e z ∉ P.carrier)

def BoundsDiskInComplementW (P : ParamTorus) (α : ClosedCurve P) : Prop :=
  ∃ e : C(Metric.closedBall (0 : ℂ) 1, R3), IsBoundingDiskW P α e

def CleansDiscsW (P : ParamTorus) : Prop :=
  ∀ (S : Set R3) (D : Work.InnermostDisk.InnermostDisc P S), BoundsDiskInComplementW P D.α

def CleansDiscsAllW : Prop :=
  ∀ (ψ : Submission.Diffeo), CleansDiscsW
    (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)

theorem boundsDiskInComplementW_of_strong {P : ParamTorus} {α : ClosedCurve P}
    (h : BoundsDiskInComplement P α) : BoundsDiskInComplementW P α := by
  obtain ⟨e, -, h1, h2⟩ := h
  exact ⟨e, h1, h2⟩

theorem cleansDiscsW_of_strong {P : ParamTorus} (h : Work.InnermostDisk.CleansDiscs P) :
    CleansDiscsW P := fun S D => boundsDiskInComplementW_of_strong (h S D)

open Work.BoxShrink.Pinch in
/-- Pardon's Lemma 3 with his counting, consuming only the WEAK cut-and-paste input. -/
def CountingHalfW : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u

end Work.Drive
