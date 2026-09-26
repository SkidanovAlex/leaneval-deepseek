import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.BoxBubble.mustbeinessentialBox
import Submission.Work.BoxShrink.counting

/-!
# The counting consequence of Pardon's inequality

Pardon's Lemma 4.2 (in the counted form of this development) says that the box sphere
`{y | boxNorm c σ y = s}` meets the knot in fewer than `I(F,β) = min p q` points, provided its
parameter count is below `10(1+ε)/ε · d`.  The present lemma records the *sharpened* statement
that the crux actually needs: it is not the sphere *at the box boundary* whose count has to be
controlled, but an arbitrary set `S` whose parameter count is bounded by Pardon's inequality

`|S ∩ β| ≤ |S₀ ∩ β| + 2 |D ∩ β|`

(the count at the two endpoint traces of the pinching family).  Together with the two endpoint
counts this gives `|S ∩ β| < I(F,β)`, because the constants are chosen exactly so that

`10(1+ε)/ε·d + 2·5(1+ε)/ε·d = countConst·d < min p q`

(`Work.BoxShrink.count_add_two_mul_lt`).

The mathematical content is the elementary counting step: the number of intersection *points* of
the knot with `S` is at most the number of intersection *parameters* in the fundamental period,
because the range of a `2π`-periodic curve is the image of `[0,2π)` (Pardon's own counting step,
`Work.BoxBubble.encard_range_inter_le_param`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

theorem count_of_pardonInequality
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hPardon : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S}) : ENNReal)
      ≤ (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
        + 2 * (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧
            (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
    (hcS : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hcP : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ S) <
      Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)) := by
  classical
  -- The knot, regarded as a closed curve of the surface `ψ(F_standard)`: its image lies on the
  -- surface because it is the image of the standard `(p,q)`-curve.
  let γK : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) :=
    { γ := K.curve
      cont := K.smooth.continuous
      periodic := K.periodic
      mem := fun t => by
        have ht : K.curve t ∈ Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph
            ψ.toHomeomorph (Work.CoreTopology.standardCurve p q)).γ := by
          rw [← himg]
          exact Set.mem_range_self t
        obtain ⟨v, hv⟩ := ht
        rw [← hv]
        exact (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).mem v }
  -- Pardon's counting step: the number of intersection *points* of the knot with `S` is at most
  -- the number of intersection *parameters* in the fundamental period.
  have hle : Set.encard (Set.range K.curve ∩ S) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S} :=
    Work.BoxBubble.encard_range_inter_le_param γK S
  -- Pardon's inequality, read with the two counts of the crux.
  have hA : (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S}) : ENNReal)
      ≤ (↑(Work.BoxShrink.sphCount K c σ s) : ENNReal)
        + 2 * (↑(Work.BoxShrink.planeCount K c σ s u) : ENNReal) := by
    simpa [Work.BoxShrink.sphCount, Work.BoxShrink.planeCount] using hPardon
  have hS' : (↑(Work.BoxShrink.sphCount K c σ s) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d) := by
    simpa [Work.BoxShrink.sphCount] using hcS
  have hP' : (↑(Work.BoxShrink.planeCount K c σ s u) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d) := by
    simpa [Work.BoxShrink.planeCount] using hcP
  -- The constant bookkeeping: `10(1+ε)/ε·d + 2·5(1+ε)/ε·d = countConst·d < min p q`.
  have hlt :=
    Work.BoxShrink.count_add_two_mul_lt (lt_min hp hq) (K := K) (c := c) (σ := σ) (s := s)
      (u := u) hd hsmall hS' hP'
  -- Hence `|S ∩ β| < I(F,β)`.
  have hAlt : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ S}
      < (Nat.min p q : ℕ∞) :=
    ENat.toENNReal_lt.mp (lt_of_le_of_lt hA hlt)
  -- Rewrite the surface curve as the knot's curve and `I(F,β)` as `min p q`.
  have hpI : Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) = (Nat.min p q : ℕ∞) :=
    Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph
  rw [← himg, hpI]
  exact lt_of_le_of_lt hle hAlt

end Work.PinchCounted
