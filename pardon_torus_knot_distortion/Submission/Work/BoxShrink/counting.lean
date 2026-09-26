import Mathlib
import Submission.Work.BoxShrink.crux
import Submission.Work.BoxBubble.mustbeinessentialBox

/-!
# The counting step of the double-bubble core

The two counting hypotheses of `Work.BoxShrink.CruxStatement` (the number of *parameters* in the
fundamental period `[0, 2π)` at which the knot meets the box sphere `∂PBox s c σ`, respectively
the cutting plane `{y (σ 2) = c (σ 2) + u} ∩ PBox s c σ`) bound the number of *intersection
points* of the knot with those level sets, and the constants are chosen exactly so that

`10(1+ε)/ε·d + 2·5(1+ε)/ε·d = countConst·d < min p q = I(F,β)`.

This file performs that arithmetic, and records Pardon's Lemma 4.2 at the box sphere in the form
in which the crux consumes it: the box boundary meets the knot in fewer than `I(F,β) = min p q`
points, hence contains no essential loop of the surface.

Read `Submission/Work/BoxShrink/crux.lean` for the statement of the crux; this file only supplies
the constant bookkeeping and the reduction of the sphere hypothesis.
-/

namespace Work.BoxShrink

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- The number of *parameters* in the fundamental period `[0, 2π)` at which the knot meets the
boundary sphere `{boxNorm c σ · = s}` of Pardon's box, as an `ℕ∞`. -/
def sphCount (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : ℕ∞ :=
  Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Submission.boxNorm c σ (K.curve t) = s}

/-- The number of *parameters* in the fundamental period at which the knot meets the cutting
plane `{y (σ 2) = c (σ 2) + u}` inside the box `PBox s c σ`, as an `ℕ∞`. -/
def planeCount (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ) : ℕ∞ :=
  Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
    (K.curve t) (σ 2) = c (σ 2) + u}

/-- The sphere count, as a real number, is `10(1+ε)/ε = 75` times the distortion bound. -/
theorem ten_const : 10 * (1 + Submission.eps) / Submission.eps = 75 := by
  norm_num [Submission.eps]

/-- The plane count, as a real number, is `5(1+ε)/ε = 37.5` times the distortion bound. -/
theorem five_const : 5 * (1 + Submission.eps) / Submission.eps = 37.5 := by
  norm_num [Submission.eps]

theorem countConst_eq : Submission.countConst = 150 := rfl

variable {p q : ℕ}

/-- **The sphere count is below `min p q`.** -/
theorem sphCount_lt (hpq : 0 < Nat.min p q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s : ℝ}
    (h : (sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) :
    sphCount K c σ s < (Nat.min p q : ℕ∞) := by
  have h2 : (75 : ℝ) * d < (Nat.min p q : ℝ) := by
    have hle : (75 : ℝ) * d ≤ 150 * d := by nlinarith
    rw [countConst_eq] at hsmall
    linarith
  have h3 : ENNReal.ofReal (75 * d) < ((Nat.min p q : ℕ∞) : ENNReal) := by
    rw [ENat.toENNReal_coe, ENNReal.ofReal_lt_natCast (Nat.pos_iff_ne_zero.mp hpq)]
    exact h2
  have h4 : (sphCount K c σ s : ENNReal) < ((Nat.min p q : ℕ∞) : ENNReal) :=
    lt_of_le_of_lt (by simpa [ten_const] using h) h3
  exact (ENat.toENNReal_lt).mp h4

/-- **The plane count is below `min p q`.** -/
theorem planeCount_lt (hpq : 0 < Nat.min p q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s u : ℝ}
    (h : (planeCount K c σ s u : ENNReal) ≤
      ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    planeCount K c σ s u < (Nat.min p q : ℕ∞) := by
  have h2 : (37.5 : ℝ) * d < (Nat.min p q : ℝ) := by
    have hle : (37.5 : ℝ) * d ≤ 150 * d := by nlinarith
    rw [countConst_eq] at hsmall
    linarith
  have h3 : ENNReal.ofReal (37.5 * d) < ((Nat.min p q : ℕ∞) : ENNReal) := by
    rw [ENat.toENNReal_coe, ENNReal.ofReal_lt_natCast (Nat.pos_iff_ne_zero.mp hpq)]
    exact h2
  have h4 : (planeCount K c σ s u : ENNReal) < ((Nat.min p q : ℕ∞) : ENNReal) :=
    lt_of_le_of_lt (by simpa [five_const] using h) h3
  exact (ENat.toENNReal_lt).mp h4

/-- **The double-bubble count.**  The sphere count plus twice the plane count is below
`min p q = I(F,β)`, which is the count hypothesis Pardon's Lemma 3 needs (the intermediate
spheres of the `2`-surgery family meet the knot in at most this many points). -/
theorem count_add_two_mul_lt (hpq : 0 < Nat.min p q) {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s u : ℝ}
    (hS : (sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hD : (planeCount K c σ s u : ENNReal) ≤
      ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    (sphCount K c σ s : ENNReal) + 2 * (planeCount K c σ s u : ENNReal) <
      (Nat.min p q : ℕ∞) := by
  have h2 : (150 : ℝ) * d < (Nat.min p q : ℝ) := by
    rw [countConst_eq] at hsmall; exact hsmall
  have hsum : (sphCount K c σ s : ENNReal) + 2 * (planeCount K c σ s u : ENNReal)
      ≤ ENNReal.ofReal (75 * d) + 2 * ENNReal.ofReal (37.5 * d) := by
    refine add_le_add ?_ ?_
    · simpa [ten_const] using hS
    · exact mul_le_mul_of_nonneg_left (by simpa [five_const] using hD)
        (by norm_num : (0 : ℝ≥0∞) ≤ 2)
  have hof : ENNReal.ofReal (75 * d) + 2 * ENNReal.ofReal (37.5 * d) =
      ENNReal.ofReal (150 * d) := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
      rw [ENNReal.ofReal_ofNat]
    rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have h3 : ENNReal.ofReal (150 * d) < ((Nat.min p q : ℕ∞) : ENNReal) := by
    rw [ENat.toENNReal_coe, ENNReal.ofReal_lt_natCast (Nat.pos_iff_ne_zero.mp hpq)]
    exact h2
  exact lt_of_le_of_lt (hof ▸ hsum) h3

variable {p q : ℕ}

/-- **Pardon's Lemma 4.2 at the box sphere, in the form the crux consumes.**  If the box
boundary `{boxNorm c σ · = s}` meets the knot in fewer than `min p q` parameters (so, in fewer
points), and the classical innermost-disc input holds for it, then it contains no essential loop
of the surface `ψ(F_standard)`. -/
theorem not_containsEssentialLoop_of_counts (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hclean : Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcount : (sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) :
    ¬ (∃ γ : Work.CoreTopology.ClosedCurve
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph),
        Work.CoreTopology.IsEssential _ γ ∧
          ∀ t : ℝ, γ t ∈ {y : R3 | Submission.boxNorm c σ y = s}) :=
  Work.BoxBubble.mustbeinessentialBox p q hp hq hc ψ.toHomeomorph K himg hs c σ hclean
    (sphCount_lt (lt_min hp hq) hd hsmall hcount)

/-- **Pardon's Lemma 4.2 at the box sphere, with the classical inputs in the form the crux
provides them**: general position of the sphere (`SlicedSphere`) and the cut-and-paste step
(`Work.InnermostDisk.CleansDiscs`). -/
theorem not_containsEssentialLoop_of_sliced (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hclean : Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hslice : SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcount : (sphCount K c σ s : ENNReal) ≤
      ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) :
    ¬ (∃ γ : Work.CoreTopology.ClosedCurve
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph),
        Work.CoreTopology.IsEssential _ γ ∧
          ∀ t : ℝ, γ t ∈ {y : R3 | Submission.boxNorm c σ y = s}) :=
  not_containsEssentialLoop_of_counts hp hq hc ψ K hs c σ hd hsmall himg
    (Work.InnermostDisk.cleansInSphere_of_inputs
      (Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hslice.some) hclean)
    hcount

end

end Work.BoxShrink
