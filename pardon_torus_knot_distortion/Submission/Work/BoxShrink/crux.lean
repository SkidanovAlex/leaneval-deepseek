import Mathlib
import Submission.Work.Box.Shrink
import Submission.Work.BoxShrink.halving
import Submission.Work.BoxSweep.sweep
import Submission.Work.InnermostDisk.All

/-!
# Pardon's shrinking step: the double-bubble core

This file isolates the *whole* remaining content of Pardon's shrinking step in the smooth setting
of the challenge (`ψ : Submission.Diffeo`, so that the surface `ψ(F_standard)` is a smoothly
embedded torus), and splits it into two sharply stated pieces:

* `CruxCore` — **the double-bubble core**: given the general position of the swept sphere, one of
  the two halves of the box cut by the cutting plane contains an essential loop of the surface;
* `SweepNice` — **the sweep upgraded to general position**: there is a level `s ∈ (r, (1+ε)r)` of
  the box norm and a level `u ∈ (-εr, εr)` of the cutting plane at which the two intersection
  counts hold *and* the sphere `{boxNorm c σ · = s}` meets the surface in the general position
  required by the core.

Their conjunction is `CruxStatement`; `boxShrink_of_crux` assembles it into
`Submission.BoxShrinkStatement`, and everything else of Pardon's geometric argument is proved:

* `Submission.Work.BoxSweep.sweep` (sibling module) produces a level `s ∈ (r, (1+ε)r)` of the box
  norm and a level `u ∈ (-εr, εr)` of the cutting plane with the two intersection counts
  `≤ 10(1+ε)/ε·d` and `≤ 5(1+ε)/ε·d`;
* `Submission.Work.BoxShrink.halving` and `hasEssBox_of_upperHalf` / `hasEssBox_of_lowerHalf`
  (below) turn an essential loop in one of the two halves of `PBox s c σ` into a box of size
  `b·s + |u|/2 < shrinkFactor·r`, since `shrinkFactor = b(1+ε) + ε/2`;
* `Submission.Work.BoxShrink.counting` performs the constant bookkeeping
  (`10(1+ε)/ε·d + 2·5(1+ε)/ε·d = countConst·d < min p q = I(F,β)`) and records Pardon's Lemma 4.2
  at the box sphere, conditional on the classical innermost-disc input.

## Why the general-position hypothesis

For a *smooth* surface `F` and the `C^{0,1}` function `boxNorm`, the level set
`{boxNorm c σ · = s} ∩ F` is a compact 1-manifold (hence a finite disjoint union of simple closed
curves) only for *almost every* `s` (Sard for the piecewise smooth function, see the sibling
subproject `Submission/Work/Smooth/Morse`).  `InnermostDiscInput`/`CleansInSphere` for the sphere
`{boxNorm c σ · = s}` need that general position: the innermost-intersection argument of Pardon's
Lemma 4.2 selects an innermost *component* of `S ∩ F`.  The general position is recorded as
`SlicedSphere` (`Nonempty (Work.InnermostDisk.SphereSlicing P S)`) — a finite family of pairwise
disjoint simple closed curves of `F` in `S`, each bounding a disc in `S`, nested by a rank, and
covering every loop of `F` inside `S` (`Work.InnermostDisk.SphereSlicing`) — and `SweepNice` is
the statement that the sweep can be performed at such an `s`.  The classical cut-and-paste step
enters as `Work.InnermostDisk.CleansDiscs P` (a global hypothesis, Pardon's second innermost
argument).
-/

namespace Work.BoxShrink

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **General position of a sphere with respect to the surface**: the surface meets it in
finitely many pairwise disjoint simple closed curves, each bounding a disc inside the sphere,
nested, and covering every loop of the surface inside the sphere (Pardon's "put the sphere in
general position"). -/
def SlicedSphere (P : Work.CoreTopology.ParamTorus) (S : Set R3) : Prop :=
  Nonempty (Work.InnermostDisk.SphereSlicing P S)

/-- **The halving step, upper half.**  If the upper half
`{y ∈ PBox s c σ | y (σ 2) < c (σ 2) + u}` of the box `PBox s c σ` (with `r < s < (1+ε)r` and
`|u| < εr`) contains an essential loop of the surface, then some box of size `shrinkFactor * r`
does. -/
theorem hasEssBox_of_upperHalf {r s u : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) :
    Submission.HasEssBox P (Submission.shrinkFactor * r)
      (c + shiftVσ σ ((u - Submission.boxSide 2 * s) / 2)) (Submission.cycPerm.trans σ) := by
  obtain ⟨γ, hess, hmem⟩ := h
  -- the half-box size is below `shrinkFactor * r`
  have hbs : Submission.b * s + |u| / 2 ≤ Submission.shrinkFactor * r := by
    have hb : 0 < Submission.b := Submission.b_pos
    have h1 : Submission.b * s < Submission.b * ((1 + Submission.eps) * r) := by nlinarith
    have h2 : |u| / 2 < Submission.eps * r / 2 := by linarith
    have h3 : Submission.b * ((1 + Submission.eps) * r) + Submission.eps * r / 2 =
        Submission.shrinkFactor * r := by
      rw [Submission.shrinkFactor, Submission.eps, Submission.b]; ring
    linarith
  have hspos : 0 < s := lt_trans hr hrs
  have hu2 : |u| < Submission.boxSide 2 * s := by
    have hle : Submission.eps ≤ Submission.boxSide 2 := by
      rw [Submission.boxSide_two, Submission.eps]
      linarith [Submission.one_le_rpow_two_thirds]
    nlinarith [abs_nonneg u, hle, Submission.eps_pos]
  refine ⟨γ, hess, fun t => ?_⟩
  have hmem_sub := halfBox_upper_subset_perm s u hspos hu2 c σ ⟨(hmem t).1, (hmem t).2⟩
  exact Submission.PBox_mono hbs hmem_sub

/-- **The halving step, lower half.** -/
theorem hasEssBox_of_lowerHalf {r s u : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2)) :
    Submission.HasEssBox P (Submission.shrinkFactor * r)
      (c + shiftVσ σ ((u + Submission.boxSide 2 * s) / 2)) (Submission.cycPerm.trans σ) := by
  obtain ⟨γ, hess, hmem⟩ := h
  have hbs : Submission.b * s + |u| / 2 ≤ Submission.shrinkFactor * r := by
    have hb : 0 < Submission.b := Submission.b_pos
    have h1 : Submission.b * s < Submission.b * ((1 + Submission.eps) * r) := by nlinarith
    have h2 : |u| / 2 < Submission.eps * r / 2 := by linarith
    have h3 : Submission.b * ((1 + Submission.eps) * r) + Submission.eps * r / 2 =
        Submission.shrinkFactor * r := by
      rw [Submission.shrinkFactor, Submission.eps, Submission.b]; ring
    linarith
  have hspos : 0 < s := lt_trans hr hrs
  have hu2 : |u| < Submission.boxSide 2 * s := by
    have hle : Submission.eps ≤ Submission.boxSide 2 := by
      rw [Submission.boxSide_two, Submission.eps]
      linarith [Submission.one_le_rpow_two_thirds]
    nlinarith [abs_nonneg u, hle, Submission.eps_pos]
  refine ⟨γ, hess, fun t => ?_⟩
  have hmem_sub := halfBox_lower_subset_perm s u hspos hu2 c σ ⟨(hmem t).1, (hmem t).2⟩
  exact Submission.PBox_mono hbs hmem_sub

/-- **The classical cut-and-paste step of Pardon's second innermost argument**, for the
surfaces of the challenge: every innermost disc (of any sphere, for any diffeomorphism `ψ`) can be
cleaned so that its boundary bounds a disc in the complement of the surface.  This is
`Work.InnermostDisk.CleansDiscs` for the torus `ψ(F_standard)`. -/
def CleansDiscsAll : Prop :=
  ∀ (ψ : Submission.Diffeo), Work.InnermostDisk.CleansDiscs
    (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)

/-- **The double-bubble core.**  With the general position of the swept sphere available and the
classical cut-and-paste step (`Work.InnermostDisk.CleansDiscs`), one of the two halves of
`PBox s c σ` cut by the plane `{y (σ 2) = c (σ 2) + u}` contains an essential loop of the
surface, given that `PBox r c σ` does (`r < s`) and that the two intersection counts with the
knot are as in the sweep.

This is Pardon's Lemma 3 (`doublebubble`) for the double bubble
`(∂PBox s c σ, {y (σ 2) = c (σ 2)+u} ∩ PBox s c σ)`. -/
def CruxCore (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    (Work.InnermostDisk.CleansDiscs
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)) →
    ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          (∃ γ : Work.CoreTopology.ClosedCurve
              (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph),
            Work.CoreTopology.IsEssential _ γ ∧
              ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) ∨
          (∃ γ : Work.CoreTopology.ClosedCurve
              (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph),
            Work.CoreTopology.IsEssential _ γ ∧
              ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2))

/-- **The sweep, upgraded to general position.**  There is a level `s ∈ (r, (1+ε)r)` of the box
norm at which the surface meets the sphere `{boxNorm c σ · = s}` in general position
(`SlicedSphere`) and the intersection count with the knot is `≤ 10(1+ε)/ε·d`, and a level
`u ∈ (-εr, εr)` of the cutting plane with the second count `≤ 5(1+ε)/ε·d`.

This is `Work.BoxSweep.sweep` combined with the almost-everywhere general position of the level
sets of `boxNorm` on the surface: the sweep produces a *positive-measure* set of admissible
levels, and the general position holds almost everywhere. -/
def SweepNice (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∃ s ∈ Set.Ioo r ((1 + Submission.eps) * r),
        SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
            {y : R3 | Submission.boxNorm c σ y = s} ∧
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) ∧
        ∃ u ∈ Set.Ioo (-(Submission.eps * r)) (Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))

/-- **Almost every level of the box norm gives a sphere in general position.**  For a smooth
surface and the `C^{0,1}` function `boxNorm`, the level set `{boxNorm c σ · = s} ∩ F` is a compact
1-manifold — a finite disjoint union of simple closed curves, each bounding a disc inside the
sphere `{boxNorm c σ · = s}` — for almost every `s` (Sard on the finitely many smooth pieces of
`boxNorm`, together with the fact that its non-smooth locus is 1-dimensional). -/
def AeSliced (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ s ∂MeasureTheory.volume,
    SlicedSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      {y : R3 | Submission.boxNorm c σ y = s}

/-- The almost-everywhere general position of the box-norm level sets, for every diffeomorphism
of the challenge. -/
def AeSlicedAll : Prop :=
  ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)), AeSliced ψ c σ

/-- **The single remaining input of the whole proof**: the classical cut-and-paste step, the
double-bubble core, and the almost-everywhere general position of the box-norm level sets.  The
three are independent, and each is a precisely stated geometric statement:

* `CleansDiscsAll` — Pardon's second innermost argument (the cut-and-paste) for the surfaces of
  the challenge;
* `CruxCore p q` — Pardon's Lemma 3 (the double bubble);
* `AeSlicedAll` — Sard for the box norm on the smooth surface.

`SweepNice` (the sweep performed at a level in general position) is *derived* from `AeSlicedAll`
in `Submission/Work/BoxShrink/sweepNice_of_ae.lean`, and the assembly
`Work.BoxShrink.boxShrink_of_crux` is in `Submission/Work/BoxShrink/assemble.lean`. -/
def CruxStatement (p q : ℕ) : Prop :=
  CleansDiscsAll ∧ CruxCore p q ∧ AeSlicedAll

end

end Work.BoxShrink
