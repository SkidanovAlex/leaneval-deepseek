import Mathlib
import Submission.Work.Box.Shrink
import Submission.Work.CoreTopology.All
import Submission.Work.InnermostDisk.All

/-!
# Pardon's `mustbeinessential` for the boundary sphere of a box

This is the topological crux of Pardon's shrinking step, in the form in which the
box-shrinking argument consumes it.

Let `ψ` be a homeomorphism of `ℝ³`, let `F = ψ(F_standard)` be the image of the standard torus
and let `β` be the image of the standard `(p,q)`-curve, so that `I(F,β) = min p q`
(`Work.CoreTopology.pardonsI_standard_mapHomeomorph`).  Let `K` be a knot whose image is the
image of `β` (`himg`), and let `S = ∂PBox s c σ = {y | boxNorm c σ y = s}` be the boundary
sphere of Pardon's box.  If `S` meets the curve `K` in fewer than `min p q` points (`hcount`,
with the parameters counted in the fundamental period `[0, 2π)`), then `S` contains no essential
loop of the torus.

The two ingredients of Pardon's Lemma 4.2 are:

* the counting step, proved here from scratch: the number of intersection *points* of `K` with
  `S` is at most the number of intersection *parameters* in `[0, 2π)`, because the range of a
  `2π`-periodic curve is the image of the fundamental period
  (`Work.CoreTopology.ClosedCurve.range_eq_image`), and the image of a set has no larger
  cardinality than the set itself;
* the reduction `Work.InnermostDisk.mustbeinessential_of_cleansInSphere`, which turns the
  geometric content of the innermost-disc argument (the hypothesis `hclean`) plus the count
  `< I(F,β)` into the vanishing of the winding vector.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxBubble

/-- **The counting step.**  For a closed curve `γ` of a parametrised torus, the number of
intersection *points* of `γ` with a set `T ⊆ ℝ³` is at most the number of intersection
*parameters* in the fundamental period `[0, 2π)`.

Indeed, the range of a `2π`-periodic curve is the image of `[0, 2π)`
(`Work.CoreTopology.ClosedCurve.range_eq_image`), so `range γ ∩ T` is the image under `γ` of
the parameter set `[0, 2π) ∩ γ ⁻¹' T`; an image never has larger cardinality than its
source (`Set.encard_image_le`).  No injectivity of `γ` is needed, since the estimate goes in
the direction that collapsing can only help. -/
theorem encard_range_inter_le_param {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P) (T : Set R3) :
    Set.encard (Set.range γ.γ ∩ T) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧ γ.γ t ∈ T} := by
  have hS : Set.range γ.γ ∩ T =
      γ.γ '' (Set.Ico (0 : ℝ) (2 * Real.pi) ∩ γ.γ ⁻¹' T) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P γ]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hyT⟩
      exact ⟨t, ⟨ht, hyT⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hyT⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hyT⟩
  rw [hS]
  exact Set.encard_image_le γ.γ (Set.Ico (0 : ℝ) (2 * Real.pi) ∩ γ.γ ⁻¹' T)

theorem mustbeinessentialBox (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ
        (Work.CoreTopology.standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    (hclean : Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
      {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s})
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (∃ γ : Work.CoreTopology.ClosedCurve
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ),
        Work.CoreTopology.IsEssential _ γ ∧
          ∀ t : ℝ, γ t ∈ {y : LeanEval.KnotTheory.PardonDistortion.R3 |
            Submission.boxNorm c σ y = s}) := by
  classical
  -- The curve of the knot, regarded as a closed curve of the image torus: its image lies on the
  -- torus because it is the image of the image of the standard `(p,q)`-curve.
  let γK : Work.CoreTopology.ClosedCurve (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) :=
    { γ := K.curve
      cont := K.smooth.continuous
      periodic := K.periodic
      mem := fun t => by
        have ht : K.curve t ∈ Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ
            (Work.CoreTopology.standardCurve p q)).γ := by
          rw [← himg]
          exact Set.mem_range_self t
        obtain ⟨u, hu⟩ := ht
        rw [← hu]
        exact (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ
          (Work.CoreTopology.standardCurve p q)).mem u }
  -- The counting step: the number of intersection points of `K` with the box boundary is at most
  -- the number of intersection parameters in the fundamental period.
  have hle : Set.encard (Set.range K.curve ∩
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} :=
    encard_range_inter_le_param γK _
  -- Hence the box boundary meets `K` in fewer than `min p q` points.
  have hlt : Set.encard (Set.range K.curve ∩
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}) <
      (Nat.min p q : ℕ∞) :=
    lt_of_le_of_lt hle hcount
  -- In the vocabulary of Pardon's lemma: the box boundary meets `β` in fewer than `I(F,β)` points.
  have hSβ : Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ
          (Work.CoreTopology.standardCurve p q)).γ ∩
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}) <
      Work.CoreTopology.pardonsI (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ (Work.CoreTopology.standardCurve p q)) := by
    rw [Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ, ← himg]
    exact hlt
  -- Pardon's Lemma 4.2 (reduction to the innermost-disc input) finishes the job.
  rintro ⟨γ, hess, hmem⟩
  exact (Work.InnermostDisk.mustbeinessential_of_cleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ (Work.CoreTopology.standardCurve p q))
      {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}
      hclean hSβ) γ hmem hess

end Work.BoxBubble
