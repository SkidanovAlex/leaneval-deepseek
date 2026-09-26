import Mathlib
import Submission.Work.EpsW.pardonLemma2Local
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.CoreTopology.min_le_encard_inter_of_boundsDiskW
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.Drive.InterfacesD
import Submission.Work.BoxShrink.Core.All
import Submission.Work.BoxShrink.crux
import Submission.Work.Smooth.Morse.Defs

/-!
# Pardon's Lemma 2 in the *corrected* weak-disc vocabulary (`CleansDiscsWd`)

The bricks of `Submission/Work/EpsW/pardonLemma2Local.lean` (the local copies of Pardon's Lemma 2 at
the box sphere, at an arbitrary sliced sphere and at any sphere inside the footprint) carry the
*legacy* cut-and-paste hypothesis `Work.Drive.CleansDiscsW`, which is FALSE for general
configurations (the lens/crescent example; `Submission/Work/Drive/InterfacesD.lean`).  The crux's
current hypothesis list carries only the corrected `Work.Drive.CleansDiscsWd`, which demands the weak
cut-and-paste only for innermost discs whose interior curves are *disjoint* from the boundary curve
`α`.

In Pardon's setting the corrected hypothesis is all that is needed, and the missing disjointness is
supplied by the slicing itself: the components of `S ∩ F` are pairwise disjoint, so the curves of an
innermost disc taken from a slicing of `S` are disjoint from its boundary curve `α`.  This module
proves that, and re-runs the whole chain with `CleansDiscsWd`:

* `exists_innermostDisc_disjoint_of_slicing` — from a `SphereSlicing` of `S` containing an essential
  loop, an `InnermostDisc` whose curves are moreover disjoint from `α`;
* `trace_inessential_of_slicing_of_countsWd` — Pardon's Lemma 2 at an arbitrary sliced sphere in the
  corrected vocabulary;
* `sphereTrace_inessential_of_countsWd` — at the box sphere `∂PBox s c σ`;
* `trace_inessential_of_slicing_of_subset_footprintWd` — at any sliced sphere inside the footprint
  `sphereSet ∪ cutDisc` (both half-spheres of Pardon's double bubble are such).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.EpsW

noncomputable section

/-- **The innermost disc of a slicing, with its curves disjoint from the boundary curve.**  The
components of `S ∩ F` given by a `SphereSlicing` are pairwise disjoint, and the boundary curve `α`
of the innermost disc of minimal rank is one of them; the curves of that disc are the *other*
components with a point inside the disc of `α`, so they are disjoint from `α`. -/
theorem exists_innermostDisc_disjoint_of_slicing {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (h : Work.InnermostDisk.SphereSlicing P S)
    (hcon : ∃ γ : Work.CoreTopology.ClosedCurve P,
      Work.CoreTopology.IsEssential P γ ∧ ∀ t : ℝ, γ t ∈ S) :
    ∃ D : Work.InnermostDisk.InnermostDisc P S,
      ∀ i : D.ι, Disjoint (Set.range (D.curves i).γ) (Set.range D.α.γ) := by
  classical
  obtain ⟨i, hess, hmin⟩ := h.exists_min_essential hcon
  refine ⟨h.innermostDiscOfMinRank i hess hmin, ?_⟩
  intro j
  simp only [Work.InnermostDisk.SphereSlicing.innermostDiscOfMinRank]
  refine h.disjoint (fun hji => ?_)
  obtain ⟨z : Work.InnermostDisk.Disc, hz, hzr⟩ := j.2
  rw [hji] at hzr
  obtain ⟨θ, hθ⟩ := hzr
  have h1 : h.disc i z = h.disc i (Work.CoreTopology.circlePoint θ) := by
    rw [h.disc_boundary i θ]; exact hθ.symm
  have h2 : z = Work.CoreTopology.circlePoint θ := h.disc_inj i h1
  have h3 : ‖(z : ℂ)‖ = 1 := by
    rw [h2, Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  rw [h3] at hz
  exact lt_irrefl _ hz

/-- **Pardon's Lemma 2 for an arbitrary sliced sphere, in the corrected vocabulary.**  Let `S` be
sliced by the surface in general position (`Work.InnermostDisk.SphereSlicing`), suppose the corrected
weak cut-and-paste `Work.Drive.CleansDiscsWd` holds, and suppose `S` meets the knot in fewer than
`min p q` points.  Then no essential loop of the surface lies in `S`. -/
theorem trace_inessential_of_slicing_of_countsWd
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {S : Set R3} (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsWd (Work.Smooth.Morse.torus ψ))
    (hcount : Set.encard (Set.range K.curve ∩ S) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  rintro ⟨γ, hγess, hγS⟩
  obtain ⟨D, hdisj⟩ := exists_innermostDisc_disjoint_of_slicing hslice ⟨γ, hγess, hγS⟩
  have hb : Work.Drive.BoundsDiskInComplementW (Work.Smooth.Morse.torus ψ) D.α :=
    hcl S D hdisj
  have hle := Work.Drive.min_le_encard_inter_of_boundsDiskW p q hp hq hc ψ K himg
    D.simple D.essential hb
  have hmono : Set.encard (Set.range D.α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ S) := by
    apply Set.encard_le_encard
    rintro x ⟨⟨t, rfl⟩, hxK⟩
    exact ⟨hxK, D.mem t⟩
  exact absurd (lt_of_le_of_lt (le_trans hle hmono) hcount) (lt_irrefl _)

/-- **The trace `F ∩ ∂PBox s c σ` carries no essential loop**, from the crux's sphere count, the
general position of the box sphere and the *corrected* cut-and-paste input. -/
theorem sphereTrace_inessential_of_countsWd
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcl : Work.Drive.CleansDiscsWd (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) := by
  intro hcon
  obtain ⟨D, hdisj⟩ := exists_innermostDisc_disjoint_of_slicing hslice.some hcon
  exact Work.Drive.not_exists_weakCompressingLoop_of_counts p q hp hq hc ψ K hd himg hsmall c σ
    hcount ⟨D.α, D.simple, D.essential, hcl _ D hdisj, D.mem⟩

/-- **The count and Pardon's Lemma 2 compose, in the corrected vocabulary**: any sliced sphere
inside the footprint `sphereSet c σ s ∪ cutDisc s c σ u` is clean. -/
theorem trace_inessential_of_slicing_of_subset_footprintWd
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {S : Set R3}
    (hsub : S ⊆ Work.BoxShrink.Core.sphereSet c σ s ∪ Work.BoxShrink.Core.cutDisc s c σ u)
    (hslice : Work.InnermostDisk.SphereSlicing (Work.Smooth.Morse.torus ψ) S)
    (hcl : Work.Drive.CleansDiscsWd (Work.Smooth.Morse.torus ψ))
    (hcountS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hcountU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop S := by
  refine trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg hslice hcl ?_
  refine lt_of_le_of_lt (Set.encard_le_encard ?_) (footprintCountBound p q hp hq K hd hsmall
    c σ u hcountS hcountU)
  rintro x ⟨hxK, hxS⟩
  exact ⟨hxK, hsub hxS⟩

end

end Work.EpsW
