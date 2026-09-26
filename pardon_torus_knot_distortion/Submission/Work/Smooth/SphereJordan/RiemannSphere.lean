import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.exists_planeCurve_of_avoids_infty
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscs
import Submission.Work.Smooth.SphereJordan.exists_notMem_iUnion_range

/-!
# Jordan–Schoenflies on the Riemann sphere, from the planar theorem

This is the assembly of the sphere side of the chapter.

* `twoDiscs_of_pointOff` — a simple closed curve of `ℂ ∪ {∞}` which misses a point is the common
  boundary of two complementary embedded discs: move the missing point to `∞` by a Möbius
  transformation (`exists_homeomorph_infty_eq`), so that the curve becomes a *plane* curve, apply the
  planar two-disc theorem `planeTwoDiscs`, and transport back along the Möbius transformation.
* `schoenfliesRiemannSphere` — every simple closed curve of `ℂ ∪ {∞}` misses a point
  (`exists_notMem_iUnion_range` for a one-element family), hence `SchoenfliesRiemannSphere`.
* `jordanSchoenfliesRiemannSphere` — the same for a finite family of pairwise disjoint curves,
  together with the standard position: a point off the union exists and
  `familyDataOfTwoDiscs` produces the nested discs and the rank.

The transport to the round sphere `Metric.sphere (0 : ℝ³) 1` is in `RoundSphere.lean`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **A simple closed curve of the Riemann sphere which misses a point bounds two complementary
discs**, from the planar Jordan–Schoenflies theorem. -/
theorem twoDiscs_of_pointOff (h : PlaneHypothesis) {c : ℝ → RiemannSphere}
    (hc : IsSimpleClosedCurve c) {p : RiemannSphere} (hp : p ∉ Set.range c) :
    Nonempty (TwoDiscs c) := by
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_infty_eq p
  have hmiss : ∀ t : ℝ, Φ.symm (c t) ≠ infty := by
    intro t ht
    refine hp ?_
    have h1 : Φ (Φ.symm (c t)) = Φ infty := by rw [ht, hΦ]
    rw [Homeomorph.apply_symm_apply] at h1
    exact ⟨t, h1.trans hΦ⟩
  have hc' : IsSimpleClosedCurve (fun t => Φ.symm (c t)) :=
    ⟨Φ.symm.continuous.comp hc.1,
      fun t => by show Φ.symm (c (t + 2 * Real.pi)) = Φ.symm (c t); rw [hc.2.1 t],
      fun a ha b hb hab => hc.2.2 ha hb (Φ.symm.injective hab)⟩
  obtain ⟨γ, hcont, hper, hinj, hcoe⟩ := exists_planeCurve_of_avoids_infty hc' hmiss
  obtain ⟨d⟩ := planeTwoDiscs h hcont hper hinj
  have hd : TwoDiscs (fun t => Φ.symm (c t)) := TwoDiscs.congr (fun t => (hcoe t).symm) d
  have h2 := hd.mapHomeomorph Φ
  exact ⟨TwoDiscs.congr (fun t => by simp) h2⟩

/-- **Jordan–Schoenflies for one simple closed curve on the Riemann sphere.** -/
theorem schoenfliesRiemannSphere (h : PlaneHypothesis) : SchoenfliesRiemannSphere := by
  intro c hc
  obtain ⟨p, hp⟩ := exists_notMem_iUnion_range (fun _ : PUnit => c) (fun _ => hc)
  exact twoDiscs_of_pointOff h hc (hp PUnit.unit)

/-- **Jordan–Schoenflies and standard position for a finite family of pairwise disjoint simple
closed curves on the Riemann sphere.** -/
theorem jordanSchoenfliesRiemannSphere (h : PlaneHypothesis) : JordanSchoenfliesRiemannSphere := by
  intro ι _ c hs hd
  have h2 : ∀ i : ι, TwoDiscs (c i) := fun i => (schoenfliesRiemannSphere h (c i) (hs i)).some
  obtain ⟨x₀, hx₀⟩ := exists_notMem_iUnion_range c hs
  exact familyDataOfTwoDiscs hs hd h2 x₀ hx₀

end

end Work.Smooth.SphereJordan
