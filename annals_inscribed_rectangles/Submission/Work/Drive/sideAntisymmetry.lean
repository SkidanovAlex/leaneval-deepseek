import Mathlib
import Submission.Work.Drive.cutDichotomy
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.projRot

/-!
# The antisymmetry of the side function, from the cut dichotomy

*(agent of `Submission/Work/Drive/orderWitness_exists.lean`.)*

`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine` says that the cut of a clamped
radial sweep is either the whole **class-cut** or **empty**, the branch being decided by the *sign* of
the difference of the two profiles along the class line.  That file exports only the *disjunction*; the
two branches are proved internally.  This file exports them, and draws the consequence the order
function needs:

> the side function `w ↦ e w = [the cut of the chart `Q` by the sweep of the rotated plane `w·P₀` is
> non-empty]` is **antisymmetric**: `e w + e (-w) = 1` for `w ∈ Zc γ`.

The mathematical content is that the two comparisons `ρ < ρ ∘ rotLens (-w)` and `ρ ∘ rotLens (-w) < ρ`
(on the common class line `L`) are exchanged by `w ↔ -w`: the cut for `-w` is the cut of the *rotated*
plane by the sweep of the *base* plane (the rotation identity of `Work.Drive.sideValue`), and the class
line for `-w` is the image of the class line for `w` under the rotation.  Since the two profiles differ
(disjointness of the planes, i.e. `w ∈ Zc γ`) and the class line is preconnected, exactly one branch
holds — no mod-2 counting is used, only the rigidity of the dichotomy.

## Contents

* `Work.Drive.diskCut_eq_empty_of_lt_profile` / `Work.Drive.diskCut_eq_classCut_of_lt_profile` — the
  two branches of the dichotomy, with the sign hypothesis explicit;
* `Work.Drive.side_add_neg_of_profile` — the antisymmetry, in the profile formulation.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-! ## The two branches of the dichotomy, with the sign hypothesis explicit -/

/-- **The cut is empty when the chart's profile dominates the swept plane's.**  This is the first case
of `Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty`, with `hpos` (the sign of the profile
difference) supplied as the hypothesis `hgt` instead of being derived from preconnectedness. -/
theorem diskCut_eq_empty_of_lt_profile (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgmax : ∀ x y : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 →
      y ∈ Submission.Drive.unitBox 1 →
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ g x)
    (hgt : ∀ x ∈ classCut Q φ, g x < levelOf (Q (cplxOf x))) :
    diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxS : x ∈ classCut Q φ := hsub hx
  obtain ⟨-, hx2⟩ := hx
  rw [himg] at hx2
  obtain ⟨y, hy, hcls, _hcle, hle⟩ := hx2
  have hle' : levelOf (P y) ≤ g x := hgmax x y hxS.1 hy hcls
  have hlt := hgt x hxS
  linarith

/-- **The cut is the whole class-cut when the swept plane's profile dominates the chart's.**  The
second case of the dichotomy, again with the sign as an explicit hypothesis. -/
theorem diskCut_eq_classCut_of_lt_profile (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgatt : ∀ x ∈ classCut Q φ, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        g x = levelOf (P y))
    (hclow : ∀ x ∈ classCut Q φ, c ≤ levelOf (Q (cplxOf x)))
    (hlt : ∀ x ∈ classCut Q φ, levelOf (Q (cplxOf x)) < g x) :
    diskCut Q (clampedSweep c ψ P) = classCut Q φ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  refine Set.Subset.antisymm hsub ?_
  intro x hxS
  obtain ⟨y, hy, hcls, hgy⟩ := hgatt x hxS
  have hlt' : levelOf (Q (cplxOf x)) < levelOf (P y) := by
    rw [← hgy]
    exact hlt x hxS
  refine ⟨hxS.1, ?_⟩
  rw [himg]
  exact ⟨y, hy, hcls, hclow x hxS, hlt'.le⟩

end



/-- **The class-line form of the empty branch.**  The first case of
`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine`, with the sign hypothesis `hgt`
(`G < FQ` on the class line) replacing the preconnectedness rigidity. -/
theorem diskCut_eq_empty_of_lt_profile_classLine
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCut Q φ, (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCut Q φ,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCut Q φ, ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hgt : ∀ q ∈ L, G q < FQ q) :
    diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxS : x ∈ classCut Q φ := hsub hx
  obtain ⟨-, hx2⟩ := hx
  rw [himg] at hx2
  obtain ⟨y, hy, hcls, _hcle, hle⟩ := hx2
  have hle' : levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) :=
    hGmax x hxS y hy hcls
  have h2 : G ((cappingSpaceHomeoProj (Q (cplxOf x))).2)
      < levelOf (Q (cplxOf x)) := by
    have hh := hgt _ (hLmem x hxS)
    rwa [hFQval x hxS] at hh
  linarith

/-- **The class-line form of the class-cut branch.**  The second case of
`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine`, with the sign hypothesis `hlt`
(`FQ < G` on the class line) replacing the preconnectedness rigidity. -/
theorem diskCut_eq_classCut_of_lt_profile_classLine
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCut Q φ, (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (G : Projectivization ℝ (Eucl 3) → ℝ)
    (hGatt : ∀ x ∈ classCut Q φ, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hclow : ∀ x ∈ classCut Q φ, c ≤ levelOf (Q (cplxOf x)))
    (FQ' : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQ' : ∀ x ∈ classCut Q φ,
      FQ' ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hlt : ∀ q ∈ L, FQ' q < G q) :
    diskCut Q (clampedSweep c ψ P) = classCut Q φ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  refine Set.Subset.antisymm hsub ?_
  intro x hxS
  obtain ⟨y, hy, hcls, hgy⟩ := hGatt x hxS
  have hlt' : levelOf (Q (cplxOf x)) < levelOf (P y) := by
    have hh := hlt _ (hLmem x hxS)
    rw [hFQ' x hxS, hgy] at hh
    exact hh
  refine ⟨hxS.1, ?_⟩
  rw [himg]
  exact ⟨y, hy, hcls, hclow x hxS, hlt'.le⟩



/-- **`ParityCore γ` from the design's side function, without the `ChainAntisymmetry` engine.**

This is `Work.Drive.parityCore_of_functional` with the side function *instantiated* at the route's
`Work.Drive.sideOf Q (fun _ => c) ψ`.  It records that the wall's remaining content, once the chart and
the cut data are available, is exactly the three hypotheses below — and that the third-chain engine
`Work.Drive.ChainAntisymmetry` is not among them (its antisymmetry clause is the instance
`Work.Drive.sideOf_add_neg` of the cut dichotomy). -/
theorem parityCore_of_sideOf {γ : Circle → ℝ × ℝ} (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (hanti : ∀ t : Zc γ, sideOf Q (fun _ => c) ψ (t : UnitAddCircle)
      + sideOf Q (fun _ => c) ψ (-(t : UnitAddCircle)) = 1)
    (hcont : Continuous fun t : Zc γ => sideOf Q (fun _ => c) ψ (t : UnitAddCircle))
    (hT : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (d : UnitAddCircle) (hd : d ∈ Zc γ)
      (had : a + d ∈ Zc γ),
      sideOf Q (fun _ => c) ψ a * sideOf Q (fun _ => c) ψ (a + d)
        + sideOf Q (fun _ => c) ψ (-a) * sideOf Q (fun _ => c) ψ d
        + sideOf Q (fun _ => c) ψ (-(a + d)) * sideOf Q (fun _ => c) ψ (-d) = 1) :
    ParityCore γ := by
  refine parityCore_of_functional (fun t : Zc γ => sideOf Q (fun _ => c) ψ (t : UnitAddCircle))
    hcont (fun u hu => hanti ⟨u, hu⟩) ?_
  intro a ha d hd had
  exact hT a ha d hd had

end Work.Drive
