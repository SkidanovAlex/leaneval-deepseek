import Mathlib
import Submission.Work.Drive.Final.crux_core_wd
import Submission.Work.Drive.EpsFormSphere.OpenTiltedRegion
import Submission.Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps
import Submission.Work.EpsW.countsWd
import Submission.Work.Drive.EpsForm.sliceWallRoute
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

/-!
# The *corrected* tilted sweep, and its endpoint: Pardon's exact half-box conclusion

`Work.Drive.TiltedSweepExists` (in the shared file `Drive/pardon_of_cleansW_sphere.lean`) sweeps the
region

  `openTiltedSweepRegion P s c σ u v h ℓ lam = carrier ∩ (PBox ∖ (tiltedSlabClosed (⟪v,c⟫+u) v h ∩ {ℓ ≤ lam}))`

from the box region to `boxRegion ∖ tiltedSlabClosed`, with the four fields of Pardon's argument
(regularity, rank jump `≤ 1`, and a dichotomy per stretch).  Its size condition, however, is
`‖v − e_{σ2}‖ ≤ ε ∧ ε·R < h` with `ε` the *same* `ε` as the conclusion's perturbation parameter: for
`ε` large the slab `tiltedSlabClosed` swallows the whole box (`h > εR ≥ 2R ≥ 2‖y−c‖`), the end region
is empty, and the four fields become *unsatisfiable* (`W(boxRegion) = ⊤ ≠ ⊥ = W(∅)`).  The corrected
size condition is the `ε`-free one

  `‖v − e_{σ2}‖ · R < h`,

which is what the endpoint argument actually uses: a point of `boxRegion` outside the slab satisfies

  `y (σ 2) − c (σ 2) − u > h − ‖v − e_{σ2}‖ · ‖y − c‖ ≥ h − ‖v − e_{σ2}‖ · R > 0`

(or the same with `< 0`), so the end region lies in the *open* upper half or the *open* lower half of
the box — Pardon's exact `doublebubble` conclusion, with no perturbation margin.

This file proves the endpoint: the corrected residual together with `W(boxRegion) = ⊤` gives
`CruxCoreWd` (Pardon's exact half-box conclusion at the crux configurations).  Everything else along
the sweep (the constancy of the span by `submodule_const_of_finrank_jumps`, the two free endpoints,
the box-region span) is already in the workspace.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.Final

noncomputable section

/-- **The corrected tilted-sweep residual.**  At every counted crux configuration there are a unit
direction `v` with `‖v − e_{σ2}‖ · R < h` (the slab tilt is controlled by the box radius, *not* by
the perturbation parameter), a half-width `h > 0`, a radius `R` bounding the box, a wall functional
`ℓ`, end levels `lam0 < lam1` and a finite exceptional set `exc` such that the open tilted sweep
`openTiltedSweepRegion` satisfies

* `hreg`: the span is constant between two levels with no exceptional value in between,
* `hjump`: across a single exceptional value the `H₁`-rank jumps by at most `1`,
* `hone`: on every stretch free of exceptional values some level has span `⊥` or `⊤`.

The two endpoints are free (`openTiltedSweepRegion_eq_boxRegion` / `_eq_sdiff`), so the residual
starts at the box region and ends at `boxRegion ∖ tiltedSlabClosed`. -/
def TiltedSweepExists' : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
            ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
              ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
              (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
              (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
              (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
              (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
              (∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ ν < t) →
                Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ μ) =
                  Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) ∧
              (∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
                Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
                    (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ μ)) ≤
                  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
                    (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) + 1 ∧
                Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
                    (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) ≤
                  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
                    (Work.Drive.EpsSphere.torusOf ψ)
                    (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ μ)) + 1) ∧
              (∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
                (∀ t ∈ exc, t < μ ∨ ν < t) →
                ∃ mu : ℝ, μ ≤ mu ∧ mu ≤ ν ∧ (∀ t ∈ exc, t ≠ mu) ∧
                  (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                        (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                          (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) = ⊥ ∨
                   Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                        (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                          (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) = ⊤))

/-- The upper and lower halves of the box are open in the carrier. -/
theorem isOpenInCarrier_upperHalf {P : Work.CoreTopology.ParamTorus} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.upperHalf c σ u) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  have hcont : Continuous fun x : P.carrier => (x : R3) (σ 2) := by fun_prop
  exact isOpen_lt continuous_const hcont

/-- The lower half of the box is open in the carrier. -/
theorem isOpenInCarrier_lowerHalf {P : Work.CoreTopology.ParamTorus} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.lowerHalf c σ u) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  have hcont : Continuous fun x : P.carrier => (x : R3) (σ 2) := by fun_prop
  exact isOpen_lt hcont continuous_const

/-- **The corrected tilted sweep gives Pardon's exact half-box conclusion.**  The sweep runs the
region from `boxRegion` (span `⊤`, from `HasEssBox`) to `boxRegion ∖ tiltedSlabClosed`; by the
corrected size condition that end region is contained in the two *open* halves of the box; the two
halves are open in the carrier and disjoint, so one of them already carries the essential loop. -/
theorem cruxCoreWd_of_tiltedSweepExists' (h : TiltedSweepExists') :
    ∀ p q : ℕ, CruxCoreWd p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hvtilt, hh, hR, hlow, hhigh, hl, hexc, hreg, hjump,
    hone⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have hspos : 0 < s := lt_trans hr hrs
  -- ## 1. the box region has winding span `⊤`
  have hess : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hspos c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  obtain ⟨hstart, hconst, hfin⟩ :
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam0) = ⊤ ∧
        (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (Work.Drive.EpsFormSphere.openTiltedSweepRegion
              (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam0) =
          Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (Work.Drive.EpsFormSphere.openTiltedSweepRegion
              (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam1)) ∧
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (Work.Drive.EpsFormSphere.openTiltedSweepRegion
              (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam1) = ⊤ := by
    have h0 : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion
          (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam0) = ⊤ := by
      rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
      exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential
        hspos hslice hess hne
    have hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (Work.Drive.EpsFormSphere.openTiltedSweepRegion
              (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
          Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (Work.Drive.EpsFormSphere.openTiltedSweepRegion
              (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤ :=
      Work.Drive.dichotomy_every_level_of_one_per_stretch (V := fun lam : ℝ =>
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam)) exc hexc hreg hone
    have h1 := Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps
      (V := fun lam : ℝ => Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion
          (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam))
      lam0 lam1 exc hl hexc hreg hjump hdich
    exact ⟨h0, h1, h1 ▸ h0⟩
  -- ## 2. the end region is `boxRegion ∖ tiltedSlabClosed`
  rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_sdiff hhigh] at hfin
  -- ## 3. every point of the end region lies strictly above or below the plane
  have hmem_split : ∀ y ∈ Work.BoxShrink.Core.boxRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h,
      y ∈ Work.BoxShrink.Core.upperHalf c σ u ∨ y ∈ Work.BoxShrink.Core.lowerHalf c σ u := by
    intro y hy
    obtain ⟨⟨hyc, hyb⟩, hyslab⟩ := hy
    -- the slab datum, as an inequality of the tilted functional
    have hbig : h < |inner ℝ v (y - c) - u| := by
      have h1 : ¬ |inner ℝ v y - (inner ℝ v c + u)| ≤ h := hyslab
      have h2 : inner ℝ v y - (inner ℝ v c + u) = inner ℝ v (y - c) - u := by
        rw [inner_sub_right]; ring
      rw [h2] at h1
      exact not_le.mp h1
    have hcoord : inner ℝ e (y - c) = y (σ 2) - c (σ 2) := by
      rw [he, Work.BoxShrink.shiftVσ]
      simp [PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply]
    have hsplit : inner ℝ v (y - c) - u =
        (y (σ 2) - c (σ 2) - u) + inner ℝ (v - e) (y - c) := by
      rw [inner_sub_left]; rw [hcoord]; ring
    have hCS : |inner ℝ (v - e) (y - c)| ≤ ‖v - e‖ * ‖y - c‖ := abs_real_inner_le_norm _ _
    have hyR : ‖y - c‖ ≤ R := hR y hyb
    rcases lt_abs.mp hbig with hgt | hlt
    · -- above the plane
      refine Or.inl ?_
      show c (σ 2) + u < y (σ 2)
      have h3 : ‖v - e‖ * ‖y - c‖ ≤ ‖v - e‖ * R :=
        mul_le_mul_of_nonneg_left hyR (norm_nonneg _)
      have hup' : inner ℝ (v - e) (y - c) ≤ ‖v - e‖ * R := by
        have h1 : inner ℝ (v - e) (y - c) ≤ |inner ℝ (v - e) (y - c)| := le_abs_self _
        linarith [hCS, h3]
      have hkey : y (σ 2) - c (σ 2) - u =
          (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by linarith [hsplit]
      have h5 : 0 < h - ‖v - e‖ * R := by linarith
      have hpos : 0 < (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by linarith
      have : 0 < y (σ 2) - c (σ 2) - u := hkey.symm ▸ hpos
      linarith
    · -- below the plane
      refine Or.inr ?_
      show y (σ 2) < c (σ 2) + u
      have h3 : ‖v - e‖ * ‖y - c‖ ≤ ‖v - e‖ * R :=
        mul_le_mul_of_nonneg_left hyR (norm_nonneg _)
      have hlow' : -(‖v - e‖ * R) ≤ inner ℝ (v - e) (y - c) := by
        have h1 : -|inner ℝ (v - e) (y - c)| ≤ inner ℝ (v - e) (y - c) := neg_abs_le _
        linarith [hCS, h3]
      have hkey : y (σ 2) - c (σ 2) - u =
          (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by linarith [hsplit]
      have h5 : (inner ℝ v (y - c) - u) < -h := by linarith
      have hneg : (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) < 0 := by linarith
      have : y (σ 2) - c (σ 2) - u < 0 := hkey.symm ▸ hneg
      linarith
  -- ## 4. the split of the end region into the two open halves
  set X : Set R3 := Work.BoxShrink.Core.boxRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h with hX
  set A : Set R3 := X ∩ Work.BoxShrink.Core.upperHalf c σ u with hA
  set B : Set R3 := X ∩ Work.BoxShrink.Core.lowerHalf c σ u with hB
  have hXeq : X = (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) := by
    rw [hX, Work.BoxShrink.Core.boxRegion]
    ext y
    constructor
    · rintro ⟨⟨hyc, hyb⟩, hys⟩
      exact ⟨hyc, hyb, hys⟩
    · rintro ⟨hyc, hyb, hys⟩
      exact ⟨⟨hyc, hyb⟩, hys⟩
  have hXopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) X := by
    rw [hXeq]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (P := Work.Drive.EpsSphere.torusOf ψ)
      ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
        (Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h))
  have hAopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) A :=
    Work.SurgeryInvariance.isOpenInCarrier_inter (Work.Drive.EpsSphere.torusOf ψ) hXopen
      isOpenInCarrier_upperHalf
  have hBopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) B :=
    Work.SurgeryInvariance.isOpenInCarrier_inter (Work.Drive.EpsSphere.torusOf ψ) hXopen
      isOpenInCarrier_lowerHalf
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hyu⟩ ⟨-, hyl⟩
    have hyu' : c (σ 2) + u < y (σ 2) := hyu
    have hyl' : y (σ 2) < c (σ 2) + u := hyl
    exact absurd (lt_trans hyu' hyl') (lt_irrefl _)
  have hAB : A ∪ B = X := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact hy.1
    · intro hy
      rcases hmem_split y hy with hy' | hy'
      · exact Or.inl ⟨hy, hy'⟩
      · exact Or.inr ⟨hy, hy'⟩
  -- ## 5. one of the two halves carries an essential loop
  have hspan : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) A ⊔
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) B = ⊤ := by
    rw [← Work.SurgeryInvariance.Span.union_eq_sup hAopen hBopen hdisj, hAB]
    exact hfin
  have hcase : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) A ≠ ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) B ≠ ⊥ := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2, bot_sup_eq] at hspan
    exact bot_ne_top hspan
  rcases hcase with hAne | hBne
  · obtain ⟨γ, hγ, hmem⟩ :=
      (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ A).mp hAne
    refine Or.inr ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨⟨⟨-, hP⟩, hyslab⟩, hupper⟩ := hmem t
    exact ⟨hP, hupper⟩
  · obtain ⟨γ, hγ, hmem⟩ :=
      (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ B).mp hBne
    refine Or.inl ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨⟨⟨-, hP⟩, hyslab⟩, hlower⟩ := hmem t
    exact ⟨hP, hlower⟩

end

end Work.Drive.Final
