import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Rectangular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Existence of a regular value in `(0,1)` for a smooth function on the half-space

`Work.PTGeometric.exists_regularValue_halfSpace`: if `ρ` is a smooth function on the closed
half-space `EuclideanHalfSpace N` whose values on the boundary avoid the interval `(0,1)`, then
some `c ∈ (0,1)` is a *regular value* of `ρ`: the manifold derivative of `ρ` does not vanish at any
point of the level set `ρ ⁻¹' {c}`.

The proof is Sard's theorem.  Level sets of values in `(0,1)` do not meet the boundary, so the
statement is about the interior of the half-space, which is an open subset of `EuclideanSpace ℝ
(Fin N)`; reading `ρ` in the coordinates of the half-space model gives a function `halfSpaceExt ρ`
on `EuclideanSpace ℝ (Fin N)` which is smooth on `{y | 0 < y 0}`, and the manifold derivative of
`ρ` at an interior point is the Fréchet derivative of `halfSpaceExt ρ` there.  Sard's theorem in the
rectangular case (`SardEuclidOn`, proved in `ThomBordism/Transversality/Sard/`) says that the image
of the critical set of `halfSpaceExt ρ` (inside the open set `{0 < y 0}`) has measure zero; a value
`c ∈ (0,1)` which is not a regular value would lie in that image, so the image would contain all of
`(0,1)`, contradicting the vanishing of its measure.
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Set MeasureTheory Function

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The representative of a function `ρ` on the half-space, read in the coordinates of the model
vector space `EuclideanSpace ℝ (Fin N)` (i.e. through the extended chart of the half-space model). -/
def halfSpaceExt (ρ : EuclideanHalfSpace N → ℝ) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun y => ρ ((modelWithCornersEuclideanHalfSpace N).symm y)

lemma halfSpaceExt_apply_of_le (ρ : EuclideanHalfSpace N → ℝ) {y : EuclideanSpace ℝ (Fin N)}
    (hy : 0 ≤ y 0) : halfSpaceExt ρ y = ρ ⟨y, hy⟩ := by
  simp [halfSpaceExt, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]

lemma halfSpaceExt_model (ρ : EuclideanHalfSpace N → ℝ) (y : EuclideanHalfSpace N) :
    halfSpaceExt ρ ((modelWithCornersEuclideanHalfSpace N) y) = ρ y := by
  rw [halfSpaceExt, ModelWithCorners.left_inv]

/-- The half-space model corners map the interior of the half-space onto `{y | 0 < y 0}`. -/
lemma mem_interior_range_of_pos {y : EuclideanSpace ℝ (Fin N)} (hy : 0 < y 0) :
    y ∈ interior (range (modelWithCornersEuclideanHalfSpace N)) := by
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  exact hy

lemma model_apply_zero (x : EuclideanHalfSpace N) :
    ((modelWithCornersEuclideanHalfSpace N) x) 0 = x.1 0 := rfl

lemma interior_range_mem_nhds {y : EuclideanSpace ℝ (Fin N)} (hy : 0 < y 0) :
    range (modelWithCornersEuclideanHalfSpace N) ∈ 𝓝 y :=
  Filter.mem_of_superset (isOpen_interior.mem_nhds (mem_interior_range_of_pos hy)) interior_subset

/-- **The manifold derivative of `ρ` is the Fréchet derivative of its Euclidean representative**,
at every point of the half-space. -/
lemma mfderiv_halfSpace_eq (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (x : EuclideanHalfSpace N) :
    mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ρ x
      = fderivWithin ℝ (halfSpaceExt ρ) (range (modelWithCornersEuclideanHalfSpace N))
          ((modelWithCornersEuclideanHalfSpace N) x) := by
  have hdiff : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N)
      (modelWithCornersSelf ℝ ℝ) ρ x :=
    (hρ x).mdifferentiableAt (by simp)
  rw [hdiff.mfderiv]
  have h1 : writtenInExtChartAt (modelWithCornersEuclideanHalfSpace N)
      (modelWithCornersSelf ℝ ℝ) x ρ = halfSpaceExt ρ := by
    funext y
    simp [writtenInExtChartAt, halfSpaceExt, extChartAt, chartAt_self_eq,
      OpenPartialHomeomorph.extend]
  have h2 : (extChartAt (modelWithCornersEuclideanHalfSpace N) x) x
      = (modelWithCornersEuclideanHalfSpace N) x := by
    simp [extChartAt, chartAt_self_eq, OpenPartialHomeomorph.extend]
  rw [h1, h2]
  all_goals first | rfl | (ext v; rfl) | simp

/-- **`halfSpaceExt ρ` is smooth on the interior of the half-space.** -/
lemma contDiffOn_halfSpaceExt (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (halfSpaceExt ρ)
      (interior (range (modelWithCornersEuclideanHalfSpace N))) := by
  intro y hy
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hy
  have hwit : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (halfSpaceExt ρ)
      (range (modelWithCornersEuclideanHalfSpace N)) y := by
    have hx := (contMDiffAt_iff.mp (hρ ((modelWithCornersEuclideanHalfSpace N).symm y))).2
    have hx' : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (writtenInExtChartAt (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
          ((modelWithCornersEuclideanHalfSpace N).symm y) ρ)
        (range (modelWithCornersEuclideanHalfSpace N))
        ((extChartAt (modelWithCornersEuclideanHalfSpace N)
          ((modelWithCornersEuclideanHalfSpace N).symm y))
          ((modelWithCornersEuclideanHalfSpace N).symm y)) := hx
    have e1 : writtenInExtChartAt (modelWithCornersEuclideanHalfSpace N)
        (modelWithCornersSelf ℝ ℝ) ((modelWithCornersEuclideanHalfSpace N).symm y) ρ
        = halfSpaceExt ρ := by
      funext z
      simp [writtenInExtChartAt, halfSpaceExt, extChartAt, chartAt_self_eq,
        OpenPartialHomeomorph.extend]
    have e2 : (extChartAt (modelWithCornersEuclideanHalfSpace N)
          ((modelWithCornersEuclideanHalfSpace N).symm y))
          ((modelWithCornersEuclideanHalfSpace N).symm y) = y := by
      rw [show (extChartAt (modelWithCornersEuclideanHalfSpace N)
            ((modelWithCornersEuclideanHalfSpace N).symm y))
            ((modelWithCornersEuclideanHalfSpace N).symm y)
          = (modelWithCornersEuclideanHalfSpace N)
            ((modelWithCornersEuclideanHalfSpace N).symm y) from by
        simp [extChartAt, chartAt_self_eq, OpenPartialHomeomorph.extend]]
      rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hy)]
      rfl
    rw [e1, e2] at hx'
    exact hx'
  exact hwit.mono interior_subset

/-- **Existence of a regular value in `(0,1)`.**  If `ρ : EuclideanHalfSpace N → ℝ` is smooth and
its boundary values avoid the interval `(0,1)`, then some `c ∈ (0,1)` is a regular value of `ρ`. -/
theorem exists_regularValue_halfSpace {N : ℕ} [NeZero N]
    (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hbdry : ∀ x : EuclideanHalfSpace N, x.1 0 = 0 → ρ x ∉ Set.Ioo (0 : ℝ) 1) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ x : EuclideanHalfSpace N, ρ x = c →
      mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ρ x ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := (OrthonormalBasis.singleton (Fin 1) ℝ).repr with he
  set g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 1) :=
    fun y => e (halfSpaceExt ρ y) with hg
  have hgsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
      (interior (range (modelWithCornersEuclideanHalfSpace N))) := by
    rw [hg]
    exact e.contDiff.comp_contDiffOn (contDiffOn_halfSpaceExt ρ hρ)
  have hcrit : ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))) ⊆
      ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint g y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))) := by
    rintro y ⟨hycrit, hyU⟩
    refine ⟨?_, hyU⟩
    have hdiff : DifferentiableAt ℝ (halfSpaceExt ρ) y :=
      ((contDiffOn_halfSpaceExt ρ hρ).differentiableOn (by simp)).differentiableAt
        (isOpen_interior.mem_nhds hyU)
    have hfderiv : fderiv ℝ g y =
        (↑↑e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp (fderiv ℝ (halfSpaceExt ρ) y) := by
      rw [hg]
      exact (fderiv_comp y e.differentiableAt hdiff).trans (by rw [e.fderiv])
    intro hsurj
    apply hycrit
    rw [hfderiv] at hsurj
    intro t
    obtain ⟨u, hu⟩ := hsurj (e t)
    exact ⟨u, e.injective hu⟩
  have hsard : volume (g '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint g y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N)))) = 0 :=
    (Work.ThomBordism.Transversality.Sard.sardEuclidOn_of_steps
      Work.ThomBordism.Transversality.Sard.sardSteps (N + 1) N 1 (by omega))
      g (interior (range (modelWithCornersEuclideanHalfSpace N))) isOpen_interior hgsmooth
  have hsard' : volume (g '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N)))) = 0 :=
    measure_mono_null (image_mono hcrit) hsard
  have hpre : volume (e ⁻¹' (g '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))))) = 0 :=
    e.measurePreserving.preimage_null hsard'
  have heq : e ⁻¹' (g '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))))
      = halfSpaceExt ρ '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))) := by
    rw [hg]
    ext y
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨s, hs, hs'⟩
      exact ⟨s, hs, e.injective hs'⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨s, hs, by rw [h]⟩
  have hzero : volume (halfSpaceExt ρ '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N)))) = 0 := by
    rw [heq] at hpre
    exact hpre
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ halfSpaceExt ρ '' ({y : EuclideanSpace ℝ (Fin N) |
        Work.ThomBordism.Transversality.IsCriticalPoint (halfSpaceExt ρ) y} ∩
        interior (range (modelWithCornersEuclideanHalfSpace N))) := by
    rintro c ⟨hc0, hc1⟩
    obtain ⟨x, hxc, hxder⟩ := hcon c ⟨hc0, hc1⟩
    have hxpos : 0 < x.1 0 := by
      rcases lt_trichotomy (x.1 0) 0 with h | h | h
      · exact absurd x.2 (not_le.mpr h)
      · exact absurd (hxc.symm ▸ (⟨hc0, hc1⟩ : c ∈ Set.Ioo (0 : ℝ) 1)) (hbdry x h)
      · exact h
    refine ⟨(modelWithCornersEuclideanHalfSpace N) x, ⟨?_, ?_⟩, ?_⟩
    · have hzero' : fderiv ℝ (halfSpaceExt ρ)
          ((modelWithCornersEuclideanHalfSpace N) x) = 0 := by
        have h1 := mfderiv_halfSpace_eq ρ hρ x
        rw [hxder] at h1
        have hmem : range (modelWithCornersEuclideanHalfSpace N) ∈ 𝓝
            ((modelWithCornersEuclideanHalfSpace N) x) :=
          interior_range_mem_nhds (by simpa [model_apply_zero] using hxpos)
        rw [← fderivWithin_of_mem_nhds hmem]
        exact h1.symm
      intro hsurj
      rw [hzero'] at hsurj
      obtain ⟨u, hu⟩ := hsurj 1
      simpa using hu
    · exact mem_interior_range_of_pos (by simpa [model_apply_zero] using hxpos)
    · rw [halfSpaceExt_model ρ x]
      exact hxc
  have hvol : volume (Set.Ioo (0 : ℝ) 1) = 0 := measure_mono_null hsub hzero
  rw [Real.volume_Ioo] at hvol
  simp at hvol

end

end Work.PTGeometric
