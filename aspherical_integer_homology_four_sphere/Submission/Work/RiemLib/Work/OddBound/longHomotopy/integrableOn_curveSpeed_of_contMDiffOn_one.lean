import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle MeasureTheory

/-!
# Integrability of the speed of a `C¹` curve on a closed interval

For a curve `γ : ℝ → M` of class `C¹` on the closed interval `[a,b]`, the Riemannian speed
`s ↦ curveSpeed γ s` is integrable on `[a,b]`.

The definition of `curveSpeed` goes through `mfderiv` (the *unrestricted* derivative), whose junk
value `0` can occur at the two endpoints `a`, `b` of the interval: the hypothesis only bounds `γ`
on the closed interval.  The workaround is to compare `curveSpeed γ` with the continuous
"within-interval" speed

`g t = √⟪(mfderivWithin 𝓘(ℝ) I γ (Icc a b) t) 1, (mfderivWithin 𝓘(ℝ) I γ (Icc a b) t) 1⟫`,

which is continuous on `Icc a b` by `ContMDiffOn.continuousOn_tangentMapWithin` (the tangent map of
a `C¹` function is continuous) composed with the constant unit section, using the continuity of the
metric along continuous sections (`ContinuousOn.inner_bundle`).  The two functions agree on the
open interval `Ioo a b`, hence almost everywhere on `Icc a b`; a continuous function is integrable
on a compact interval.

This is the general-interval version of the corresponding statement in `curveLength_toolkit`.
-/

/-- **The speed of a `C¹` curve is integrable.**  For `γ : ℝ → M` of class `C¹` on the closed
interval `[a,b]`, the Riemannian speed of `γ` is integrable on `[a,b]`. -/
theorem integrableOn_curveSpeed_of_contMDiffOn_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc a b)) :
    IntegrableOn (fun s : ℝ => Submission.Length.curveSpeed (I := I) γ s) (Set.Icc a b) volume := by
  rcases lt_or_ge a b with hlt | hle
  · -- Main case `a < b`.
    -- The Riemannian bundle is in particular a *continuous* Riemannian bundle.
    haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
      obtain ⟨Φ, hΦsm, hΦ⟩ :=
        (inferInstance : IsContMDiffRiemannianBundle I ∞ E
          (fun x : M ↦ TangentSpace I x)).exists_contMDiff
      exact ⟨Φ, hΦsm.continuous, hΦ⟩
    -- The tangent map of `γ` within `[a,b]` is continuous.
    have hs_umd : UniqueMDiff[Set.Icc a b] := UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc hlt)
    have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I γ (Set.Icc a b))
        (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) :=
      hγ.continuousOn_tangentMapWithin le_rfl hs_umd
    -- The constant unit section of the tangent bundle of the model space `ℝ`.
    have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
        TangentBundle 𝓘(ℝ) ℝ)) (Set.Icc a b) :=
      ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
        (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
    have hcomp : ContinuousOn (fun t : ℝ =>
        (⟨γ t, (mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ)⟩ : TangentBundle I M))
        (Set.Icc a b) :=
      htan.comp hκ (fun t ht => by simpa using ht)
    -- The "within-interval" speed.
    set g : ℝ → ℝ := fun t => Real.sqrt
      (inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))) with hgdef
    have hgcont : ContinuousOn g (Set.Icc a b) :=
      (ContinuousOn.inner_bundle (b := γ) hcomp hcomp).sqrt
    -- It agrees with `curveSpeed` on the interior of `[a,b]`.
    have hgspeed : ∀ t ∈ Set.Ioo a b, g t = Submission.Length.curveSpeed (I := I) γ t := by
      intro t ht
      have hmem : Set.Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      show Real.sqrt (inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ)))
          = Submission.Length.curveSpeed (I := I) γ t
      rw [mfderivWithin_of_mem_nhds hmem, Submission.Length.curveSpeed_def,
        Submission.Geodesic.curveVelocity_apply]
    -- A continuous function is integrable on the compact interval.
    have hintg : IntegrableOn g (Set.Icc a b) volume := hgcont.integrableOn_Icc
    -- The two functions differ at most at the two endpoints.
    have hbad : volume {t : ℝ | ¬ (t ∈ Set.Icc a b →
        Submission.Length.curveSpeed (I := I) γ t = g t)} = 0 := by
      refine MeasureTheory.measure_mono_null (t := ({a} ∪ {b} : Set ℝ)) ?_ ?_
      · intro t ht
        rw [Set.mem_ofPred_eq, Classical.not_imp] at ht
        obtain ⟨hts, hne⟩ := ht
        by_cases ha : t = a
        · exact Or.inl ha
        · right
          by_contra hb
          exact hne (hgspeed t ⟨lt_of_le_of_ne hts.1 (Ne.symm ha),
            lt_of_le_of_ne hts.2 hb⟩).symm
      · rw [MeasureTheory.measure_union_null_iff]
        exact ⟨Real.volume_singleton, Real.volume_singleton⟩
    -- Hence the two functions are almost everywhere equal on `[a,b]`.
    have hae : (fun t : ℝ => Submission.Length.curveSpeed (I := I) γ t)
        =ᵐ[volume.restrict (Set.Icc a b)] g := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Icc,
        MeasureTheory.ae_iff]
      exact hbad
    exact hintg.congr_fun_ae hae.symm
  · -- Degenerate case `b ≤ a`: the interval `[a,b]` has measure zero.
    refine MeasureTheory.IntegrableOn.of_measure_zero ?_
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
    exact sub_nonpos.mpr hle

end Work.OddBound.longHomotopy
