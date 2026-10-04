import Mathlib
import Submission.Length
import Submission.Geodesic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.indexTransfer

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle MeasureTheory

/-- **The squared speed of a `C¹` curve is interval-integrable on subintervals of `[0,S]`.**

For a curve `γ : ℝ → M` of class `C¹` on the closed interval `[0,S]`, the square of the Riemannian
speed, `s ↦ (curveSpeed γ s)²`, is interval-integrable on every subinterval `[a,b] ⊆ [0,S]`.

The definition of `curveSpeed` goes through `mfderiv` (the *unrestricted* derivative), whose junk
value `0` can occur at the two endpoints: the hypothesis only bounds `γ` on the closed interval.
The workaround is to compare `(curveSpeed γ)²` with the continuous "within-interval" squared speed

`g t = ⟪(mfderivWithin 𝓘(ℝ) I γ (Icc a b) t) 1, (mfderivWithin 𝓘(ℝ) I γ (Icc a b) t) 1⟫`,

which is continuous on `Icc a b` by `ContMDiffOn.continuousOn_tangentMapWithin` (the tangent map of
a `C¹` function is continuous) composed with the constant unit section, using the continuity of the
metric along continuous sections (`ContinuousOn.inner_bundle`).  The two functions agree on the open
interval `Ioo a b`, hence almost everywhere on `Icc a b`; a continuous function is integrable on a
compact interval. -/
theorem intervalIntegrable_curveSpeed_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {γ : ℝ → M} {S : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc (0 : ℝ) S))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ S) :
    IntervalIntegrable (fun s : ℝ => (Submission.Length.curveSpeed (I := I) γ s)^2)
      MeasureTheory.volume a b := by
  rcases lt_or_ge a b with hlt | hle
  · -- Main case `a < b`.
    have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) S := Set.Icc_subset_Icc ha hb
    have hγab : ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc a b) := hγ.mono hsub
    -- The Riemannian bundle is in particular a *continuous* Riemannian bundle.
    haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
      obtain ⟨Φ, hΦsm, hΦ⟩ :=
        (inferInstance : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
          (fun x : M ↦ TangentSpace I x)).exists_contMDiff
      exact ⟨Φ, hΦsm.continuous, hΦ⟩
    -- The tangent map of `γ` within `[a,b]` is continuous.
    have hs_umd : UniqueMDiff[Set.Icc a b] := UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc hlt)
    have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I γ (Set.Icc a b))
        (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) :=
      hγab.continuousOn_tangentMapWithin le_rfl hs_umd
    -- The constant unit section of the tangent bundle of the model space `ℝ`.
    have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
        TangentBundle 𝓘(ℝ) ℝ)) (Set.Icc a b) :=
      ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
        (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
    have hcomp : ContinuousOn (fun t : ℝ =>
        (⟨γ t, (mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ)⟩ : TangentBundle I M))
        (Set.Icc a b) :=
      htan.comp hκ (fun t ht => by simpa using ht)
    -- The "within-interval" squared speed.
    have hg2 : ContinuousOn (fun t : ℝ =>
        inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
          ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))) (Set.Icc a b) :=
      ContinuousOn.inner_bundle (b := γ) hcomp hcomp
    have hintg2 : IntegrableOn (fun t : ℝ =>
        inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
          ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))) (Set.Icc a b) volume :=
      hg2.integrableOn_Icc
    -- It agrees with the squared speed on the interior of `[a,b]`.
    have hgspeed : ∀ t ∈ Set.Ioo a b,
        (Submission.Length.curveSpeed (I := I) γ t)^2
          = inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
              ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ)) := by
      intro t ht
      have hmem : Set.Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      rw [Submission.Length.curveSpeed_sq, mfderivWithin_of_mem_nhds hmem,
        Submission.Geodesic.curveVelocity_apply]
    -- The two functions differ at most at the two endpoints.
    have hbad : volume {t : ℝ | ¬ (t ∈ Set.Icc a b →
        (Submission.Length.curveSpeed (I := I) γ t)^2
          = inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
              ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ)))} = 0 := by
      refine MeasureTheory.measure_mono_null (t := ({a} ∪ {b} : Set ℝ)) ?_ ?_
      · intro t ht
        rw [Set.mem_ofPred_eq, Classical.not_imp] at ht
        obtain ⟨hts, hne⟩ := ht
        by_cases hat : t = a
        · exact Or.inl hat
        · right
          by_contra hbt
          exact hne (hgspeed t ⟨lt_of_le_of_ne hts.1 (Ne.symm hat),
            lt_of_le_of_ne hts.2 hbt⟩)
      · rw [MeasureTheory.measure_union_null_iff]
        exact ⟨Real.volume_singleton, Real.volume_singleton⟩
    -- Hence the two functions are almost everywhere equal on `[a,b]`.
    have hae : (fun t : ℝ => (Submission.Length.curveSpeed (I := I) γ t)^2)
        =ᵐ[volume.restrict (Set.Icc a b)] (fun t : ℝ =>
          inner ℝ ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))
            ((mfderivWithin 𝓘(ℝ) I γ (Set.Icc a b) t) (1 : ℝ))) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Icc,
        MeasureTheory.ae_iff]
      exact hbad
    have hintcs : IntegrableOn (fun t : ℝ => (Submission.Length.curveSpeed (I := I) γ t)^2)
        (Set.Icc a b) volume := hintg2.congr_fun_ae hae.symm
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hintcs.mono_set Set.Ioc_subset_Icc_self)
  · -- Degenerate case `b ≤ a` (so `a = b`): the interval has measure zero.
    have hab' : a = b := le_antisymm hab hle
    subst hab'
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl]
    simp

end Work.OddBound.indexTransfer
