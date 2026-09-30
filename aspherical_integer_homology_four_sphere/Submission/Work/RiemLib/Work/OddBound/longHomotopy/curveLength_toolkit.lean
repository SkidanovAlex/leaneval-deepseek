import Mathlib
import Submission.Work.RiemLib.Work.OddBound.LiftKit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-!
# The length toolkit for a `C¹` curve on `[0,S]`

For a curve `h : ℝ → M` that is `C¹` on the closed interval `[0,S]`, this file collects the three
elementary facts about its Riemannian speed `curveSpeed h` and its length `curveLength h` that are
used in the long-homotopy argument:

* `curveSpeed h` is interval-integrable on every subinterval `[a,b] ⊆ [0,S]`;
* `a ↦ curveLength h 0 a` is monotone on `[0,S]`;
* the manifold path length `pathELength I h a b` (the Lebesgue integral of the extended norm of
  the derivative) is `ENNReal.ofReal (curveLength h a b)`.

The proof is a little more delicate than one might expect, because `curveSpeed` is defined through
`mfderiv` (the *unrestricted* derivative), whose junk value `0` may occur at the two endpoints
`0` and `S` of the interval: the hypothesis `hc` only bounds `h` on the closed interval.  The
workaround is to compare `curveSpeed h` with the continuous "within-interval" speed

`g t = √⟪(mfderivWithin 𝓘(ℝ) I h (Icc 0 S) t) 1, (mfderivWithin 𝓘(ℝ) I h (Icc 0 S) t) 1⟫`,

which is continuous on `Icc 0 S` by `ContMDiffOn.continuousOn_tangentMapWithin` (the tangent map of
a `C¹` function is continuous) composed with the constant unit section, using continuity of the
metric along continuous sections (`ContinuousOn.inner_bundle`).  The two functions agree off the
two endpoints, hence almost everywhere on every `[a,b] ⊆ [0,S]`.

## Main result

* `curveLength_toolkit`.
-/

/-- **The length toolkit for a `C¹` curve on `[0,S]`.**  For `h : ℝ → M` of class `C¹` on
`Icc 0 S`: the speed is interval-integrable on subintervals, the length is monotone in the upper
endpoint, and the manifold path length agrees with the (real) length. -/
theorem curveLength_toolkit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E]
    {h : ℝ → M} {S : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) :
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S →
        IntervalIntegrable (curveSpeed (I := I) h) MeasureTheory.volume a b) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S →
        curveLength (I := I) h 0 a ≤ curveLength (I := I) h 0 b) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S →
        Manifold.pathELength I h a b = ENNReal.ofReal (curveLength (I := I) h a b)) := by
  rcases le_or_gt S 0 with hSle | hS
  · -- Degenerate case `S ≤ 0`: the three conditions force `a = b = 0`.
    have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S → a = 0 ∧ b = 0 := by
      intro a b ha hab hbS
      exact ⟨le_antisymm (le_trans hab (le_trans hbS hSle)) ha,
             le_antisymm (le_trans hbS hSle) (le_trans ha hab)⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b ha hab hbS
      obtain ⟨rfl, rfl⟩ := key a b ha hab hbS
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl]
      simp
    · intro a b ha hab hbS
      obtain ⟨rfl, rfl⟩ := key a b ha hab hbS
      exact le_rfl
    · intro a b ha hab hbS
      obtain ⟨rfl, rfl⟩ := key a b ha hab hbS
      rw [Manifold.pathELength_self, Submission.Length.curveLength_self]
      simp
  · -- Main case `0 < S`.
    -- The Riemannian bundle is in particular a *continuous* Riemannian bundle.
    haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
      obtain ⟨Φ, hΦsm, hΦ⟩ :=
        (inferInstance : IsContMDiffRiemannianBundle I ∞ E
          (fun x : M ↦ TangentSpace I x)).exists_contMDiff
      exact ⟨Φ, hΦsm.continuous, hΦ⟩
    set s : Set ℝ := Set.Icc (0 : ℝ) S with hsdef
    have hs_umd : UniqueMDiff[s] := UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc hS)
    -- The tangent map of `h` within `[0,S]` is continuous.
    have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I h s) (Bundle.TotalSpace.proj ⁻¹' s) :=
      hc.continuousOn_tangentMapWithin le_rfl hs_umd
    -- The constant unit section of the tangent bundle of the model space `ℝ`.
    have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
        TangentBundle 𝓘(ℝ) ℝ)) s :=
      ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
        (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
    have hcomp : ContinuousOn (fun t : ℝ =>
        (⟨h t, (mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ)⟩ : TangentBundle I M)) s :=
      htan.comp hκ (fun t ht => by simpa using ht)
    -- The "within-interval" speed.
    set g : ℝ → ℝ := fun t => Real.sqrt
      (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))) with hgdef
    have hgcont : ContinuousOn g s := (ContinuousOn.inner_bundle (b := h) hcomp hcomp).sqrt
    -- It agrees with `curveSpeed` on the interior of `[0,S]`.
    have hgspeed : ∀ t ∈ Set.Ioo (0 : ℝ) S, g t = curveSpeed (I := I) h t := by
      intro t ht
      have hmem : s ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      show Real.sqrt (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
        ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))) = curveSpeed (I := I) h t
      rw [mfderivWithin_of_mem_nhds hmem, Submission.Length.curveSpeed_def,
        Submission.Geodesic.curveVelocity_apply]
    -- Hence the two functions are almost everywhere equal on any `[a,b] ⊆ [0,S]`.
    have hae : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S →
        curveSpeed (I := I) h =ᵐ[volume.restrict (Set.Icc a b)] g := by
      intro a b ha hab hbS
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Icc,
        MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null (t := ({0} ∪ {S} : Set ℝ)) ?_ ?_
      · intro t ht
        rw [Set.mem_ofPred_eq] at ht
        by_contra hcon
        simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hcon
        have htab : t ∈ Set.Icc a b := by
          by_contra hmem
          exact ht (fun h' => absurd h' hmem)
        have hne : curveSpeed (I := I) h t ≠ g t := fun heq => ht (fun _ => heq)
        exact hne (hgspeed t ⟨lt_of_le_of_ne (le_trans ha htab.1) (Ne.symm hcon.1),
          lt_of_le_of_ne (le_trans htab.2 hbS) hcon.2⟩).symm
      · rw [measure_union_null_iff]
        exact ⟨measure_singleton 0, measure_singleton S⟩
    have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ S →
        IntervalIntegrable (curveSpeed (I := I) h) volume a b := by
      intro a b ha hab hbS
      have hsub : Set.Icc a b ⊆ s := Icc_subset_Icc ha hbS
      have hintg : IntegrableOn g (Set.Icc a b) volume := (hgcont.mono hsub).integrableOn_Icc
      have hintcs : IntegrableOn (curveSpeed (I := I) h) (Set.Icc a b) volume :=
        hintg.congr_fun_ae (hae a b ha hab hbS).symm
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (hintcs.mono_set Set.Ioc_subset_Icc_self)
    refine ⟨hint, ?_, ?_⟩
    · -- Monotonicity of the length.
      intro a b ha hab hbS
      have h1 := hint 0 a le_rfl ha (le_trans hab hbS)
      have h2 := hint a b ha hab hbS
      have hadd := Submission.Length.curveLength_add_of_integrable (I := I) h h1 h2
      have hnn : 0 ≤ curveLength (I := I) h a b :=
        Submission.Length.curveLength_nonneg (I := I) h hab
      linarith
    · -- The path length is the integral of the speed.
      intro a b ha hab hbS
      have hsub : Set.Icc a b ⊆ s := Icc_subset_Icc ha hbS
      have hintg : IntegrableOn g (Set.Icc a b) volume := (hgcont.mono hsub).integrableOn_Icc
      have hintcs : IntegrableOn (curveSpeed (I := I) h) (Set.Icc a b) volume :=
        hintg.congr_fun_ae (hae a b ha hab hbS).symm
      rw [Submission.Length.curveLength_def]
      refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg (I := I)
        (γ := h) (a := a) (b := b) (f := fun t => curveSpeed (I := I) h t) hab
        hintcs (fun t _ => Submission.Length.curveSpeed_nonneg (I := I) h t) ?_
      intro t ht
      show ‖curveVelocity (I := I) h t‖ₑ = ENNReal.ofReal (curveSpeed (I := I) h t)
      rw [Submission.Minimal.enorm_eq_ofReal_norm, Submission.GeodesicSpeed.curveSpeed_eq_norm]

end Work.OddBound.longHomotopy
