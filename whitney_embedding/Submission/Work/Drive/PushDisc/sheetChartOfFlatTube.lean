import Mathlib
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology
open Set Metric

/-- An injective composite of continuous linear maps is injective in its first factor. -/
theorem injective_of_comp_injective {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommMonoid Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [AddCommMonoid Z] [Module 𝕜 Z] [TopologicalSpace Z]
    (D : X →L[𝕜] Y) (E : Y →L[𝕜] Z) (h : Function.Injective (E.comp D)) :
    Function.Injective D := by
  intro u v huv
  exact h (by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, huv])

/-- **The chart of the flat first tube.**

Let `f : M → ℝ^{2n}` be a smooth immersion of an `n`-manifold, `U₁` an open nonempty set on which
`f` is injective, and `Φ` a chart of `ℝ^{2n}` onto the model space `Mdl k = ℝ × ℝ × E^k × E^k`
(`n = k + 1`) with left inverse `Θ` (`Θ ∘ Φ = id`).  If `U₁` is a *flat tube* of the first sheet,
i.e. `Φ (f x) ∈ sheetA = {y = 0, v = 0}` for every `x ∈ U₁`, then the `(x, u)`-coordinates of
`Φ ∘ f` are a chart of `M` on `U₁`: there is `c : OpenPartialHomeomorph M ℝ^{k+1}` with source `U₁`
and `c x = splitE k ((Φ (f x)).1, (Φ (f x)).2.2.1)` for all `x ∈ U₁`.

The mathematical content is that `x ↦ Φ (f x)` lands in the *linear* model plane `sheetA ≅ ℝ^n`
there, so that along `U₁` the immersion `f` factors through the `n`-dimensional projection
`(x, u)` of the ambient chart: `f = (Θ ∘ B') ∘ g` on `U₁` with `B'` the linear embedding
`ℝ^{k+1} → sheetA` realised through `splitE`.  An injective immersion from an `n`-manifold to `ℝ^n`
on an open set is a chart (`Work.Drive.PushDisc.exists_smoothChart_of_injOn_immersion_of_nonempty_source`),
and injectivity of the composite `f|U₁ = (Θ ∘ B') ∘ g|U₁` gives the injectivity of `g|U₁`. -/
theorem sheetChartOfFlatTube {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (hk : n = k + 1)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (U₁ : Set M) (hU₁o : IsOpen U₁) (hU₁ne : U₁.Nonempty) (hU₁inj : Set.InjOn f U₁)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y)
    (hflat : ∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) :
    ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))),
      c.source = U₁ ∧ (∀ x : M, x ∈ U₁ →
        c x = Work.Drive.PushDisc.splitE k ((Φ (f x)).1, (Φ (f x)).2.2.1)) := by
  subst hk
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  -- ## The linear embedding of the model plane `sheetA` into the model space
  let S : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) :=
    ((LinearEquiv.toContinuousLinearEquiv (splitE k)).symm :
      EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)))
  let p1 : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp S
  let p2 : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp S
  let B' : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] Work.Drive.Whitney.Mdl k :=
    ContinuousLinearMap.prod p1
      (ContinuousLinearMap.prod (0 : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ)
        (ContinuousLinearMap.prod p2
          (0 : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k))))
  have hB'val : ∀ w : EuclideanSpace ℝ (Fin (k + 1)),
      B' w = (((splitE k).symm w).1, (0 : ℝ), ((splitE k).symm w).2,
        (0 : EuclideanSpace ℝ (Fin k))) := by
    intro w
    simp [B', p1, p2, S]
  -- ## Injectivity of the chart of the ambient space
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h := congrArg Θ hab
    simpa only [hΘΦ] using h
  -- ## The chart map `(x, u)`
  let g : M → EuclideanSpace ℝ (Fin (k + 1)) :=
    fun z => splitE k ((Φ (f z)).1, (Φ (f z)).2.2.1)
  have hgsm : ContMDiff (MWC (k + 1)) (MWC (k + 1)) hInf g := by
    have h1 : ContMDiff (MWC (k + 1)) (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        hInf (fun z : M => Φ (f z)) := hΦsm.contMDiff.comp hf
    have hc : ContDiff ℝ hInf (fun ξ : Work.Drive.Whitney.Mdl k =>
        ((ξ.1, ξ.2.2.1) : ℝ × EuclideanSpace ℝ (Fin k))) := by fun_prop
    have h3 : ContDiff ℝ hInf (fun ξ : Work.Drive.Whitney.Mdl k =>
        splitE k ((ξ.1, ξ.2.2.1))) :=
      (LinearEquiv.toContinuousLinearEquiv (splitE k)).contDiff.comp hc
    have h2 : ContMDiff (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (MWC (k + 1)) hInf
        (fun ξ : Work.Drive.Whitney.Mdl k => splitE k ((ξ.1, ξ.2.2.1))) := h3.contMDiff
    exact h2.comp h1
  -- ## On the flat tube, `Φ ∘ f` is the image of `(x,u)` under the linear embedding
  have hBg : ∀ z : M, z ∈ U₁ → B' (g z) = Φ (f z) := by
    intro z hz
    have hsymm : (splitE k).symm (g z) = ((Φ (f z)).1, (Φ (f z)).2.2.1) := by
      show (splitE k).symm (splitE k ((Φ (f z)).1, (Φ (f z)).2.2.1)) = _
      rw [LinearEquiv.symm_apply_apply]
    have hfy : (Φ (f z)).2.1 = 0 := (hflat z hz).1
    have hfv : (Φ (f z)).2.2.2 = 0 := (hflat z hz).2
    have hEq : ((Φ (f z)).1, (0 : ℝ), (Φ (f z)).2.2.1,
        (0 : EuclideanSpace ℝ (Fin k))) = Φ (f z) := by
      rw [← hfy, ← hfv]
    calc B' (g z)
        = (((splitE k).symm (g z)).1, (0 : ℝ), ((splitE k).symm (g z)).2,
            (0 : EuclideanSpace ℝ (Fin k))) := hB'val (g z)
      _ = ((Φ (f z)).1, (0 : ℝ), (Φ (f z)).2.2.1, (0 : EuclideanSpace ℝ (Fin k))) := by
            rw [hsymm]
      _ = Φ (f z) := hEq
  -- ## Injectivity
  have hinj : Set.InjOn g U₁ := by
    intro x hx y hy hxy
    refine hU₁inj hx hy (hΦinj ?_)
    rw [← hBg x hx, ← hBg y hy, hxy]
  -- ## The immersion property
  have himmg : ∀ x : M, x ∈ U₁ →
      Function.Injective (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) := by
    intro x hx
    -- the smooth parametrisation of the model plane through `Φ`
    let F : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
      fun w => Θ (B' w)
    have hF : ContDiff ℝ hInf F := by
      have h := hΘsm.comp (ContinuousLinearMap.contDiff B' : ContDiff ℝ hInf (⇑B'))
      simpa only [F, Function.comp_def] using h
    -- on `U₁`, `f = F ∘ g`
    have hev : (fun z : M => F (g z)) =ᶠ[𝓝 x] f := by
      filter_upwards [hU₁o.mem_nhds hx] with z hz
      show Θ (B' (g z)) = f z
      rw [hBg z hz, hΘΦ]
    have hchain : mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) (fun z : M => F (g z)) x
        = (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)).comp
          (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) :=
      mfderiv_comp x (hF.contMDiff.mdifferentiableAt hne) (hgsm.mdifferentiableAt hne)
    have hmf : mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) f x
        = (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)).comp
          (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x) := by
      rw [← hev.mfderiv_eq_v433]
      exact hchain
    -- injectivity of the composite gives injectivity of `mfderiv g x`
    exact injective_of_comp_injective (mfderiv (MWC (k + 1)) (MWC (k + 1)) g x)
      (mfderiv (MWC (k + 1)) (MWC (2 * (k + 1))) F (g x)) (by rw [← hmf]; exact himm x)
  -- ## the chart
  obtain ⟨c, hcsrc, hceq, -⟩ :=
    exists_smoothChart_of_injOn_immersion_of_nonempty_source g U₁ hU₁o hU₁ne hgsm hinj himmg
  exact ⟨c, hcsrc, fun x hx => hceq x hx⟩

end Work.Drive.PushDisc
