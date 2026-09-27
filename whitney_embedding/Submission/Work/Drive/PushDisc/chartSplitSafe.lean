import Mathlib
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Injectivity of the derivative of the chart split of the Whitney-move coordinate map

The target of this file is the linear-algebraic step of the *chart position* reduction of the
signed push: if `f : M → ℝ^{2n}` (`n = k + 1`) is an immersion, `Φ` is a diffeomorphism of
`ℝ^{2n}` onto the model space `Mdl k = ℝ × ℝ × E^k × E^k` (with inverse `Θ`), and `c` is a chart of
`M` around the point whose coordinate is `splitE k p`, then the map

    q ↦ Φ (f (c.symm (splitE k q)))

has injective Fréchet derivative at `p`.

The content is the chain rule plus the three invertibility facts:

* `fderiv ℝ Φ (Φ⁻¹ x)` is injective because `Θ ∘ Φ = id` (`inj_fderiv_of_leftInverse`);
* the derivative of the chart representation `v ↦ f (c.symm v)` is `mfderiv f (c.symm v₀)` composed
  with the derivative of `c.symm`, which is invertible with inverse the derivative of `c`
  (`injective_mfderiv_chartSymm`, from the two chain rules for `c ∘ c.symm` and `c.symm ∘ c`);
* `splitE k` is a linear equivalence, hence injective.

Note the pervasive use of `set_option backward.isDefEq.respectTransparency false`: the tangent
space instances of the model with corners are not syntactically the model space, so the identity of
`ContinuousLinearMap`s living on `TangentSpace I x` and on the model space is only visible at full
transparency.
-/

/-!
# `injective_fderiv_chartSplit`, with the auxiliary linear map renamed

A copy of the workspace's `injective_fderiv_chartSplit.lean` in which the auxiliary definition
`splitECLM` is renamed `lwSplitECLM`, so that the module can be imported together with the older
`firstSheet_xyJet_signCoherence.lean` (which declares its own `splitECLM`).  The mathematics is
unchanged.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology

/-- The splitting `ℝ × E^k → E^{k+1}` of `splitE` as a continuous linear map. -/
noncomputable def lwSplitECLM (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (splitE k).toLinearMap.toContinuousLinearMap

lemma lwSplitECLM_apply (k : ℕ) (q : ℝ × EuclideanSpace ℝ (Fin k)) :
    lwSplitECLM k q = splitE k q := rfl

lemma injective_lwSplitECLM (k : ℕ) : Function.Injective (lwSplitECLM k) := by
  intro a b hab
  have hab' : splitE k a = splitE k b := by
    rw [← lwSplitECLM_apply k a, ← lwSplitECLM_apply k b]
    exact hab
  exact (splitE k).injective hab'

/-- **A map with a smooth left inverse has injective derivative.**  If `Θ ∘ Φ = id` then
`fderiv ℝ Θ (Φ x) ∘ fderiv ℝ Φ x = fderiv ℝ id x`, so `fderiv ℝ Φ x` is injective. -/
lemma inj_fderiv_of_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E → F} {Θ : F → E} (h : ∀ y, Θ (Φ y) = y) (x : E)
    (hΦ : DifferentiableAt ℝ Φ x) (hΘ : DifferentiableAt ℝ Θ (Φ x)) :
    Function.Injective (fderiv ℝ Φ x) := by
  have hcomp : (fun y => Θ (Φ y)) = (id : E → E) := funext h
  have hfd : (fderiv ℝ Θ (Φ x)).comp (fderiv ℝ Φ x) = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (fun y => Θ (Φ y))
        ((fderiv ℝ Θ (Φ x)).comp (fderiv ℝ Φ x)) x :=
      hΘ.hasFDerivAt.comp x hΦ.hasFDerivAt
    rw [← h1.fderiv, hcomp, fderiv_id]
  have key : ∀ u : E, (fderiv ℝ Θ (Φ x)) ((fderiv ℝ Φ x) u) = u := by
    intro u
    have h2 := congrArg (fun (L : E →L[ℝ] E) => L u) hfd
    simpa using h2
  intro a b hab
  have h4 : (fderiv ℝ Θ (Φ x)) ((fderiv ℝ Φ x) (a - b)) = a - b := key (a - b)
  rw [map_sub, hab, sub_self, map_zero] at h4
  exact sub_eq_zero.mp h4.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The derivative of the chart representation of `f`.**  For a chart-like map `c` of the smooth
structure, the Fréchet derivative of `v ↦ f (c.symm v)` at `v₀ ∈ c.target` is the manifold
derivative of `f` at `c.symm v₀` composed with the manifold derivative of `c.symm`. -/
lemma hasFDerivAt_chartRep {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    {v₀ : EuclideanSpace ℝ (Fin (k + 1))} (hv₀ : v₀ ∈ c.target) :
    HasFDerivAt (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v))
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f (c.symm v₀)).comp
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀)) v₀ := by
  have hy₀src : c.symm v₀ ∈ c.source := c.map_target hv₀
  have htgt_nhds : c.target ∈ 𝓝 v₀ := c.open_target.mem_nhds hv₀
  have hmd_c : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) c (c.symm v₀) :=
    (hc.1.mdifferentiableOn (by simp)).mdifferentiableAt (c.open_source.mem_nhds hy₀src)
  have hmd_cs : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀ :=
    (hc.2.mdifferentiableOn (by simp)).mdifferentiableAt htgt_nhds
  have hmd_f : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1))))) f (c.symm v₀) :=
    (hf (c.symm v₀)).mdifferentiableAt (by simp)
  have hmd_comp : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) v₀ :=
    hmd_f.comp v₀ hmd_cs
  have hmf_comp : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) v₀ =
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f (c.symm v₀)).comp
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) :=
    mfderiv_comp v₀ hmd_f hmd_cs
  have hdiff : DifferentiableAt ℝ (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) v₀ :=
    mdifferentiableAt_iff_differentiableAt.mp hmd_comp
  have hA : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) v₀ =
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f (c.symm v₀)).comp
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) := by
    rw [← mfderiv_eq_fderiv
      (f := fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) (x := v₀), hmf_comp]
  rw [← hA]
  exact hdiff.hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
/-- **The derivative of the inverse chart is injective.**  `c.symm` and `c` are mutually inverse on
their (open) source and target, and both are smooth there; the two chain rules give
`mfderiv c (c.symm v₀) ∘ mfderiv c.symm v₀ = id`. -/
lemma injective_mfderiv_chartSymm {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    {v₀ : EuclideanSpace ℝ (Fin (k + 1))} (hv₀ : v₀ ∈ c.target) :
    Function.Injective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) := by
  have hy₀src : c.symm v₀ ∈ c.source := c.map_target hv₀
  have htgt_nhds : c.target ∈ 𝓝 v₀ := c.open_target.mem_nhds hv₀
  have hmd_c : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) c (c.symm v₀) :=
    (hc.1.mdifferentiableOn (by simp)).mdifferentiableAt (c.open_source.mem_nhds hy₀src)
  have hmd_cs : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀ :=
    (hc.2.mdifferentiableOn (by simp)).mdifferentiableAt htgt_nhds
  have hchain : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (fun v : EuclideanSpace ℝ (Fin (k + 1)) => c (c.symm v)) v₀ =
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) c (c.symm v₀)).comp
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) :=
    mfderiv_comp v₀ hmd_c hmd_cs
  have heq : (fun v : EuclideanSpace ℝ (Fin (k + 1)) => c (c.symm v))
      =ᶠ[𝓝 v₀] (id : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))) := by
    filter_upwards [htgt_nhds] with v hv
    exact c.right_inv hv
  have hid : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (fun v : EuclideanSpace ℝ (Fin (k + 1)) => c (c.symm v)) v₀ =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
    rw [Filter.EventuallyEq.mfderiv_eq_v433 heq, mfderiv_id]
    rfl
  have hcomm : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) c (c.symm v₀)).comp
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
    rw [← hchain, hid]
  have hpt : ∀ u : EuclideanSpace ℝ (Fin (k + 1)),
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) c (c.symm v₀)
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀ u) = u := by
    intro u
    have h := congrArg (fun (L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (k + 1))) => L u) hcomm
    exact h
  intro a b hab
  have hsub : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀ (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hfinal := hpt (a - b)
  rw [hsub, map_zero] at hfinal
  exact sub_eq_zero.mp hfinal.symm

set_option backward.isDefEq.respectTransparency false in
theorem injective_fderiv_chartSplitSafe {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    {Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k}
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    {Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    {p : ℝ × EuclideanSpace ℝ (Fin k)} (hp : Work.Drive.PushDisc.splitE k p ∈ c.target) :
    Function.Injective (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
      Φ (f (c.symm (Work.Drive.PushDisc.splitE k q)))) p) := by
  classical
  set v₀ : EuclideanSpace ℝ (Fin (k + 1)) := splitE k p with hv₀def
  set y₀ : M := c.symm v₀ with hy₀def
  have hv₀ : v₀ ∈ c.target := hp
  -- (I) the ambient chart `Φ` has injective derivative (its inverse `Θ` is a left inverse)
  have hinjΦ : Function.Injective (fderiv ℝ Φ (f y₀)) :=
    inj_fderiv_of_leftInverse (Φ := Φ) (Θ := Θ) hΘΦ (f y₀)
      (hΦsm.differentiable (by simp)).differentiableAt
      (hΘsm.differentiable (by simp)).differentiableAt
  -- (II) the chart representation of `f` has injective derivative
  set A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y₀).comp
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) with hAdef
  have hAinj : Function.Injective A := by
    intro u v huv
    have h1 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y₀)
          ((mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) u) =
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y₀)
          ((mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm v₀) v) :=
      huv
    exact (injective_mfderiv_chartSymm (k := k) c hc hv₀) ((himm y₀) h1)
  have hchA : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm v)) A v₀ :=
    hasFDerivAt_chartRep (k := k) hf c hc hv₀
  -- (III) the splitting
  have hsplit : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin k) => splitE k q)
      (lwSplitECLM k) p := by
    have h0 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin k) => lwSplitECLM k q)
        (lwSplitECLM k) p := (lwSplitECLM k).hasFDerivAt
    have h1 : (fun q : ℝ × EuclideanSpace ℝ (Fin k) => splitE k q)
        = fun q : ℝ × EuclideanSpace ℝ (Fin k) => lwSplitECLM k q := by
      funext q
      exact lwSplitECLM_apply k q
    rw [h1]
    exact h0
  have hInner : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
      f (c.symm (splitE k q))) (A.comp (lwSplitECLM k)) p :=
    hchA.comp p hsplit
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (f y₀)) (f y₀) :=
    (hΦsm.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hAll : HasFDerivAt (Φ ∘ (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
      f (c.symm (splitE k q)))) ((fderiv ℝ Φ (f y₀)).comp (A.comp (lwSplitECLM k))) p :=
    hΦd.comp p hInner
  have hderiv : fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
      Φ (f (c.symm (splitE k q)))) p = (fderiv ℝ Φ (f y₀)).comp (A.comp (lwSplitECLM k)) := by
    have hfun : (fun q : ℝ × EuclideanSpace ℝ (Fin k) => Φ (f (c.symm (splitE k q))))
        = Φ ∘ (fun q : ℝ × EuclideanSpace ℝ (Fin k) => f (c.symm (splitE k q))) := rfl
    rw [hfun, hAll.fderiv]
  rw [hderiv]
  intro q₁ q₂ hq
  simp only [ContinuousLinearMap.comp_apply] at hq
  exact injective_lwSplitECLM k (hAinj (hinjΦ hq))

end Work.Drive.PushDisc
