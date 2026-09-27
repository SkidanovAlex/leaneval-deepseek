import Mathlib
import Submission.Work.Drive.PushDisc.asymSignDefs
import Submission.Work.Drive.PushDisc.asymSignTransport

/-!
# Sign coherence of the `(x,u)`-jet of the first sheet along an arc

Let `M` be a smooth `(k+1)`-manifold, `f : M → ℝ^{2(k+1)}` a smooth immersion, `Φ : ℝ^{2(k+1)} → Mdl k`
a model chart (with inverse `Θ`) that flattens the first sheet `f '' c.source` into the plane
`{y = 0, v = 0}`, and `c` a smooth chart of `M`.  The `(x,u)`-jet of `f` in the model coordinates is

  `t ↦ (x, u) = xyProj (Φ (f (c.symm (splitE t))))`,

a map `ℝ × ℝ^k → ℝ × ℝ^k`.  This file proves that its Jacobian determinant has the *same sign* at
the two ends of an arc `γ` in `M` (both ends read through the *same* chart `c`).

Since the map is an immersion of an open set of `ℝ^{k+1}` into itself (it is a composite of the
immersion `f`, the diffeomorphism `Φ` and the chart), its Jacobian determinant is nowhere zero on
the chart's target; the determinant is continuous, so along the connected curve `c ∘ γ` the sign is
constant.

The main mathematical input is that the flattened first sheet is a graph over its `(x,u)`-shadow:
`xyProj` restricts to an isomorphism from the plane `{y = 0, v = 0}` onto `ℝ × ℝ^k`, so the
`(x,u)`-projection of the derivative of `Φ ∘ f` is still injective.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The `(x,u)`-projection of the model space and the flattened first sheet -/

/-- The projection `(x, y, u, v) ↦ (x, u)` of the model space `Mdl k`. -/
noncomputable def xyProj (k : ℕ) :
    Work.Drive.Whitney.Mdl k →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).prod
    ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).comp
      ((ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)))))

@[simp] theorem xyProj_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    xyProj k ξ = (ξ.1, ξ.2.2.1) := rfl

/-- The inclusion `(x, u) ↦ (x, 0, u, 0)` of the plane `{y = 0, v = 0}` of the model space. -/
noncomputable def incCLM (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] Work.Drive.Whitney.Mdl k :=
  (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).prod
    ((0 : (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] ℝ).prod
      (((ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).prod
        (0 : (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin k)))))

@[simp] theorem incCLM_apply (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    incCLM k p = (p.1, 0, p.2, 0) := rfl

/-- `xyProj` is a left inverse of the inclusion of the flattened first sheet. -/
theorem xyProj_incCLM (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    xyProj k (incCLM k p) = p := rfl

/-- On the plane `{y = 0, v = 0}` the inclusion is a right inverse of `xyProj`. -/
theorem incCLM_xyProj (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k)
    (h1 : ξ.2.1 = 0) (h2 : ξ.2.2.2 = 0) : incCLM k (xyProj k ξ) = ξ := by
  obtain ⟨x, y, u, v⟩ := ξ
  have h1' : y = 0 := h1
  have h2' : v = 0 := h2
  simp only [xyProj_apply, incCLM_apply, h1', h2']

theorem incCLM_injective (k : ℕ) : Function.Injective (incCLM k) := by
  intro a b h
  have := congrArg (xyProj k) h
  simpa using this

/-! ## The chart expression of the `(x,u)`-jet -/

/-- The chart expression of `Φ ∘ f` in the chart `c`: `u ↦ Φ (f (c.symm u))`. -/
noncomputable def mdlSheet (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))) :
    EuclideanSpace ℝ (Fin (k + 1)) → Work.Drive.Whitney.Mdl k :=
  fun u => Φ (f (c.symm u))

/-- The `(x,u)`-projection of the chart expression of `Φ ∘ f`: `u ↦ (x, u)`. -/
noncomputable def xySheet (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))) :
    EuclideanSpace ℝ (Fin (k + 1)) → (ℝ × EuclideanSpace ℝ (Fin k)) :=
  fun u => xyProj k (mdlSheet k Φ f c u)

/-- The `(x,u)`-jet in the chart `c` read through the splitting `splitE k` of `ℝ × ℝ^k`. -/
noncomputable def xyJet (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))) :
    (ℝ × EuclideanSpace ℝ (Fin k)) → (ℝ × EuclideanSpace ℝ (Fin k)) :=
  fun t => xySheet k Φ f c (splitE k t)

@[simp] theorem mdlSheet_apply (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (u : EuclideanSpace ℝ (Fin (k + 1))) :
    mdlSheet k Φ f c u = Φ (f (c.symm u)) := rfl

@[simp] theorem xySheet_apply (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (u : EuclideanSpace ℝ (Fin (k + 1))) :
    xySheet k Φ f c u = xyProj k (Φ (f (c.symm u))) := rfl

@[simp] theorem xyJet_apply (k : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (t : ℝ × EuclideanSpace ℝ (Fin k)) :
    xyJet k Φ f c t =
      ((Φ (f (c.symm (splitE k t)))).1, (Φ (f (c.symm (splitE k t)))).2.2.1) := rfl

/-- The splitting `splitE k` as a continuous linear map. -/
noncomputable def splitECLM (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearMap.toContinuousLinearMap
    (splitE k : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))

/-- Its inverse as a continuous linear map. -/
noncomputable def splitESymmCLM (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) :=
  LinearMap.toContinuousLinearMap
    ((splitE k).symm : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin k)))

@[simp] theorem splitECLM_apply (k : ℕ) (t : ℝ × EuclideanSpace ℝ (Fin k)) :
    splitECLM k t = splitE k t := rfl

@[simp] theorem splitESymmCLM_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    splitESymmCLM k x = (splitE k).symm x := rfl

theorem splitECLM_injective (k : ℕ) : Function.Injective (splitECLM k) := by
  intro a b h
  exact (splitE k).injective (by simpa using h)

theorem splitECLM_contDiff (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ × EuclideanSpace ℝ (Fin k) => splitE k t) :=
  ContinuousLinearMap.contDiff (splitECLM k)

theorem fderiv_splitE (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    fderiv ℝ (fun t => splitE k t) p = splitECLM k := by
  rw [show (fun t : ℝ × EuclideanSpace ℝ (Fin k) => splitE k t) = ⇑(splitECLM k) from rfl]
  exact (ContinuousLinearMap.hasFDerivAt (splitECLM k) (x := p)).fderiv

/-! ## A determinant test for injectivity -/

theorem det_toLinearMap_ne_zero_of_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E)
    (h : Function.Injective A) : A.toLinearMap.det ≠ 0 := by
  intro h0
  have hker : A.toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0
  rw [LinearMap.ker_eq_bot.mpr h] at hker
  exact hker rfl

/-! ## The chart representation of an immersion has injective derivative -/

/-- The chart representation `u ↦ g (c.symm u)` of a smooth map has injective Fréchet derivative
at `c p` whenever `g` is an immersion at `p`. -/
theorem injective_fderiv_chartRep {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : M → F}
    (hg : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : Work.Whitney.IsSmoothChart c) {p : M} (hp : p ∈ c.source)
    (hinj : Function.Injective
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F) g p)) :
    Function.Injective (fderiv ℝ (fun u => g (c.symm u)) (c p)) := by
  haveI : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1 M :=
    IsManifold.of_le (m := 1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hmd : c.MDifferentiable (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) :=
    ⟨hc.1.mdifferentiableOn hne, hc.2.mdifferentiableOn hne⟩
  have hcs : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F)
      (fun u => g (c.symm u)) (c p) :=
    MDifferentiableAt.comp (c p) (hg.mdifferentiableAt hne)
      ((hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))).mdifferentiableAt hne)
  have hchain := mfderiv_comp p hcs (hmd.mdifferentiableAt hp)
  have heq : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F)
      ((fun u => g (c.symm u)) ∘ c) p =
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F) g p := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [c.open_source.mem_nhds hp] with y hy
    simp only [Function.comp_apply]
    rw [c.left_inv hy]
  have hdec : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, F) g p =
      (fderiv ℝ (fun u => g (c.symm u)) (c p)) ∘SL
        (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) c p) := by
    rw [← heq, hchain, mfderiv_eq_fderiv]
    rfl
  have hsurj : Function.Surjective
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) c p) :=
    (hmd.mfderiv hp).surjective
  intro a b hab
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  refine congrArg (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) c p) (hinj ?_)
  rw [hdec]
  exact hab

/-! ## Smoothness of the `(x,u)`-jet -/

theorem contDiffOn_xySheet {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hf : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xySheet k Φ f c) c.target := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ => xyProj k (Φ ξ)) :=
    (xyProj k).contDiff.contMDiff.comp hΦsm.contMDiff
  have h12 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : M => xyProj k (Φ (f z))) := h1.comp hf
  have h12u : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : M => xyProj k (Φ (f z))) Set.univ := h12.contMDiffOn (s := Set.univ)
  exact (h12u.comp hc.2 (fun u _ => Set.mem_univ _)).contDiffOn

/-! ## Injectivity of the derivative of the `(x,u)`-jet -/

theorem injective_fderiv_xySheet {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ x : M, x ∈ c.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    {u : EuclideanSpace ℝ (Fin (k + 1))} (hu : u ∈ c.target) :
    Function.Injective (fderiv ℝ (xySheet k Φ f c) u) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- `Φ` has injective derivative, being a diffeomorphism with inverse `Θ`
  have hdΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))),
      Function.Injective (fderiv ℝ Φ y) := by
    intro y
    have hcomp_id : (fderiv ℝ Θ (Φ y)).comp (fderiv ℝ Φ y) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))) := by
      have h := fderiv_comp (g := Θ) (f := Φ) y
        ((hΘsm.differentiable (by simp)).differentiableAt)
        ((hΦsm.differentiable (by simp)).differentiableAt)
      rw [show (Θ ∘ Φ) = id from funext hΘΦ, fderiv_id] at h
      exact h.symm
    refine Function.LeftInverse.injective (g := fderiv ℝ Θ (Φ y)) (fun v => ?_)
    have h := congrArg
      (fun (L : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * (k + 1)))) => L v) hcomp_id
    simpa using h
  -- the composite `Φ ∘ f` is an immersion
  have hgsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : M => Φ (f z)) :=
    hΦsm.contMDiff.comp hf
  have hgimm : ∀ x : M, Function.Injective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
      (𝓘(ℝ, Work.Drive.Whitney.Mdl k)) (fun z : M => Φ (f z)) x) := by
    intro x
    have h1 : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1)))))
        (𝓘(ℝ, Work.Drive.Whitney.Mdl k)) Φ (f x) :=
      (hΦsm.contMDiff.contMDiffAt).mdifferentiableAt hne
    have h2 : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1))))) f x :=
      hf.contMDiffAt.mdifferentiableAt hne
    have h3 : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1)))))
        (𝓘(ℝ, Work.Drive.Whitney.Mdl k)) Φ (f x) = fderiv ℝ Φ (f x) := mfderiv_eq_fderiv
    have hev : (fun z : M => Φ (f z)) =ᶠ[nhds x] (Φ ∘ f) := by
      filter_upwards with z
      rfl
    have hchain : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, Work.Drive.Whitney.Mdl k)) (fun z : M => Φ (f z)) x =
        (fderiv ℝ Φ (f x)).comp (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (k + 1))))) f x) := by
      rw [hev.mfderiv_eq, mfderiv_comp x h1 h2, h3]
      rfl
    rw [hchain]
    intro a b hab
    exact himm x ((hdΦ (f x)) hab)
  -- the chart representation of `Φ ∘ f` has injective derivative
  have hx : c.symm u ∈ c.source := c.map_target hu
  have hcu : c (c.symm u) = u := c.right_inv hu
  have hA : Function.Injective (fderiv ℝ (mdlSheet k Φ f c) (c (c.symm u))) :=
    injective_fderiv_chartRep (g := fun z : M => Φ (f z)) hgsm hc hx (hgimm _)
  have hA' : Function.Injective (fderiv ℝ (mdlSheet k Φ f c) u) := by
    rwa [hcu] at hA
  -- on the chart target the sheet lies in the plane `{y = 0, v = 0}`
  have hsheet_range : mdlSheet k Φ f c =ᶠ[nhds u]
      (fun u' => incCLM k (xySheet k Φ f c u')) := by
    filter_upwards [c.open_target.mem_nhds hu] with u' hu'
    obtain ⟨h1, h2⟩ := hsh (c.symm u') (c.map_target hu')
    simp only [mdlSheet_apply, xySheet_apply]
    exact (incCLM_xyProj k _ h1 h2).symm
  have hxycd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xySheet k Φ f c) c.target :=
    contDiffOn_xySheet Φ f c hc hΦsm hf
  have h2diff : DifferentiableAt ℝ (xySheet k Φ f c) u :=
    (hxycd.differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hu)
  have hcomp1 : fderiv ℝ (⇑(incCLM k) ∘ xySheet k Φ f c) u =
      (incCLM k).comp (fderiv ℝ (xySheet k Φ f c) u) := by
    have h := fderiv_comp (g := ⇑(incCLM k)) (f := xySheet k Φ f c) u
      (ContinuousLinearMap.differentiableAt (incCLM k)) h2diff
    rw [(ContinuousLinearMap.hasFDerivAt (incCLM k) (x := xySheet k Φ f c u)).fderiv] at h
    exact h
  have hderiv : fderiv ℝ (mdlSheet k Φ f c) u =
      (incCLM k).comp (fderiv ℝ (xySheet k Φ f c) u) := by
    rw [hsheet_range.fderiv_eq]
    show fderiv ℝ (⇑(incCLM k) ∘ xySheet k Φ f c) u =
      (incCLM k).comp (fderiv ℝ (xySheet k Φ f c) u)
    exact hcomp1
  intro a b hab
  have h1 : (fderiv ℝ (mdlSheet k Φ f c) u) a = (fderiv ℝ (mdlSheet k Φ f c) u) b := by
    rw [hderiv]
    exact congrArg (incCLM k) hab
  exact hA' h1

/-! ## Sign coherence along an interval -/

/-- A continuous nowhere-zero real function on `[0,1]` takes values of the same sign at `0` and
`1`, so their product is positive. -/
theorem mul_pos_of_continuousOn_ne_zero {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≠ 0) : 0 < F 0 * F 1 := by
  have hF0 : F 0 ≠ 0 := hne 0 (by norm_num)
  have hF1 : F 1 ≠ 0 := hne 1 (by norm_num)
  rcases lt_trichotomy (F 0) 0 with h0 | h0 | h0
  · rcases lt_trichotomy (F 1) 0 with h1 | h1 | h1
    · exact mul_pos_of_neg_of_neg h0 h1
    · exact absurd h1 hF1
    · obtain ⟨t, ht, hFt⟩ := (intermediate_value_Icc zero_le_one hF)
        (show (0 : ℝ) ∈ Set.Icc (F 0) (F 1) from ⟨le_of_lt h0, le_of_lt h1⟩)
      exact absurd hFt (hne t ht)
  · exact absurd h0 hF0
  · rcases lt_trichotomy (F 1) 0 with h1 | h1 | h1
    · -- `F 1 < 0 < F 0`: apply the intermediate value theorem to `-F`
      have hneg : ContinuousOn (fun t : ℝ => -F t) (Set.Icc (0 : ℝ) 1) := hF.neg
      obtain ⟨t, ht, hFt⟩ := (intermediate_value_Icc zero_le_one hneg)
        (show (0 : ℝ) ∈ Set.Icc (-F 0) (-F 1) from ⟨by linarith, by linarith⟩)
      exact absurd hFt (fun h => hne t ht (neg_eq_zero.mp h))
    · exact absurd h1 hF1
    · exact mul_pos h0 h1

theorem firstSheet_xyJet_signCoherence {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ x : M, x ∈ c.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    {γ : ℝ → M} (hγ : Continuous γ) (hsrc : γ '' Set.Icc (0 : ℝ) 1 ⊆ c.source)
    {τ₁ τ₂ : ℝ × EuclideanSpace ℝ (Fin k)}
    (hτ₁ : (Work.Drive.PushDisc.splitE k) τ₁ = c (γ 0))
    (hτ₂ : (Work.Drive.PushDisc.splitE k) τ₂ = c (γ 1)) :
    0 < LinearMap.det ((fderiv ℝ (fun t : ℝ × EuclideanSpace ℝ (Fin k) =>
        ((Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).1,
          (Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).2.2.1)) τ₁).toLinearMap)
      * LinearMap.det ((fderiv ℝ (fun t : ℝ × EuclideanSpace ℝ (Fin k) =>
        ((Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).1,
          (Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).2.2.1)) τ₂).toLinearMap) := by
  have hfun : (fun t : ℝ × EuclideanSpace ℝ (Fin k) =>
        ((Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).1,
          (Φ (f (c.symm ((Work.Drive.PushDisc.splitE k) t)))).2.2.1)) = xyJet k Φ f c := rfl
  rw [hfun]
  -- the derivative of the jet is injective at every point above the chart target
  have hinj : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), splitE k p ∈ c.target →
      Function.Injective (fderiv ℝ (xyJet k Φ f c) p) := by
    intro p hp
    have hsheet := injective_fderiv_xySheet (k := k) (M := M) hf himm Φ Θ hΦsm hΘsm hΘΦ hΦΘ
      c hc hsh hp
    have hxycd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xySheet k Φ f c) c.target :=
      contDiffOn_xySheet Φ f c hc hΦsm hf
    have hdiff : DifferentiableAt ℝ (xySheet k Φ f c) (splitE k p) :=
      (hxycd.differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hp)
    have hchain : fderiv ℝ (xyJet k Φ f c) p =
        (fderiv ℝ (xySheet k Φ f c) (splitE k p)).comp (splitECLM k) := by
      rw [show xyJet k Φ f c = xySheet k Φ f c ∘ (fun t => splitE k t) from rfl]
      rw [fderiv_comp p hdiff (ContinuousLinearMap.differentiableAt (splitECLM k))]
      rw [fderiv_splitE k p]
    rw [hchain]
    exact hsheet.comp (splitECLM_injective k)
  -- the curve in `ℝ × ℝ^k` joining `τ₁` and `τ₂`
  set σ : ℝ → ℝ × EuclideanSpace ℝ (Fin k) :=
    fun t => (splitE k).symm (c (γ t)) with hσdef
  have hσ0 : σ 0 = τ₁ := by
    rw [hσdef]
    show (splitE k).symm (c (γ 0)) = τ₁
    rw [← hτ₁, LinearEquiv.symm_apply_apply]
  have hσ1 : σ 1 = τ₂ := by
    rw [hσdef]
    show (splitE k).symm (c (γ 1)) = τ₂
    rw [← hτ₂, LinearEquiv.symm_apply_apply]
  have hσcont : ContinuousOn σ (Set.Icc (0 : ℝ) 1) := by
    rw [hσdef]
    refine Continuous.comp_continuousOn
      (ContinuousLinearMap.continuous (splitESymmCLM k)) ?_
    exact (c.continuousOn).comp hγ.continuousOn
      (fun t ht => hsrc ⟨t, ht, rfl⟩)
  have hσmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, σ t ∈ (splitE k) ⁻¹' c.target := by
    intro t ht
    show splitE k (σ t) ∈ c.target
    rw [hσdef]
    show splitE k ((splitE k).symm (c (γ t))) ∈ c.target
    rw [LinearEquiv.apply_symm_apply]
    exact c.map_source (hsrc ⟨t, ht, rfl⟩)
  -- the determinant is continuous and nowhere zero along the curve
  have hU0 : IsOpen ((splitE k) ⁻¹' c.target) :=
    c.open_target.preimage (ContinuousLinearMap.continuous (splitECLM k))
  have hjetcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xyJet k Φ f c)
      ((splitE k) ⁻¹' c.target) := by
    rw [show xyJet k Φ f c = xySheet k Φ f c ∘ (fun t => splitE k t) from rfl]
    exact (contDiffOn_xySheet Φ f c hc hΦsm hf).comp
      (splitECLM_contDiff k).contDiffOn (fun t ht => ht)
  have hdetcont : ContinuousOn
      (fun p => (fderiv ℝ (xyJet k Φ f c) p).toLinearMap.det) ((splitE k) ⁻¹' c.target) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hjetcd.continuousOn_fderiv_of_isOpen hU0 (by simp))
  have hcontF : ContinuousOn
      (fun t : ℝ => (fderiv ℝ (xyJet k Φ f c) (σ t)).toLinearMap.det) (Set.Icc (0 : ℝ) 1) :=
    hdetcont.comp hσcont (fun t ht => hσmem t ht)
  have hneF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (fderiv ℝ (xyJet k Φ f c) (σ t)).toLinearMap.det ≠ 0 :=
    fun t ht => det_toLinearMap_ne_zero_of_injective _ (hinj (σ t) (hσmem t ht))
  have hmain : 0 < (fderiv ℝ (xyJet k Φ f c) (σ 0)).toLinearMap.det *
      (fderiv ℝ (xyJet k Φ f c) (σ 1)).toLinearMap.det :=
    mul_pos_of_continuousOn_ne_zero hcontF hneF
  rw [hσ0, hσ1] at hmain
  exact hmain

end Work.Drive.PushDisc
