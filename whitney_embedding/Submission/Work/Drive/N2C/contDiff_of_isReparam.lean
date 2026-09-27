import Mathlib

/-!
# Smoothness of a reparametrisation of a smooth immersed curve in a surface

If `α β : ℝ → M` are `C^∞` immersions into a smooth surface `M` and `β = α ∘ h` for a continuous
`h : ℝ → ℝ`, then `h` is `C^∞` and has nowhere vanishing derivative.  This is the elementary
"reparametrisation of an immersed arc is smooth" step used in the routing arguments.

The proof is the classical one: at a point `x`, let `p := β x = α (h x)` and put
`F := extChartAt I p ∘ β`, `G := extChartAt I p ∘ α`.  Then `F = G ∘ h` globally.  Since `α` is
an immersion, `fderiv ℝ G (h x) ≠ 0`, so some component of `G` is a local diffeomorphism near
`h x`; a smooth local inverse of it (produced by the inverse function theorem in dimension one)
composes with `F` to give `h` near `x`.  Finally `fderiv ℝ F x ≠ 0` and the chain rule force
`deriv h x ≠ 0`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

/-- **Local smooth inverse.**  A `C^∞` function `g : ℝ → ℝ` with `deriv g t ≠ 0` admits, near
`g t`, a `C^∞` left inverse of `g` (a function `G` with `G (g s) = s` for `s` near `t`). -/
lemma contDiffAt_localInverse_exists {g : ℝ → ℝ} {t : ℝ}
    (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g t) (hg' : deriv g t ≠ 0) :
    ∃ G : ℝ → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (g t) ∧ G (g t) = t ∧
      ∀ᶠ s in 𝓝 t, G (g s) = s := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv g t) hg')
  have hsta : HasStrictFDerivAt g (e : ℝ →L[ℝ] ℝ) t :=
    (hg.hasStrictDerivAt hn).hasStrictFDerivAt_equiv hg'
  have hfa : HasFDerivAt g (e : ℝ →L[ℝ] ℝ) t := hsta.hasFDerivAt
  let Φ := hg.toOpenPartialHomeomorph g hfa hn
  refine ⟨hg.localInverse hfa hn, hg.to_localInverse hfa hn,
    hg.localInverse_apply_image hfa hn, ?_⟩
  change ∀ᶠ s in 𝓝 t, Φ.symm (g s) = s
  exact Φ.eventually_left_inverse (hg.mem_toOpenPartialHomeomorph_source hfa hn)

/-- **The Euclidean reduction.**  Let `G F : ℝ → E` be `C^∞` at `h x` resp. `x`, with
`F = G ∘ h` near `x`, and suppose the derivatives of `G` at `h x` and of `F` at `x` are non-zero.
Then `h` is `C^∞` at `x` with `deriv h x ≠ 0`.  (The proof only uses one scalar component of `G`,
produced by pairing with `deriv G (h x)` in the inner product.) -/
lemma contDiffAt_of_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G F : ℝ → E} {h : ℝ → ℝ} {x : ℝ}
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (h x))
    (hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F x)
    (hh : ContinuousAt h x)
    (hG' : fderiv ℝ G (h x) ≠ 0) (hF' : fderiv ℝ F x ≠ 0)
    (heq : F =ᶠ[𝓝 x] (G ∘ h)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x ∧ deriv h x ≠ 0 := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hv : deriv G (h x) ≠ 0 := by
    intro h0
    exact hG' (ContinuousLinearMap.ext_ring (by simp [h0]))
  -- the scalar observation `t ↦ ⟪G t, deriv G (h x)⟫`
  let π : E →L[ℝ] ℝ := innerSL ℝ (deriv G (h x))
  have hπ : π (deriv G (h x)) ≠ 0 := by
    simp only [π, innerSL_apply_apply]
    exact inner_self_ne_zero.mpr hv
  have hdG : HasFDerivAt G (fderiv ℝ G (h x)) (h x) := (hG.differentiableAt hn).hasFDerivAt
  have hcomp' : HasFDerivAt (π ∘ G) (π.comp (fderiv ℝ G (h x))) (h x) :=
    (ContinuousLinearMap.hasFDerivAt π).comp (h x) hdG
  have hderivg : deriv (π ∘ G) (h x) = π (deriv G (h x)) := by
    simpa [ContinuousLinearMap.comp_apply] using hcomp'.hasDerivAt.deriv
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (π ∘ G) (h x) :=
    (ContinuousLinearMap.contDiff π).contDiffAt.comp (h x) hG
  obtain ⟨Γ, hΓ, _hΓ0, hΓinv⟩ := contDiffAt_localInverse_exists hg (by rw [hderivg]; exact hπ)
  have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (π ∘ F) x :=
    (ContinuousLinearMap.contDiff π).contDiffAt.comp x hF
  have hfeq : (π ∘ F) =ᶠ[𝓝 x] ((π ∘ G) ∘ h) :=
    heq.mono (fun t ht => by simp only [Function.comp_apply, ht])
  have hfx : (π ∘ F) x = (π ∘ G) (h x) := by
    have := heq.self_of_nhds; simpa [Function.comp_apply] using congrArg π this
  have hΓ2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ ((π ∘ F) x) := hfx.symm ▸ hΓ
  have hΓ' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Γ ∘ (π ∘ F)) x :=
    ContDiffAt.comp x hΓ2 hf
  -- `h` agrees with the smooth function `Γ ∘ π ∘ F` near `x`
  have hEq : h =ᶠ[𝓝 x] (Γ ∘ (π ∘ F)) := by
    filter_upwards [hh.eventually hΓinv, hfeq] with s hs hfs
    simp only [Function.comp_apply] at hs hfs
    show h s = Γ (π (F s))
    have : Γ (π (F s)) = h s := by rw [hfs, hs]
    exact this.symm
  have hhc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x :=
    ContDiffAt.congr_of_eventuallyEq hΓ' hEq
  refine ⟨hhc, ?_⟩
  -- the derivative is non-zero by the chain rule and `fderiv ℝ F x ≠ 0`
  intro h0
  apply hF'
  have hdh : fderiv ℝ h x = 0 := ContinuousLinearMap.ext_ring (by simp [h0])
  rw [heq.fderiv_eq, fderiv_comp x (hG.differentiableAt hn) (hhc.differentiableAt hn), hdh,
    ContinuousLinearMap.comp_zero]

/-- The derivative at `t` of the chart at `f t` composed with an immersive `C^∞` curve `f` is
non-zero. -/
lemma fderiv_extChartAt_comp_ne_zero_aligned {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : ℝ → M}
    (hsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) f t ≠ 0) (t : ℝ) :
    fderiv ℝ (fun s => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t) (f s))
      t ≠ 0 := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcsrc : f t ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (f t)).source := mem_chart_source _ _
  have hpsrc : f t ∈ (extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t)).source := by
    rw [extChartAt_source]; exact hcsrc
  have he : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t)) (f t) :=
    contMDiffAt_extChartAt' hcsrc
  have he_md := he.mdifferentiableAt hn
  have hf_md : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) f t := (hsm.contMDiffAt).mdifferentiableAt hn
  have hinj : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t)) (f t)) :=
    (isInvertible_mfderiv_extChartAt hpsrc).injective
  rw [← mfderiv_eq_fderiv]
  intro h0
  have h0' : mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t)) ∘ f) t = 0 := h0
  apply himm t
  apply ContinuousLinearMap.ext
  intro v
  rw [zero_apply]
  refine hinj ?_
  have h1 := mfderiv_comp_apply (f := f)
      (g := extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (f t))
      (x := t) he_md hf_md v
  rw [← h1, h0', zero_apply, map_zero]

/-- The chart can be centred at any point `p` with `f t = p`. -/
lemma fderiv_extChartAt_comp_ne_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : ℝ → M}
    (hsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) f t ≠ 0)
    {p : M} {t : ℝ} (hp : f t = p) :
    fderiv ℝ (fun s => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) p (f s))
      t ≠ 0 := by
  rw [← hp]
  exact fderiv_extChartAt_comp_ne_zero_aligned hsm himm t

theorem contDiff_of_isReparam {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {α β : ℝ → M}
    (hαsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hβsm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hαimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) α x ≠ 0)
    (hβimm : ∀ x : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) β x ≠ 0)
    {h : ℝ → ℝ} (hcont : Continuous h) (heq : ∀ x : ℝ, β x = α (h x)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ ∀ x : ℝ, deriv h x ≠ 0 := by
  have hkey : ∀ x : ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h x ∧ deriv h x ≠ 0 := by
    intro x
    set p : M := β x with hp
    have hpα : p = α (h x) := heq x
    let e : M → EuclideanSpace ℝ (Fin 2) :=
      extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) p
    have hcsrc : p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source := mem_chart_source _ _
    have he : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) e p :=
      contMDiffAt_extChartAt' hcsrc
    have hGsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ∘ α) (h x) :=
      (he.comp_of_eq (hαsm.contMDiffAt) hpα.symm).contDiffAt
    have hFsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ∘ β) x :=
      (he.comp_of_eq (hβsm.contMDiffAt) hp.symm).contDiffAt
    have hG' : fderiv ℝ (e ∘ α) (h x) ≠ 0 := fderiv_extChartAt_comp_ne_zero hαsm hαimm hpα.symm
    have hF' : fderiv ℝ (e ∘ β) x ≠ 0 := fderiv_extChartAt_comp_ne_zero hβsm hβimm hp.symm
    have heq' : (e ∘ β) =ᶠ[𝓝 x] ((e ∘ α) ∘ h) :=
      Filter.Eventually.of_forall (fun t => by simp [Function.comp_apply, heq t])
    exact contDiffAt_of_eq_comp hGsm hFsm hcont.continuousAt hG' hF' heq'
  exact ⟨(contDiff_iff_contDiffAt.mpr (fun x => (hkey x).1)), fun x => (hkey x).2⟩

end Work.Drive.N2C
