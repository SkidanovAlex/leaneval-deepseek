import Mathlib
import Submission.Work.Drive.N2.morseLemma2

/-!
# The Morse normal form on `ℝ × ℝ`

`Work.Drive.N2.morseLemma2` proves the Morse lemma in the plane for functions on
`EuclideanSpace ℝ (Fin 2)`.  The present file transports it to the product `ℝ × ℝ`, which is the shape
Pardon's argument uses.

The transport is by the linear isometry equivalence `planeEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)`,
`(a, b) ↦ ![a, b]`.  Everything is straightforward except the nondegeneracy hypothesis: the Hessian of
`g ∘ e.symm` at `e p` has to be identified with the Hessian of `g` at `p` conjugated by `e`.  This is the
content of `fderiv_fderiv_comp_right_apply` (and its corollary
`injective_fderiv_fderiv_comp_right`), which say that precomposition with a continuous linear
equivalence transforms second derivatives by conjugation.

The final statement is `morseLemmaProd`.
-/

namespace Work.Drive.Final

noncomputable section

open scoped ContDiff

/-! ## The linear equivalence `(a, b) ↦ ![a, b]` -/

/-- `Fin 2 → ℝ` is `ℝ × ℝ`, and `EuclideanSpace ℝ (Fin 2)` is that with the `ℓ²` norm. -/
def planeEquivRaw :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toContinuousLinearEquiv.symm)

/-- The coordinate identification `(a, b) ↦ ![a, b]` used for the transport. -/
noncomputable def planeEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := by
  exact planeEquivRaw

@[simp] lemma planeEquiv_symm_fst (v : EuclideanSpace ℝ (Fin 2)) :
    (planeEquiv.symm v).1 = v 0 := by
  simp [planeEquiv, planeEquivRaw]

@[simp] lemma planeEquiv_symm_snd (v : EuclideanSpace ℝ (Fin 2)) :
    (planeEquiv.symm v).2 = v 1 := by
  simp [planeEquiv, planeEquivRaw]

/-! ## Second derivatives under precomposition by a linear equivalence -/

/-- Precomposing a smooth function of one real variable's worth of values with a continuous linear
equivalence conjugates the second derivative: `D²(f ∘ e)(x)(v)(w) = D²f(e x)(e v)(e w)`. -/
lemma fderiv_fderiv_comp_right_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : F → ℝ) (e : E ≃L[ℝ] F) (x : E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ ⇑e)) x v w = fderiv ℝ (fderiv ℝ f) (e x) (e v) (e w) := by
  set K : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip (e : E →L[ℝ] F) with hK
  have hKapp : ∀ (u : F →L[ℝ] ℝ) (y : E), K u y = u (e y) := by
    intro u y
    rw [hK]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    rfl
  have hfe : fderiv ℝ (f ∘ ⇑e) = fun y => (fderiv ℝ f (e y)).comp (e : E →L[ℝ] F) := by
    funext y
    exact e.comp_right_fderiv
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (e x)) (e x) :=
    ((hf.contDiffAt.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).differentiableAt
      (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => fderiv ℝ f (e y))
      ((fderiv ℝ (fderiv ℝ f) (e x)).comp (e : E →L[ℝ] F)) x := h1.comp x e.hasFDerivAt
  have h3 : HasFDerivAt (fun y : E => K (fderiv ℝ f (e y)))
      (K.comp ((fderiv ℝ (fderiv ℝ f) (e x)).comp (e : E →L[ℝ] F))) x :=
    (ContinuousLinearMap.hasFDerivAt K).comp x h2
  have hfun2 : (fun y : E => (fderiv ℝ f (e y)).comp (e : E →L[ℝ] F))
      = fun y : E => K (fderiv ℝ f (e y)) := by
    funext y
    ext z
    exact (hKapp (fderiv ℝ f (e y)) z).symm
  rw [hfe, hfun2, h3.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hKapp]
  rfl

/-- Nondegeneracy of a critical point (injectivity of the Hessian) is preserved by precomposing with a
continuous linear equivalence. -/
lemma injective_fderiv_fderiv_comp_right {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : F → ℝ) (e : E ≃L[ℝ] F) (x : E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ f) (e x))) :
    Function.Injective (fderiv ℝ (fderiv ℝ (f ∘ ⇑e)) x) := by
  intro v w hvw
  have hpt := fderiv_fderiv_comp_right_apply f e x hf
  have h1 : fderiv ℝ (fderiv ℝ f) (e x) (e v) = fderiv ℝ (fderiv ℝ f) (e x) (e w) := by
    ext z
    have hz := congrArg (fun (L : E →L[ℝ] ℝ) => L (e.symm z)) hvw
    rw [hpt v (e.symm z), hpt w (e.symm z)] at hz
    simpa using hz
  exact e.injective (hinj h1)

/-! ## The Morse lemma on `ℝ × ℝ` -/

/-- **The Morse lemma on the plane (product coordinates).**  A smooth `g : ℝ × ℝ → ℝ` with a
nondegenerate critical point `p` is, in suitable smooth coordinates `φ` centred at `p` and with smooth
inverse, equal to `g p ± u² ± v²`. -/
theorem morseLemmaProd (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hcrit : fderiv ℝ g p = 0)
    (hnondeg : Function.Injective (fderiv ℝ (fderiv ℝ g) p)) :
    ∃ (φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (s₁ s₂ : ℝ),
      p ∈ φ.source ∧ φ p = 0 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ × ℝ → ℝ × ℝ) φ.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ.symm φ.target ∧
      (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      ∀ y ∈ φ.source, g y = g p + s₁ * (φ y).1 ^ 2 + s₂ * (φ y).2 ^ 2 := by
  -- transport the Morse lemma for `EuclideanSpace ℝ (Fin 2)` along `planeEquiv`
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := g ∘ ⇑(planeEquiv.symm) with hG
  have hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hG]; exact hg.comp planeEquiv.symm.contDiff
  have hGcrit : fderiv ℝ G (planeEquiv p) = 0 := by
    rw [hG, ContinuousLinearEquiv.comp_right_fderiv,
      ContinuousLinearEquiv.symm_apply_apply, hcrit]
    exact ContinuousLinearMap.zero_comp _
  have hGnd : Function.Injective (fderiv ℝ (fderiv ℝ G) (planeEquiv p)) := by
    rw [hG]
    refine injective_fderiv_fderiv_comp_right g planeEquiv.symm (planeEquiv p) hg ?_
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨phi, s1, s2, hp_phi, hphi0, hphi_sm, hphi_symm_sm, hs1, hs2, hform⟩ :=
    Work.Drive.N2.morseLemma2 G (planeEquiv p) hGsm hGcrit hGnd
  -- conjugate the resulting chart back to `ℝ × ℝ`
  set ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    (planeEquiv.toHomeomorph.transOpenPartialHomeomorph phi).transHomeomorph
      planeEquiv.symm.toHomeomorph with hψ
  have hψ_apply : ∀ y, ψ y = planeEquiv.symm (phi (planeEquiv y)) := by
    intro y
    rw [hψ]
    simp only [OpenPartialHomeomorph.transHomeomorph_apply,
      Homeomorph.transOpenPartialHomeomorph_apply,
      Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  have hψ_symm_apply : ∀ z, ψ.symm z = planeEquiv.symm (phi.symm (planeEquiv z)) := by
    intro z
    rw [hψ]
    simp only [OpenPartialHomeomorph.transHomeomorph_symm_apply,
      Homeomorph.transOpenPartialHomeomorph_symm_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, ← ContinuousLinearEquiv.toHomeomorph_symm,
      ContinuousLinearEquiv.symm_symm]
  have hsrc : ψ.source = planeEquiv ⁻¹' phi.source := by
    rw [hψ]
    simp [Homeomorph.transOpenPartialHomeomorph_source,
      OpenPartialHomeomorph.transHomeomorph_source]
  have htgt : ψ.target = planeEquiv ⁻¹' phi.target := by
    rw [hψ]
    simp [Homeomorph.transOpenPartialHomeomorph_target, OpenPartialHomeomorph.transHomeomorph_target,
      ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_symm]
  have hψ_fun : (ψ : ℝ × ℝ → ℝ × ℝ) = fun y => planeEquiv.symm (phi (planeEquiv y)) :=
    funext hψ_apply
  have hψ_symm_fun : (ψ.symm : ℝ × ℝ → ℝ × ℝ)
      = fun z => planeEquiv.symm (phi.symm (planeEquiv z)) := funext hψ_symm_apply
  refine ⟨ψ, s1, s2, ?_, ?_, ?_, ?_, hs1, hs2, ?_⟩
  · rw [hsrc]; exact hp_phi
  · rw [hψ_apply, hphi0]; simp
  · rw [hsrc, hψ_fun]
    exact (planeEquiv.symm.contDiff.contDiffOn).comp
      (hphi_sm.comp planeEquiv.contDiff.contDiffOn (fun y hy => hy))
      (fun _ _ => Set.mem_univ _)
  · rw [htgt, hψ_symm_fun]
    exact (planeEquiv.symm.contDiff.contDiffOn).comp
      (hphi_symm_sm.comp planeEquiv.contDiff.contDiffOn (fun y hy => hy))
      (fun _ _ => Set.mem_univ _)
  · intro y hy
    rw [hsrc] at hy
    have h1 : G (planeEquiv y)
        = G (planeEquiv p) + s1 * (phi (planeEquiv y) 0) ^ 2
          + s2 * (phi (planeEquiv y) 1) ^ 2 := hform (planeEquiv y) hy
    have h2 : G (planeEquiv y) = g y := by rw [hG]; simp
    have h3 : G (planeEquiv p) = g p := by rw [hG]; simp
    rw [hψ_apply, planeEquiv_symm_fst, planeEquiv_symm_snd]
    linarith

end

end Work.Drive.Final
