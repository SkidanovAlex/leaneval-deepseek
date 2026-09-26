import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux

/-!
# `Work.Drive.Mono.exists_faceChart`

A **face (type-2) event chart**: at a parameter-plane point `x₀` at which the level functional
`fderiv (sH ψ a₀ b₀ τ₀)` of the swept level is *proportional* to `fderiv (hFn ψ v)` with nonzero
factor `mu₀` (`htang`), where the level functional is nonzero (`hbne`) and where the constrained
second derivative of the Lagrangian is nondegenerate along the kernel of `fderiv (hFn ψ v)` (`hlag`),
the tangency locus

`{ (τ,q) | ∃ t, fderiv (sH ψ a₀ b₀ τ) q = t • fderiv (hFn ψ v) q }`

is, near `x₀`, the graph of a `C¹` function `σ ↦ Ψ (τ, σ)` of the slab height `σ = ⟪v, par ψ ·⟫`,
with a nonzero `σ`-derivative of the sweep height along it and with the envelope formula for the
`τ`-derivative.  This is precisely an `EvChart` for the condition `Tangent ψ v a₀ b₀`.

## Proof

Consider the Lagrange map

`faceFn : (τ,σ,(x,λ)) ↦ (covec (∇sH_τ x − λ ∇hFn x), hFn x − σ)`

whose zero set is exactly the tangency locus.  At `p₀ = (τ₀,σ₀,(x₀,mu₀))` its derivative in the
`(x,λ)`-block is `faceSecDeriv`, which is invertible precisely by `hlag`
(`faceSecDeriv_isInvertible`); the map `faceG : (P,Q) ↦ (P, faceFn (P,Q))` is therefore a local
homeomorphism at `p₀` (inverse function theorem), and we read the chart off the local inverse
composed with `(τ,σ) ↦ (τ,σ,0)`.  The derivatives of the level function along the chart are
computed by `evLevel_sigma` and `evLevel_tau`.  Uniqueness is obtained from the injectivity of the
local homeomorphism, using that the tangency multiplier `λ` is a *continuous* function of `(τ,q)`
wherever `∇hFn ≠ 0`, so that it stays close to `mu₀`.
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal Topology

set_option maxHeartbeats 3000000

namespace Work.Drive.Mono

noncomputable section

/-- The parameter space `(τ, σ)` of the face chart. -/
abbrev FacePar : Type := ℝ × ℝ

/-- The unknown `(x, λ)` of the Lagrange equation `∇sH = λ ∇hFn`. -/
abbrev FaceUnk : Type := (ℝ × ℝ) × ℝ

/-! ## Smoothness of the Lagrange map -/

/-- The joint derivative of the sweep height, reindexed to the face chart's variables. -/
theorem contDiff_fderiv_sH_face {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) :
    ContDiff ℝ 1 (fun p : FacePar × FaceUnk =>
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x) p.2.1) := by
  have h1 : ContDiff ℝ 2 (Function.uncurry
      (fun p : FacePar × FaceUnk => fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x)) := by
    have h2 : Function.uncurry (fun p : FacePar × FaceUnk => fun x : ℝ × ℝ =>
          sH ψ a₀ b₀ p.1.1 x)
        = (Function.uncurry (sH ψ a₀ b₀)) ∘
            (fun w : (FacePar × FaceUnk) × (ℝ × ℝ) => (w.1.1.1, w.2)) := rfl
    rw [h2]
    exact (contDiff_sH_uncurry ha hb hab ψ).comp (by fun_prop)
  exact ContDiff.fderiv
    (f := fun p : FacePar × FaceUnk => fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x)
    (g := fun p : FacePar × FaceUnk => p.2.1) h1 (by fun_prop) (by norm_num)

/-- **The Lagrange (face) map is `C¹`.** -/
theorem contDiff_faceFn {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 1 (faceFn ψ v a₀ b₀) := by
  have hE : ContDiff ℝ 1 (fun p : FacePar × FaceUnk =>
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x) p.2.1) :=
    contDiff_fderiv_sH_face ha hb hab ψ
  have hG : ContDiff ℝ 1 (fun p : FacePar × FaceUnk =>
      fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p.2.1) :=
    (contDiff_fderiv_hFn ψ v).comp (by fun_prop)
  have hD : ContDiff ℝ 1 (fun p : FacePar × FaceUnk =>
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x) p.2.1
        - p.2.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p.2.1) :=
    hE.sub ((by fun_prop : ContDiff ℝ 1 (fun p : FacePar × FaceUnk => p.2.2)).smul hG)
  have h1 : ContDiff ℝ 1 (fun p : FacePar × FaceUnk =>
      covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x) p.2.1
        - p.2.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p.2.1)) :=
    covecL.contDiff.comp hD
  have h2 : ContDiff ℝ 1 (fun p : FacePar × FaceUnk => hFn ψ v p.2.1 - p.1.2) :=
    ((contDiff_hFn ψ v).comp (by fun_prop)).sub (by fun_prop)
  exact h1.prodMk h2

/-- The inverse-function-theorem map of the face chart: `(P,Q) ↦ (P, faceFn (P,Q))`. -/
def faceG (ψ : Submission.Diffeo) (v a₀ b₀ : R3) : FacePar × FaceUnk → FacePar × FaceUnk :=
  fun z => (z.1, faceFn ψ v a₀ b₀ z)

@[simp] theorem faceG_apply (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (z : FacePar × FaceUnk) :
    faceG ψ v a₀ b₀ z = (z.1, faceFn ψ v a₀ b₀ z) := rfl

/-- `faceG` is `C¹`. -/
theorem contDiff_faceG {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 1 (faceG ψ v a₀ b₀) := by
  have h1 : ContDiff ℝ 1 (fun z : FacePar × FaceUnk => z.1) :=
    (ContinuousLinearMap.fst ℝ FacePar FaceUnk).contDiff
  have h2 := contDiff_faceFn ha hb hab ψ v
  exact h1.prodMk h2

/-! ## The `(x,λ)`-block of the derivative of the Lagrange map -/

/-- The `(x,λ)`-block of the derivative of `faceFn` is the derivative of the section `faceSec`. -/
theorem fderiv_faceFn_comp_inr {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : R3) (τ₀ σ₀ : ℝ) (x₀ : ℝ × ℝ)
    (mu₀ : ℝ) :
    (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, σ₀), (x₀, mu₀)))
      ∘SL (ContinuousLinearMap.inr ℝ FacePar FaceUnk)
      = faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀ := by
  have hcd : ContDiff ℝ 1 (faceFn ψ v a₀ b₀) := contDiff_faceFn ha hb hab ψ v
  have hd : HasFDerivAt (faceFn ψ v a₀ b₀)
      (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, σ₀), (x₀, mu₀))) ((τ₀, σ₀), (x₀, mu₀)) :=
    ((hcd.differentiable one_ne_zero).differentiableAt).hasFDerivAt
  have hinr : HasFDerivAt (fun Q : FaceUnk => (((τ₀, σ₀) : FacePar), Q))
      (ContinuousLinearMap.inr ℝ FacePar FaceUnk) (x₀, mu₀) :=
    hasFDerivAt_prodMk_right (τ₀, σ₀) (x₀, mu₀)
  have hcomp := hd.comp (x₀, mu₀) hinr
  have h1 : HasFDerivAt (faceSec ψ v a₀ b₀ τ₀ σ₀)
      ((fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, σ₀), (x₀, mu₀)))
        ∘SL (ContinuousLinearMap.inr ℝ FacePar FaceUnk)) (x₀, mu₀) := hcomp
  exact h1.unique (hasFDerivAt_faceSec ha hb hab ψ v τ₀ σ₀ x₀ mu₀)

/-! ## Invertibility of the derivative of `faceG` -/

/-- **The derivative of `faceG` is invertible** at a point satisfying the Lagrange non-degeneracy
hypotheses. -/
theorem faceG_fderiv_isInvertible {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : R3) {τ₀ : ℝ} {x₀ : ℝ × ℝ} {mu₀ : ℝ}
    (htang : fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
      = mu₀ • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀)
    (hbne : fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ ≠ 0)
    (hlag : ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ w = 0 →
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) w) w
        - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) w) w) ≠ 0) :
    (fderiv ℝ (faceG ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))).IsInvertible := by
  classical
  have hcdF : ContDiff ℝ 1 (faceFn ψ v a₀ b₀) := contDiff_faceFn ha hb hab ψ v
  have hderiv_eq : fderiv ℝ (faceG ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))
      = (ContinuousLinearMap.fst ℝ FacePar FaceUnk).prod
          (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))) := by
    have h1 : HasFDerivAt (fun z : FacePar × FaceUnk => z.1)
        (ContinuousLinearMap.fst ℝ FacePar FaceUnk) ((τ₀, hFn ψ v x₀), (x₀, mu₀)) :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (faceFn ψ v a₀ b₀)
        (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))
        ((τ₀, hFn ψ v x₀), (x₀, mu₀)) :=
      ((hcdF.differentiable one_ne_zero).differentiableAt).hasFDerivAt
    have h3 : HasFDerivAt (fun z : FacePar × FaceUnk => (z.1, faceFn ψ v a₀ b₀ z))
        ((ContinuousLinearMap.fst ℝ FacePar FaceUnk).prod
          (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))))
        ((τ₀, hFn ψ v x₀), (x₀, mu₀)) := h1.prodMk h2
    exact h3.fderiv
  have hsection : (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))
      ∘SL (ContinuousLinearMap.inr ℝ FacePar FaceUnk) = faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀ :=
    fderiv_faceFn_comp_inr ha hb hab ψ v τ₀ (hFn ψ v x₀) x₀ mu₀
  have hinj : Function.Injective ((ContinuousLinearMap.fst ℝ FacePar FaceUnk).prod
      (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))) := by
    rintro ⟨δP, δQ⟩ ⟨ηP, ηQ⟩ h
    have h1 : δP = ηP := congrArg (fun z : FacePar × FaceUnk => z.1) h
    have h2 : (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))) (δP, δQ)
        = (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀))) (ηP, ηQ) :=
      congrArg (fun z : FacePar × FaceUnk => z.2) h
    have h5 : (δP, δQ) - (ηP, ηQ) = ((0 : FacePar), δQ - ηQ) := by
      ext <;> simp [h1]
    have h3 : (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))
        ((0 : FacePar), δQ - ηQ) = 0 := by
      rw [← h5, map_sub, h2, sub_self]
    have h4 : faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀ (δQ - ηQ) = 0 := by
      rw [← congrArg (fun T => T (δQ - ηQ)) hsection]
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      exact h3
    have h6 : δQ - ηQ = 0 := faceSecDeriv_injective (ψ := ψ) (v := v) ha hb hab τ₀ x₀ mu₀
      hbne hlag (δQ - ηQ) h4
    exact Prod.ext h1 (sub_eq_zero.mp h6)
  have hMinv : ((ContinuousLinearMap.fst ℝ FacePar FaceUnk).prod
      (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective
      ((ContinuousLinearMap.fst ℝ FacePar FaceUnk).prod
        (fderiv ℝ (faceFn ψ v a₀ b₀) ((τ₀, hFn ψ v x₀), (x₀, mu₀)))) ?_ ?_, rfl⟩
    · rw [LinearMap.ker_eq_bot]
      exact hinj
    · rw [LinearMap.range_eq_top]
      exact LinearMap.injective_iff_surjective.mp hinj
  rwa [hderiv_eq]

/-! ## The face-event chart -/

theorem exists_faceChart {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : LeanEval.KnotTheory.PardonDistortion.R3)
    {τ₀ : ℝ} {x₀ : ℝ × ℝ} {mu₀ : ℝ}
    (htang : fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ τ₀ x) x₀
      = mu₀ • fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.hFn ψ v x) x₀)
    (hmu : mu₀ ≠ 0)
    (hbne : fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.hFn ψ v x) x₀ ≠ 0)
    (hlag : ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.hFn ψ v x) x₀ w = 0 →
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ τ₀ x)) x₀) w) w
        - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.hFn ψ v x)) x₀) w) w) ≠ 0) :
    Nonempty (Work.Drive.Mono.EvChart ψ v a₀ b₀ (Work.Drive.Mono.Tangent ψ v a₀ b₀) τ₀
      (Work.Drive.Mono.hFn ψ v x₀) x₀) := by
  classical
  -- ## 0. abbreviation
  let σ₀ : ℝ := hFn ψ v x₀
  -- ## 1. the Lagrange map vanishes at the base point
  have hzero : faceFn ψ v a₀ b₀ ((τ₀, σ₀), (x₀, mu₀)) = 0 := by
    have h1 : covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
        - mu₀ • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) = 0 := by
      rw [htang, sub_self]
      rfl
    have h2 : hFn ψ v x₀ - σ₀ = 0 := by simp [σ₀]
    have hthis : faceFn ψ v a₀ b₀ ((τ₀, σ₀), (x₀, mu₀))
        = (covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
            - mu₀ • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀), hFn ψ v x₀ - σ₀) := rfl
    rw [hthis, h1, h2]
    rfl
  have hGz₀ : faceG ψ v a₀ b₀ ((τ₀, σ₀), (x₀, mu₀)) = ((τ₀, σ₀), (0 : FaceUnk)) := by
    rw [faceG_apply, hzero]
  -- ## 2. the inverse-function-theorem homeomorphism
  have hGcd : ContDiff ℝ 1 (faceG ψ v a₀ b₀) := contDiff_faceG ha hb hab ψ v
  have hMinv : (fderiv ℝ (faceG ψ v a₀ b₀) ((τ₀, σ₀), (x₀, mu₀))).IsInvertible :=
    faceG_fderiv_isInvertible ha hb hab ψ v htang hbne hlag
  obtain ⟨E', hE'⟩ := hMinv
  have hGd : HasFDerivAt (faceG ψ v a₀ b₀)
      (E' : (FacePar × FaceUnk) →L[ℝ] (FacePar × FaceUnk)) ((τ₀, σ₀), (x₀, mu₀)) := by
    have h := ((hGcd.differentiable one_ne_zero).differentiableAt
      (x := ((τ₀, σ₀), (x₀, mu₀)))).hasFDerivAt
    rw [← hE'] at h
    exact h
  let e : OpenPartialHomeomorph (FacePar × FaceUnk) (FacePar × FaceUnk) :=
    ContDiffAt.toOpenPartialHomeomorph (faceG ψ v a₀ b₀) hGcd.contDiffAt hGd one_ne_zero
  have hecoe : (e : FacePar × FaceUnk → FacePar × FaceUnk) = faceG ψ v a₀ b₀ :=
    ContDiffAt.toOpenPartialHomeomorph_coe hGcd.contDiffAt hGd one_ne_zero
  have hmem : ((τ₀, σ₀), (x₀, mu₀)) ∈ e.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hGcd.contDiffAt hGd one_ne_zero
  have htgt : faceG ψ v a₀ b₀ ((τ₀, σ₀), (x₀, mu₀)) ∈ e.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hGcd.contDiffAt hGd one_ne_zero
  have htgt' : ((τ₀, σ₀), (0 : FaceUnk)) ∈ e.target := by rw [← hGz₀]; exact htgt
  have hesymm : e.symm ((τ₀, σ₀), (0 : FaceUnk)) = ((τ₀, σ₀), (x₀, mu₀)) := by
    have h := e.left_inv hmem
    rw [hecoe] at h
    rwa [hGz₀] at h
  -- ## 3. a neighbourhood of the base point where `fderiv faceG` is invertible
  have hN : Set.range ContinuousLinearEquiv.toContinuousLinearMap
      ∈ 𝓝 (fderiv ℝ (faceG ψ v a₀ b₀) ((τ₀, σ₀), (x₀, mu₀))) := by
    rw [← hE']
    exact ContinuousLinearEquiv.nhds E'
  have hderiv_cont : Continuous (fun x : FacePar × FaceUnk => fderiv ℝ (faceG ψ v a₀ b₀) x) :=
    hGcd.continuous_fderiv one_ne_zero
  have hpre : (fun x : FacePar × FaceUnk => fderiv ℝ (faceG ψ v a₀ b₀) x) ⁻¹'
      Set.range ContinuousLinearEquiv.toContinuousLinearMap ∈ 𝓝 ((τ₀, σ₀), (x₀, mu₀)) :=
    hderiv_cont.continuousAt hN
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hballInv : ∀ x ∈ Metric.ball ((τ₀, σ₀), (x₀, mu₀)) ε,
      (fderiv ℝ (faceG ψ v a₀ b₀) x).IsInvertible := fun x hx => hεsub hx
  -- ## 4. the tangency multiplier as a continuous function
  let evec : ℝ × ℝ :=
    if (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) (1, 0) ≠ 0 then (1, 0) else (0, 1)
  have hevec : (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) evec ≠ 0 := by
    dsimp only [evec]
    by_cases h : (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) (1, 0) ≠ 0
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      intro h0
      exact hbne (by
        refine ContinuousLinearMap.ext fun w => ?_
        have hw : w = w.1 • ((1, 0) : ℝ × ℝ) + w.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
        have h10 : (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) (1, 0) = 0 := by
          by_contra hc
          exact h hc
        rw [hw, map_add, map_smul, map_smul, h10, h0]
        simp)
  let T : ℝ × (ℝ × ℝ) → ℝ := fun r =>
    ((fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ r.1 x) r.2) evec)
      / ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) r.2) evec)
  have hT_eq : ∀ {τ : ℝ} {q : ℝ × ℝ} {t : ℝ},
      (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec ≠ 0 →
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q
        = t • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q →
      T (τ, q) = t := by
    intro τ q t hB hpar
    have h1 : (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q) evec
        = t * ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec) := by
      rw [hpar, smul_apply, smul_eq_mul]
    show ((fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q) evec)
      / ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec) = t
    rw [h1, mul_div_cancel_right₀ _ hB]
  have hT_cont : ContinuousAt T (τ₀, x₀) := by
    have hA : ContinuousAt (fun r : ℝ × (ℝ × ℝ) =>
        (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ r.1 x) r.2) evec) (τ₀, x₀) :=
      (contDiff_fderiv_sH_apply ha hb hab ψ evec).continuous.continuousAt
    have hB : ContinuousAt (fun r : ℝ × (ℝ × ℝ) =>
        (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) r.2) evec) (τ₀, x₀) := by
      have h1 : Continuous (fun q : ℝ × ℝ =>
          (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec) :=
        ((ContinuousLinearMap.apply ℝ ℝ evec).continuous).comp (contDiff_fderiv_hFn ψ v).continuous
      exact (h1.comp continuous_snd).continuousAt
    show ContinuousAt (fun r : ℝ × (ℝ × ℝ) =>
      ((fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ r.1 x) r.2) evec)
        / ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) r.2) evec)) (τ₀, x₀)
    exact hA.div hB hevec
  have hTx₀ : T (τ₀, x₀) = mu₀ := by
    have h1 : (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀) evec
        = mu₀ * ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) evec) := by
      rw [htang, smul_apply, smul_eq_mul]
    show ((fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀) evec)
      / ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) evec) = mu₀
    rw [h1, mul_div_cancel_right₀ _ hevec]
  -- ## 5. the continuous map carrying the tangency point to `e.source`
  let Φ : ℝ × (ℝ × ℝ) → FacePar × FaceUnk := fun r => ((r.1, hFn ψ v r.2), (r.2, T r))
  have hΦz : Φ (τ₀, x₀) = ((τ₀, σ₀), (x₀, mu₀)) := by
    show ((τ₀, hFn ψ v x₀), (x₀, T (τ₀, x₀))) = ((τ₀, σ₀), (x₀, mu₀))
    rw [hTx₀]
  have hΦcont : ContinuousAt Φ (τ₀, x₀) := by
    refine ContinuousAt.prodMk ?_ ?_
    · exact (continuous_fst.continuousAt).prodMk
        (((contDiff_hFn ψ v).continuous).continuousAt.comp continuous_snd.continuousAt)
    · exact (continuous_snd.continuousAt).prodMk hT_cont
  have hW : e.source ∈ 𝓝 ((τ₀, σ₀), (x₀, mu₀)) := e.open_source.mem_nhds hmem
  have hW' : e.source ∈ 𝓝 (Φ (τ₀, x₀)) := by rw [hΦz]; exact hW
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hΦcont.preimage_mem_nhds hW')
  -- ## 6. the chart domain and the chart map
  have hAopen : IsOpen (e.target ∩ e.symm ⁻¹' Metric.ball ((τ₀, σ₀), (x₀, mu₀)) ε) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target Metric.isOpen_ball
  let U : Set (ℝ × ℝ) := Metric.ball x₀ δ ∩
    {q : ℝ × ℝ | (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec ≠ 0}
  have hUopen : IsOpen U := by
    refine (Metric.isOpen_ball (x := x₀) (ε := δ)).inter ?_
    exact isOpen_ne.preimage
      (((ContinuousLinearMap.apply ℝ ℝ evec).continuous).comp (contDiff_fderiv_hFn ψ v).continuous)
  have hUmem : x₀ ∈ U := ⟨Metric.mem_ball_self hδpos, hevec⟩
  let V : Set (ℝ × ℝ) := (fun P : ℝ × ℝ => P.1) ⁻¹' Metric.ball τ₀ δ ∩
    {P : ℝ × ℝ | (P, (0 : FaceUnk)) ∈ e.target ∩ e.symm ⁻¹'
      Metric.ball ((τ₀, σ₀), (x₀, mu₀)) ε}
  have hVopen : IsOpen V := by
    refine (Metric.isOpen_ball (x := τ₀) (ε := δ)).preimage continuous_fst |>.inter ?_
    exact hAopen.preimage (continuous_id.prodMk continuous_const)
  have hVmem : (τ₀, σ₀) ∈ V := by
    refine ⟨?_, htgt', ?_⟩
    · exact Metric.mem_ball_self hδpos
    · show e.symm ((τ₀, σ₀), (0 : FaceUnk)) ∈ Metric.ball ((τ₀, σ₀), (x₀, mu₀)) ε
      rw [hesymm]
      exact Metric.mem_ball_self hεpos
  let Ψ : ℝ × ℝ → ℝ × ℝ := fun P => (e.symm (P, (0 : FaceUnk))).2.1
  have hΨmem : Ψ (τ₀, σ₀) = x₀ := by
    show (e.symm ((τ₀, σ₀), (0 : FaceUnk))).2.1 = x₀
    rw [hesymm]
  have hgΨ : ∀ P ∈ V, hFn ψ v (Ψ P) = P.2 := by
    intro P hP
    have h1 : (e : FacePar × FaceUnk → FacePar × FaceUnk) (e.symm (P, (0 : FaceUnk)))
        = (P, (0 : FaceUnk)) := e.right_inv hP.2.1
    rw [hecoe] at h1
    have h3 : (e.symm (P, (0 : FaceUnk))).1 = P := by
      have h := congrArg (fun z : FacePar × FaceUnk => z.1) h1
      exact h
    have h4 : hFn ψ v (e.symm (P, (0 : FaceUnk))).2.1
        - (e.symm (P, (0 : FaceUnk))).1.2 = 0 := by
      have h := congrArg (fun z : FacePar × FaceUnk => z.2.2) h1
      exact h
    rw [h3] at h4
    show hFn ψ v (e.symm (P, (0 : FaceUnk))).2.1 = P.2
    exact sub_eq_zero.mp h4
  have hΨcd : ContDiffOn ℝ 1 Ψ V := by
    rw [hVopen.contDiffOn_iff]
    intro P hP
    obtain ⟨T', hT'⟩ := hballInv (e.symm (P, (0 : FaceUnk))) hP.2.2
    have hderivF : HasFDerivAt (faceG ψ v a₀ b₀)
        (T' : (FacePar × FaceUnk) →L[ℝ] (FacePar × FaceUnk))
        (e.symm (P, (0 : FaceUnk))) := by
      rw [show (T' : (FacePar × FaceUnk) →L[ℝ] (FacePar × FaceUnk))
          = fderiv ℝ (faceG ψ v a₀ b₀) (e.symm (P, (0 : FaceUnk))) from hT']
      exact ((hGcd.contDiffAt (x := e.symm (P, (0 : FaceUnk)))).differentiableAt
        one_ne_zero).hasFDerivAt
    have hsymm_cd : ContDiffAt ℝ 1 (fun y : FacePar × FaceUnk => e.symm y) (P, (0 : FaceUnk)) :=
      e.contDiffAt_symm (f₀' := T') hP.2.1 (by rw [hecoe]; exact hderivF)
        (by rw [hecoe]; exact hGcd.contDiffAt)
    have hpair : ContDiffAt ℝ 1 (fun P : ℝ × ℝ => (P, (0 : FaceUnk))) P := by fun_prop
    have hflam : ContDiffAt ℝ 1 (fun P : ℝ × ℝ => e.symm (P, (0 : FaceUnk))) P :=
      hsymm_cd.comp P hpair
    have hsnd : ContDiffAt ℝ 1 (fun z : FacePar × FaceUnk => z.2)
        (e.symm (P, (0 : FaceUnk))) :=
      (ContinuousLinearMap.snd ℝ FacePar FaceUnk).contDiff.contDiffAt
    have h2 : ContDiffAt ℝ 1 ((fun z : FacePar × FaceUnk => z.2) ∘
        (fun P : ℝ × ℝ => e.symm (P, (0 : FaceUnk)))) P :=
      hsnd.comp P hflam
    have hfst : ContDiffAt ℝ 1 (fun w : FaceUnk => w.1) ((e.symm (P, (0 : FaceUnk))).2) :=
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).contDiff.contDiffAt
    have h3 : ContDiffAt ℝ 1 ((fun w : FaceUnk => w.1) ∘
        ((fun z : FacePar × FaceUnk => z.2) ∘
          (fun P : ℝ × ℝ => e.symm (P, (0 : FaceUnk))))) P :=
      hfst.comp P h2
    exact h3
  -- ## 7. the level-function derivatives along the chart
  have hσ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (0, 1) ≠ 0 := by
    have h := evLevel_sigma (a₀ := a₀) (b₀ := b₀) (ψ := ψ) (v := v)
      (τ₀ := τ₀) (σ₀ := σ₀) (mu₀ := mu₀) (x₀ := x₀) (Ψ := Ψ) (V := V)
      ha hb hab hVopen hVmem hΨcd hΨmem hgΨ htang
    rw [h]
    exact hmu
  have hτ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (1, 0)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ x₀) :=
    evLevel_tau (a₀ := a₀) (b₀ := b₀) (ψ := ψ) (v := v)
      (τ₀ := τ₀) (σ₀ := σ₀) (mu₀ := mu₀) (x₀ := x₀) (Ψ := Ψ) (V := V)
      ha hb hab hVopen hVmem hΨcd hΨmem hgΨ htang
  -- ## 8. uniqueness
  have huniq : ∀ (τ σ : ℝ) (q : ℝ × ℝ), (τ, σ) ∈ V → q ∈ U →
      Tangent ψ v a₀ b₀ τ q → hFn ψ v q = σ → q = Ψ (τ, σ) := by
    intro τ σ q hτσV hqU hcare hσq
    obtain ⟨t, ht⟩ := hcare
    have hqball : q ∈ Metric.ball x₀ δ := hqU.1
    have hqB : (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) q) evec ≠ 0 := hqU.2
    have htT : t = T (τ, q) := (hT_eq hqB ht).symm
    have hτball : τ ∈ Metric.ball τ₀ δ := hτσV.1
    have hdist : (τ, q) ∈ Metric.ball (τ₀, x₀) δ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp hτball) (Metric.mem_ball.mp hqball)
    have hΦmem : Φ (τ, q) ∈ e.source := hδsub hdist
    have hΦmem' : ((τ, σ), (q, t)) ∈ e.source := by
      rw [← hσq, htT]
      exact hΦmem
    have hface : faceFn ψ v a₀ b₀ ((τ, σ), (q, t)) = 0 := by
      have h1 : covec (fderiv ℝ (sH ψ a₀ b₀ τ) q - t • fderiv ℝ (hFn ψ v) q) = 0 := by
        rw [ht, sub_self]
        rfl
      have h2 : hFn ψ v q - σ = 0 := by rw [hσq, sub_self]
      have hthis : faceFn ψ v a₀ b₀ ((τ, σ), (q, t))
          = (covec (fderiv ℝ (sH ψ a₀ b₀ τ) q - t • fderiv ℝ (hFn ψ v) q), hFn ψ v q - σ) := rfl
      rw [hthis, h1, h2]
      rfl
    have hP : ((τ, σ), (0 : FaceUnk)) ∈ e.target := hτσV.2.1
    have hsym_mem : e.symm ((τ, σ), (0 : FaceUnk)) ∈ e.source := e.map_target hP
    have heq1 : (e : FacePar × FaceUnk → FacePar × FaceUnk) ((τ, σ), (q, t))
        = ((τ, σ), (0 : FaceUnk)) := by
      rw [hecoe]
      show ((τ, σ), faceFn ψ v a₀ b₀ ((τ, σ), (q, t))) = ((τ, σ), (0 : FaceUnk))
      rw [hface]
    have heq2 : (e : FacePar × FaceUnk → FacePar × FaceUnk) (e.symm ((τ, σ), (0 : FaceUnk)))
        = ((τ, σ), (0 : FaceUnk)) := e.right_inv hP
    have hfin : ((τ, σ), (q, t)) = e.symm ((τ, σ), (0 : FaceUnk)) :=
      e.injOn hΦmem' hsym_mem (heq1.trans heq2.symm)
    have hqeq : q = (e.symm ((τ, σ), (0 : FaceUnk))).2.1 := by
      have h := congrArg (fun z : FacePar × FaceUnk => z.2.1) hfin
      exact h
    rw [hqeq]
  exact ⟨{ V := V
           hVopen := hVopen
           hVmem := hVmem
           Ψ := Ψ
           hΨcd := hΨcd
           hΨmem := hΨmem
           hg := hgΨ
           hσ := hσ
           hτ := hτ
           U := U
           hUopen := hUopen
           hUmem := hUmem
           huniq := huniq }⟩

end

end Work.Drive.Mono
