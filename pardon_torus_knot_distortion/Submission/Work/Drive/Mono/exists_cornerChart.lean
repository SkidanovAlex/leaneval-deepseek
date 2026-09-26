import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux
import Submission.Work.Drive.Mono.dirOfBasic

/-!
# `Work.Drive.Mono.exists_cornerChart`

A **corner (or face) event chart**: at a parameter-plane point `x₀` at which the pair

`q ↦ ((par ψ q) (σi i), ⟪v, par ψ q⟫)`

(the `σi i`-th coordinate of the parametrisation of the embedded torus, and the slab height) has an
invertible derivative, and at which the sweep height at tilt `τ₀` is *not* proportional to the
derivative of the coordinate function, the event locus

`{(τ, q) | (par ψ q) (σi i) = (par ψ x₀) (σi i)}`

is, near `x₀`, the graph of a `C¹` function `σ ↦ Ψ (τ, σ)` of the slab height `σ = ⟪v, par ψ ·⟫`,
with a nonvanishing `σ`-derivative of the sweep height along it (transversality), and with the
envelope formula for the `τ`-derivative.  This is precisely an `EvChart`.

## Proof

By the inverse function theorem for `F = ((par ψ ·) (σi i), ⟪v, par ψ ·⟫)` at `x₀`, `F` is a local
homeomorphism; its local inverse on a neighbourhood of `F x₀` parametrises the coordinate level
curve by the slab height, and it is `C¹`.  The `τ`-direction is constant in the parametrisation, so
the level function of the chart, `(τ, σ) ↦ sH ψ a₀ b₀ τ (Ψ (τ, σ))`, has `τ`-derivative
`⟪deriv dirOf τ₀, par ψ x₀⟫` and `σ`-derivative `β (0,1)` where
`β = (fderiv sH) ∘ (fderiv F)⁻¹`; the latter is nonzero precisely because `fderiv sH` is not a
multiple of the derivative of the coordinate function (`hnt`).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace Topology

namespace Work.Drive.Mono

theorem exists_cornerChart {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (σi : Equiv.Perm (Fin 3)) (i : Fin 3) {τ₀ : ℝ} {x₀ : ℝ × ℝ}
    (hinv : (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σi i),
        inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) x₀).IsInvertible)
    (hnt : ∀ t : ℝ, fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ τ₀ x) x₀ ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σi i)) x₀) :
    Nonempty (Work.Drive.Mono.EvChart ψ v a₀ b₀ (fun τ q => (Work.BoxShrink.Pinch.par ψ q) (σi i) =
      (Work.BoxShrink.Pinch.par ψ x₀) (σi i)) τ₀ (Work.Drive.Mono.hFn ψ v x₀) x₀) := by
  classical
  -- ## 0. abbreviations
  let P : ℝ × ℝ → R3 := Work.BoxShrink.Pinch.par ψ
  let f : ℝ × ℝ → ℝ := fun q => P q (σi i)
  let F : ℝ × ℝ → ℝ × ℝ := fun q => (f q, hFn ψ v q)
  let c : ℝ := f x₀
  let σ₀ : ℝ := hFn ψ v x₀
  let D : R3 := Work.Drive.Mono.Band.dirOf τ₀ a₀ b₀
  -- ## 1. smoothness of the three functions involved
  have hP1 : ContDiff ℝ 1 P :=
    (Work.BoxShrink.Pinch.par_contDiff ψ).of_le (m := 1) (WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiff ℝ 1 f :=
    (contDiff_piLp_apply (i := σi i) (p := 2)).comp hP1
  have hg : ContDiff ℝ 1 (hFn ψ v) := contDiff_hFn ψ v
  have hFcd : ContDiff ℝ 1 F := hf.prodMk hg
  -- ## 2. the derivative of `F` and its invertibility
  have hFderiv : fderiv ℝ F x₀
      = (fderiv ℝ f x₀).prod (fderiv ℝ (hFn ψ v) x₀) := by
    have h1 : HasFDerivAt F ((fderiv ℝ f x₀).prod (fderiv ℝ (hFn ψ v) x₀)) x₀ :=
      ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt).prodMk
        ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt)
    exact h1.fderiv
  obtain ⟨A, hA⟩ := (show (fderiv ℝ F x₀).IsInvertible from hinv)
  have hAd : HasFDerivAt F (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) x₀ := by
    rw [hA]
    exact (hFcd.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  let Λ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (A.symm : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
  -- ## 3. the local homeomorphism and its inverse
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    ContDiffAt.toOpenPartialHomeomorph F hFcd.contDiffAt hAd one_ne_zero
  have hecoe : (e : ℝ × ℝ → ℝ × ℝ) = F :=
    ContDiffAt.toOpenPartialHomeomorph_coe hFcd.contDiffAt hAd one_ne_zero
  have hmem : x₀ ∈ e.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hFcd.contDiffAt hAd one_ne_zero
  have htgt : F x₀ ∈ e.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hFcd.contDiffAt hAd one_ne_zero
  have hesymm : (e.symm : ℝ × ℝ → ℝ × ℝ) (F x₀) = x₀ := by
    have h := e.left_inv hmem
    rwa [hecoe] at h
  have hesymm' : (e.symm : ℝ × ℝ → ℝ × ℝ) (c, σ₀) = x₀ := hesymm
  have hderiv_symm : HasFDerivAt (fun y : ℝ × ℝ => e.symm y) Λ (F x₀) := by
    refine e.hasFDerivAt_symm htgt ?_
    rw [hesymm]
    exact hAd
  -- ## 4. a neighbourhood of `x₀` on which `fderiv F` is invertible
  have hN : Set.range ContinuousLinearEquiv.toContinuousLinearMap ∈ 𝓝 (fderiv ℝ F x₀) := by
    rw [← hA]
    exact ContinuousLinearEquiv.nhds A
  have hderiv_cont : Continuous (fun x : ℝ × ℝ => fderiv ℝ F x) :=
    hFcd.continuous_fderiv one_ne_zero
  have hpre : (fun x : ℝ × ℝ => fderiv ℝ F x) ⁻¹'
      Set.range ContinuousLinearEquiv.toContinuousLinearMap ∈ 𝓝 x₀ :=
    hderiv_cont.continuousAt hN
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hballInv : ∀ x ∈ Metric.ball x₀ ε, (fderiv ℝ F x).IsInvertible :=
    fun x hx => hεsub hx
  -- ## 5. the domain `V` of the chart and the chart map `Ψ`
  have hAopen : IsOpen (e.target ∩ e.symm ⁻¹' Metric.ball x₀ ε) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target Metric.isOpen_ball
  let V : Set (ℝ × ℝ) := {p : ℝ × ℝ | (c, p.2) ∈ e.target ∩ e.symm ⁻¹' Metric.ball x₀ ε}
  have hVopen : IsOpen V := hAopen.preimage (by fun_prop)
  let Ψ : ℝ × ℝ → ℝ × ℝ := fun p => e.symm (c, p.2)
  have hVmem : (τ₀, σ₀) ∈ V := by
    refine ⟨?_, ?_⟩
    · exact htgt
    · show (e.symm : ℝ × ℝ → ℝ × ℝ) (c, σ₀) ∈ Metric.ball x₀ ε
      rw [hesymm']
      exact Metric.mem_ball_self hεpos
  have hΨmem : Ψ (τ₀, σ₀) = x₀ := hesymm'
  have hΨσ₀ : ∀ τ : ℝ, Ψ (τ, σ₀) = x₀ := fun τ => hesymm'
  have hgΨ : ∀ p ∈ V, hFn ψ v (Ψ p) = p.2 := by
    intro p hp
    have h := e.right_inv hp.1
    rw [hecoe] at h
    exact congrArg Prod.snd h
  -- ## 6. `C¹`-regularity of `Ψ`
  have hΨcd : ContDiffOn ℝ 1 Ψ V := by
    rw [hVopen.contDiffOn_iff]
    intro p hp
    obtain ⟨T, hT⟩ := hballInv (e.symm (c, p.2)) hp.2
    have hderivF : HasFDerivAt F (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm (c, p.2)) := by
      rw [show (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = fderiv ℝ F (e.symm (c, p.2)) from hT]
      exact (hFcd.contDiffAt (x := (e.symm (c, p.2)))).differentiableAt one_ne_zero
        |>.hasFDerivAt
    have hsymm_cd : ContDiffAt ℝ 1 (fun y : ℝ × ℝ => e.symm y) (c, p.2) :=
      e.contDiffAt_symm (f₀' := T) hp.1 (by rw [hecoe]; exact hderivF)
        (by rw [hecoe]; exact hFcd.contDiffAt)
    have hpair : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (c, p.2)) p := by fun_prop
    exact hsymm_cd.comp p hpair
  -- ## 7. the derivative of the chart map in the `σ`-direction
  have hΞderiv : HasDerivAt (fun s : ℝ => e.symm (c, s)) (Λ (0, 1)) σ₀ := by
    have h2 : HasDerivAt (fun s : ℝ => (c, s)) (0, 1) σ₀ := by
      have h := (hasFDerivAt_prodMk_right c σ₀).hasDerivAt
      simpa [ContinuousLinearMap.inr_apply] using h
    exact hderiv_symm.comp_hasDerivAt σ₀ h2
  have hPderiv : HasFDerivAt P (fderiv ℝ P x₀) (e.symm (c, σ₀)) := by
    rw [hesymm']
    exact (hP1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hΞP : HasDerivAt (fun s : ℝ => P (e.symm (c, s))) ((fderiv ℝ P x₀) (Λ (0, 1))) σ₀ :=
    hPderiv.comp_hasDerivAt σ₀ hΞderiv
  -- ## 8. the derivative of `sH` at `x₀`
  have hsHderiv : fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
      = (innerSL ℝ D) ∘SL (fderiv ℝ P x₀) := by
    have hfun : (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) = (innerSL ℝ D) ∘ P := by
      funext x
      simp only [sH_apply, Function.comp_apply, innerSL_apply_apply, P, D]
    rw [hfun]
    have hd : HasFDerivAt ((innerSL ℝ D) ∘ P) ((innerSL ℝ D) ∘SL (fderiv ℝ P x₀)) x₀ :=
      (ContinuousLinearMap.hasFDerivAt (innerSL ℝ D)).comp x₀
        ((hP1.differentiable one_ne_zero).differentiableAt.hasFDerivAt)
    exact hd.fderiv
  let α : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
  let β : (ℝ × ℝ) →L[ℝ] ℝ := α ∘SL Λ
  have hσval : (innerSL ℝ D) ((fderiv ℝ P x₀) (Λ (0, 1))) = β (0, 1) := by
    rw [show β = α ∘SL Λ from rfl]
    rw [show α = (innerSL ℝ D) ∘SL (fderiv ℝ P x₀) from hsHderiv]
    rfl
  have hinner : HasDerivAt (fun s : ℝ => inner ℝ D (P (e.symm (c, s)))) (β (0, 1)) σ₀ := by
    have hraw : HasDerivAt (fun s : ℝ => inner ℝ D (P (e.symm (c, s))))
        ((innerSL ℝ D) ((fderiv ℝ P x₀) (Λ (0, 1)))) σ₀ :=
      (ContinuousLinearMap.hasFDerivAt (innerSL ℝ D)).comp_hasDerivAt σ₀ hΞP
    rwa [hσval] at hraw
  -- ## 9. `β (0,1) ≠ 0`: the transversality hypothesis `hnt`
  have hβne : β (0, 1) ≠ 0 := by
    intro h0
    -- `β` only sees the first coordinate of its argument
    have hβpt : ∀ v : ℝ × ℝ, β v = β (1, 0) * v.1 := by
      intro v
      have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, h0]
      ring
    -- hence `α = β (1,0) • fderiv f x₀`, contradicting `hnt`
    have hM : α = β (1, 0) • (fderiv ℝ f x₀) := by
      refine ContinuousLinearMap.ext fun x => ?_
      have h1 : β ((A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) x) = α x := by
        show (α ∘SL Λ) (A x) = α x
        rw [ContinuousLinearMap.comp_apply]
        congr 1
        simp [Λ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      have h3 : ((A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) x).1 = (fderiv ℝ f x₀) x := by
        rw [hA, hFderiv, ContinuousLinearMap.prod_apply]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, ← h1, hβpt, h3]
    exact hnt (β (1, 0)) hM
  -- ## 10. the level function, its slice derivatives, and the chart fields
  have hσcurve : HasDerivAt (fun s : ℝ => evLevel ψ a₀ b₀ Ψ (τ₀, s)) (β (0, 1)) σ₀ := by
    have hfun : (fun s : ℝ => evLevel ψ a₀ b₀ Ψ (τ₀, s))
        = (fun s : ℝ => inner ℝ D (P (e.symm (c, s)))) := by
      funext s
      rfl
    rw [hfun]
    exact hinner
  have hevcd : ContDiffOn ℝ 1 (evLevel ψ a₀ b₀ Ψ) V := by
    rw [hVopen.contDiffOn_iff]
    intro p hp
    have h1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (q.1, Ψ q)) p :=
      ContDiffAt.prodMk (ContDiffAt.fst contDiffAt_id) (hΨcd.contDiffAt (hVopen.mem_nhds hp))
    have h2 : ContDiffAt ℝ 1 (Function.uncurry (sH ψ a₀ b₀)) (p.1, Ψ p) :=
      ((contDiff_sH_uncurry ha hb hab ψ).of_le (m := 1) (by norm_num)).contDiffAt
    exact h2.comp p h1
  have hL : HasFDerivAt (evLevel ψ a₀ b₀ Ψ) (fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)) (τ₀, σ₀) :=
    ((hevcd.contDiffAt (hVopen.mem_nhds hVmem)).differentiableAt one_ne_zero).hasFDerivAt
  have hγσ : HasDerivAt (fun s : ℝ => (τ₀, s)) (0, 1) σ₀ := by
    have h := (hasFDerivAt_prodMk_right τ₀ σ₀).hasDerivAt
    simpa [ContinuousLinearMap.inr_apply] using h
  have hLσ : HasDerivAt (fun s : ℝ => evLevel ψ a₀ b₀ Ψ (τ₀, s))
      ((fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)) (0, 1)) σ₀ := by
    have h := hL.comp_hasDerivAt σ₀ hγσ
    simpa only [Function.comp_def] using h
  have hσ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (0, 1) ≠ 0 := by
    have hval : (fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)) (0, 1) = β (0, 1) :=
      hLσ.unique hσcurve
    rw [fderivWithin_of_mem_nhds (hVopen.mem_nhds hVmem), hval]
    exact hβne
  have hτcurve : HasDerivAt (fun θ : ℝ => evLevel ψ a₀ b₀ Ψ (θ, σ₀))
      (inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀) (P x₀)) τ₀ := by
    have hexpl : HasDerivAt (fun θ : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf θ a₀ b₀) (P x₀))
        (inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀) (P x₀)) τ₀ := by
      have h := HasDerivAt.inner ℝ (hasDerivAt_dirOf ha hb hab τ₀)
        (hasDerivAt_const (x := τ₀) (c := P x₀))
      simpa [deriv_dirOf ha hb hab τ₀] using h
    have hfun : (fun θ : ℝ => evLevel ψ a₀ b₀ Ψ (θ, σ₀))
        = (fun θ : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf θ a₀ b₀) (P x₀)) := by
      funext θ
      show inner ℝ (Work.Drive.Mono.Band.dirOf θ a₀ b₀) (P (Ψ (θ, σ₀)))
        = inner ℝ (Work.Drive.Mono.Band.dirOf θ a₀ b₀) (P x₀)
      rw [show Ψ (θ, σ₀) = x₀ from hΨσ₀ θ]
    rw [hfun]
    exact hexpl
  have hγτ : HasDerivAt (fun θ : ℝ => (θ, σ₀)) (1, 0) τ₀ := by
    have h := (hasFDerivAt_prodMk_left τ₀ σ₀).hasDerivAt
    simpa [ContinuousLinearMap.inl_apply] using h
  have hLτ : HasDerivAt (fun θ : ℝ => evLevel ψ a₀ b₀ Ψ (θ, σ₀))
      ((fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)) (1, 0)) τ₀ := by
    have h := hL.comp_hasDerivAt τ₀ hγτ
    simpa only [Function.comp_def] using h
  have hτ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (1, 0)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀) (P x₀) := by
    rw [fderivWithin_of_mem_nhds (hVopen.mem_nhds hVmem)]
    exact hLτ.unique hτcurve
  -- ## 11. uniqueness
  let U : Set (ℝ × ℝ) := e.source
  have huniq : ∀ (τ σ : ℝ) (q : ℝ × ℝ), (τ, σ) ∈ V → q ∈ U → (f q = f x₀) → hFn ψ v q = σ →
      q = Ψ (τ, σ) := by
    intro τ σ q hτσV hqU hcare hσq
    have h1 : e q = (c, σ) := by
      rw [hecoe]
      show (f q, hFn ψ v q) = (c, σ)
      rw [hσq]
      exact congrArg₂ Prod.mk hcare rfl
    have h2 : e (Ψ (τ, σ)) = (c, σ) := by
      have h := e.right_inv hτσV.1
      rw [hecoe] at h
      exact h
    exact e.injOn hqU (e.map_target hτσV.1) (h1.trans h2.symm)
  let E : EvChart ψ v a₀ b₀ (fun τ q => (Work.BoxShrink.Pinch.par ψ q) (σi i) =
      (Work.BoxShrink.Pinch.par ψ x₀) (σi i)) τ₀ (hFn ψ v x₀) x₀ :=
    { V := V,
      hVopen := hVopen,
      hVmem := hVmem,
      Ψ := Ψ,
      hΨcd := hΨcd,
      hΨmem := hΨmem,
      hg := hgΨ,
      hσ := hσ,
      hτ := hτ,
      U := U,
      hUopen := e.open_source,
      hUmem := hmem,
      huniq := huniq }
  exact ⟨E⟩

end Work.Drive.Mono
