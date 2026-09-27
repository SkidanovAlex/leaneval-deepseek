import Mathlib
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.exists_clm_equiv_of_injective
import Submission.Work.Whitney.exists_injOn_ball_of_perturbation

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- Abstract form of the straightening lemma: for a smooth `φ : E → E × E` whose derivative at
`0` is injective, there is a smooth map `H : E × E → E × E` which is injective and an immersion
on a ball around the origin and reproduces `φ` on the axis `v = 0`.

The construction is `H (u, v) = φ u + A v` with `A` a linear map whose image is a complement of
the range of `fderiv ℝ φ 0`: `T := (fderiv ℝ φ 0) ⊕ A : E × E ≃L E × E` is a continuous linear
equivalence by dimension reasons, and with `ψ := T.symm ∘ H` we have `ψ (u,v) = (u,v) + G (u,v)`
where `G` is smooth with `fderiv ℝ G 0 = 0`; the perturbation lemma
`Work.Whitney.exists_injOn_ball_of_perturbation` then gives a ball on which `ψ` and `fderiv ℝ ψ`
are injective, and `H = T ∘ ψ` inherits both properties. -/
theorem exists_tubular_param_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → E × E) (hφ : ContDiff ℝ ⊤ φ) (h0 : Function.Injective (fderiv ℝ φ 0)) :
    ∃ (H : E × E → E × E) (ρ : ℝ), 0 < ρ ∧ ContDiff ℝ ⊤ H ∧
      (∀ u : E, H (u, 0) = φ u) ∧ Set.InjOn H (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z)) := by
  classical
  let L : E →L[ℝ] E × E := fderiv ℝ φ 0
  have hL : Function.Injective L := h0
  have hfin : Module.finrank ℝ (E × E) = Module.finrank ℝ E + Module.finrank ℝ E :=
    Module.finrank_prod
  obtain ⟨T, hT⟩ := exists_clm_equiv_of_injective L hL hfin
  -- The straightened map `ψ = T.symm ∘ H`, where `H (u,v) = φ u + T (0,v)`.
  let ψ : E × E → E × E := fun z => T.symm (φ z.1) + (0, z.2)
  let G : E × E → E × E := fun z => T.symm (φ z.1) - (z.1, 0)
  have hψG : ∀ z, ψ z = z + G z := by
    intro z
    have hz : (((0:E), z.2) : E × E) = z - ((z.1 : E), (0:E)) := by ext <;> simp
    simp only [ψ, G]
    rw [hz]
    abel
  have hψsm : ContDiff ℝ ⊤ ψ := by
    have h1 : ContDiff ℝ ⊤ (fun z : E × E => T.symm (φ z.1)) :=
      (T.symm : E × E →L[ℝ] E × E).contDiff.comp (hφ.comp contDiff_fst)
    have h2 : ContDiff ℝ ⊤ (fun z : E × E => ((0:E), z.2)) := contDiff_const.prodMk contDiff_snd
    exact h1.add h2
  have hGsm : ContDiff ℝ ⊤ G := by
    have h1 : ContDiff ℝ ⊤ (fun z : E × E => T.symm (φ z.1)) :=
      (T.symm : E × E →L[ℝ] E × E).contDiff.comp (hφ.comp contDiff_fst)
    have h2 : ContDiff ℝ ⊤ (fun z : E × E => ((z.1 : E), (0:E))) :=
      contDiff_fst.prodMk contDiff_const
    exact h1.sub h2
  have hG0 : fderiv ℝ G 0 = 0 := by
    have hne0 : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
    have hA : HasFDerivAt (fun z : E × E => T.symm (φ z.1))
        ((T.symm : E × E →L[ℝ] E × E).comp (L.comp (ContinuousLinearMap.fst ℝ E E))) 0 := by
      have hφd : HasFDerivAt φ L (0:E) :=
        ((hφ.differentiable hne0).differentiableAt (x := 0)).hasFDerivAt
      have hfst : HasFDerivAt (fun z : E × E => z.1) (ContinuousLinearMap.fst ℝ E E) (0:E × E) :=
        hasFDerivAt_fst
      exact ((ContinuousLinearMap.hasFDerivAt (T.symm : E × E →L[ℝ] E × E)).comp 0
        (hφd.comp 0 hfst))
    have hB : HasFDerivAt (fun z : E × E => ((z.1 : E), (0:E)))
        ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E)) 0 := by
      have h := ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E)) (x := (0:E × E))
      have hfun : (fun z : E × E => ((z.1 : E), (0:E)))
          = (fun z => ((ContinuousLinearMap.inl ℝ E E).comp
              (ContinuousLinearMap.fst ℝ E E)) z) := by
        funext z; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]; rfl
      rw [hfun]; exact h
    have hAB := hA.sub hB
    have hTsymmL : (T.symm : E × E →L[ℝ] E × E).comp L = ContinuousLinearMap.inl ℝ E E := by
      refine ContinuousLinearMap.ext fun u => ?_
      rw [ContinuousLinearMap.comp_apply, ← hT u]; simp
    have hkey : (T.symm : E × E →L[ℝ] E × E).comp (L.comp (ContinuousLinearMap.fst ℝ E E))
        = (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E) := by
      rw [← ContinuousLinearMap.comp_assoc, hTsymmL]
    have h2 : fderiv ℝ G 0 = fderiv ℝ ((fun z : E × E => T.symm (φ z.1))
        - (fun z : E × E => ((z.1 : E), (0:E)))) 0 := by
      congr 1
    rw [h2, hAB.fderiv, hkey, sub_self]
  obtain ⟨ρ, hρ, hinjψ, hfdψ⟩ := exists_injOn_ball_of_perturbation ψ G hψG hGsm hG0
  -- The straightened map we return.
  let H : E × E → E × E := fun z => (T : E × E →L[ℝ] E × E) (ψ z)
  refine ⟨H, ρ, hρ, ?_, ?_, ?_, ?_⟩
  · have hh : ContDiff ℝ ⊤ (fun z : E × E => (T : E × E →L[ℝ] E × E) (ψ z)) :=
      (T : E × E →L[ℝ] E × E).contDiff.comp hψsm
    simpa only [H] using hh
  · intro u
    simp only [H, ψ]
    simp
  · intro z1 h1 z2 h2 h
    exact hinjψ h1 h2 (T.injective h)
  · intro z hz
    have hne0 : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
    have hTinj : Function.Injective (T : E × E →L[ℝ] E × E) :=
      fun a b h => T.injective (by simpa using h)
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
      ((hψsm.contDiffAt).differentiableAt hne0).hasFDerivAt
    have hcomp := (ContinuousLinearMap.hasFDerivAt (T : E × E →L[ℝ] E × E)).comp z hψd
    have hfdz : fderiv ℝ H z = (T : E × E →L[ℝ] E × E).comp (fderiv ℝ ψ z) := by
      rw [show H = ((T : E × E →L[ℝ] E × E) ∘ ψ) from rfl]
      exact hcomp.fderiv
    rw [hfdz]
    intro a b hab
    exact (hfdψ z hz) (hTinj (by simpa only [ContinuousLinearMap.comp_apply] using hab))

/-- A chart representation `φ : ℝⁿ → ℝⁿ × ℝⁿ` of an immersion can be "straightened" by a tubular neighbourhood parametrisation: there is a smooth `H` which is injective and an immersion on a ball around the origin and which reproduces `φ` on the axis `v = 0`, i.e. `H (u, 0) = φ u` for all `u`.  (Here `u` runs along the image of `φ` and `v` along a complement of its tangent image.  A clean construction: choose a linear `A : ℝⁿ → ℝⁿ × ℝⁿ` whose image is a complement of the image of `fderiv ℝ φ 0` and set `H (u, v) = φ u + A v`; then `fderiv ℝ H (0,0)` is the block map `(u',v') ↦ fderiv ℝ φ 0 u' + A v'`, which is injective, so the inverse function result applies.)  This is the local form of the tubular neighbourhood result needed to glue a local model into an immersion. -/
theorem exists_tubular_param (n : ℕ) (φ : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hφ : ContDiff ℝ ⊤ φ) (h0 : Function.Injective (fderiv ℝ φ 0)) :
    ∃ (H : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ρ : ℝ), 0 < ρ ∧
      ContDiff ℝ ⊤ H ∧
      (∀ u : Fin n → ℝ, H (u, 0) = φ u) ∧
      Set.InjOn H (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z)) :=
  exists_tubular_param_general φ hφ h0

end Work.Whitney
