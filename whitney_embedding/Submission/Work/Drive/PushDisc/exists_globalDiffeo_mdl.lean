import Mathlib
import Submission.Work.Drive.PushDisc.exists_globalDiffeo_of_embedding
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Drive.Whitney.modelChart

/-!
# The global diffeomorphism extension on the model space `Mdl k`

`Work.Drive.PushDisc.exists_globalDiffeo_of_embedding` proves, on a Euclidean space `ℝ^m`, that a
`C^∞` embedding `θ` of an open set `O` with everywhere positive determinant extends to a global
`C^∞` diffeomorphism, agreeing with `θ` on an open neighbourhood of a compact star-convex set
`C ⊆ O`.  The model space of the Whitney move, `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`, is only a *product*
of Euclidean spaces (with the sup norm), not a Euclidean space itself.  This file transports the
theorem to `Mdl k` along a linear equivalence `e : Mdl k ≃L[ℝ] ℝ^{2(k+1)}`: the conjugated map
`e ∘ θ ∘ e⁻¹` is again a `C^∞` embedding with positive determinant on the image of `O` (the
determinant is unchanged, being a conjugate), and the resulting global diffeomorphism is conjugated
back.
-/

namespace Work.Drive.PushDisc

open Set

/-- **The global diffeomorphism extension, on the model space `Mdl k`.**  If `C` is compact and
star-convex about `0`, `C ⊆ O` is open, and `θ` is a `C^∞` embedding of `O` with everywhere
positive determinant, then `θ` agrees with a global `C^∞` diffeomorphism `Θ` of `Mdl k` (with
inverse `Φ`) on an open neighbourhood of `C`. -/
theorem exists_globalDiffeo_mdl {k : ℕ}
    (C : Set (Work.Drive.Whitney.Mdl k)) (hC : IsCompact C)
    (hCstar : StarConvex ℝ (0 : Work.Drive.Whitney.Mdl k) C)
    (O : Set (Work.Drive.Whitney.Mdl k)) (hO : IsOpen O) (hCO : C ⊆ O)
    (θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O) (hθinj : Set.InjOn θ O)
    (hθdet : ∀ ξ ∈ O, 0 < (fderiv ℝ θ ξ).toLinearMap.det) :
    ∃ Θ Φ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      Function.LeftInverse Φ Θ ∧ Function.RightInverse Φ Θ ∧
      ∃ O' : Set (Work.Drive.Whitney.Mdl k), IsOpen O' ∧ C ⊆ O' ∧ O' ⊆ O ∧
        ∀ ξ ∈ O', Θ ξ = θ ξ := by
  classical
  -- the linear equivalence from the model space to a Euclidean space of the same dimension
  let e : (Work.Drive.Whitney.Mdl k) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (LinearEquiv.ofFinrankEq (Work.Drive.Whitney.Mdl k)
      (EuclideanSpace ℝ (Fin (2 * (k + 1))))
      (by rw [finrank_Mdl, finrank_euclideanSpace, Fintype.card_fin])).toContinuousLinearEquiv
  -- the images of `C` and `O`, and the conjugated map
  have hC' : IsCompact (e '' C) := hC.image e.continuous
  have hCstar' : StarConvex ℝ (0 : EuclideanSpace ℝ (Fin (2 * (k + 1)))) (e '' C) := by
    have h := hCstar.linear_image
      (e.toLinearEquiv : Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
    simpa using h
  have hO' : IsOpen (e '' O) := e.isOpenMap O hO
  have hCO' : e '' C ⊆ e '' O := Set.image_mono hCO
  let θ' : EuclideanSpace ℝ (Fin (2 * (k + 1))) → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    fun y => e (θ (e.symm y))
  -- smoothness of the conjugated map
  have hθ'sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ' (e '' O) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * (k + 1))) => e.symm y) (e '' O) :=
      (e.symm.contDiff).contDiffOn
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * (k + 1))) => θ (e.symm y)) (e '' O) :=
      hθ.comp h1 (by rintro y ⟨z, hz, rfl⟩; simpa using hz)
    have h3 := ((e : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1)))).contDiff).contDiffOn.comp
      h2 (fun y _ => Set.mem_univ (θ (e.symm y)))
    simpa [θ', Function.comp_def] using h3
  -- injectivity of the conjugated map
  have hθ'inj : Set.InjOn θ' (e '' O) := by
    rintro y ⟨z, hz, rfl⟩ y₂ ⟨z₂, hz₂, rfl⟩ h
    have h1 : θ z = θ z₂ := by
      have h' := congrArg (fun w : EuclideanSpace ℝ (Fin (2 * (k + 1))) => e.symm w) h
      simpa [θ', ContinuousLinearEquiv.symm_apply_apply] using h'
    have h2 : z = z₂ := hθinj hz hz₂ h1
    rw [h2]
  -- positivity of the determinant of the conjugated map: the determinant is a conjugation invariant
  have hθ'det : ∀ ξ ∈ e '' O, 0 < (fderiv ℝ θ' ξ).toLinearMap.det := by
    rintro _ ⟨z, hzO, rfl⟩
    have hθat : HasFDerivAt θ (fderiv ℝ θ z) z :=
      ((hθ.contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp)).hasFDerivAt
    have hsymm : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (2 * (k + 1))) => e.symm y)
        ((e.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k)) (e z) :=
      (e.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k).hasFDerivAt
    have hθat' : HasFDerivAt θ (fderiv ℝ θ z) (e.symm (e z)) := by
      simpa [ContinuousLinearEquiv.symm_apply_apply] using hθat
    have hcomp := hθat'.comp (e z) hsymm
    have hmain : HasFDerivAt θ'
        ((e : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
          ∘L ((fderiv ℝ θ z)
            ∘L (e.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k)))
        (e z) := by
      have h2 := (e : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1)))).hasFDerivAt.comp
        (e z) hcomp
      simpa [θ', Function.comp_def] using h2
    rw [hmain.fderiv]
    have hLM : (((e : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
          ∘L ((fderiv ℝ θ z)
            ∘L (e.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k))).toLinearMap)
        = (e.toLinearEquiv : Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
            ∘ₗ (fderiv ℝ θ z).toLinearMap
            ∘ₗ (e.toLinearEquiv.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →ₗ[ℝ] Work.Drive.Whitney.Mdl k) := by
      ext v
      rfl
    rw [hLM, LinearMap.det_conj _ e.toLinearEquiv]
    exact hθdet z hzO
  -- the global diffeomorphism on the Euclidean space, and its inverse
  obtain ⟨Θ', Φ', hΘ'sm, hΦ'sm, hleft', hright', Oe, hOe, hCOe, hOeO', hagree⟩ :=
    exists_globalDiffeo_of_embedding (ξ₀ := (0 : EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (e '' C) hC' hCstar' (e '' O) hO' hCO' θ' hθ'sm hθ'inj hθ'det
  refine ⟨fun ξ => e.symm (Θ' (e ξ)), fun ξ => e.symm (Φ' (e ξ)), ?_, ?_, ?_, ?_,
    e.symm '' Oe, e.symm.isOpenMap Oe hOe, ?_, ?_, ?_⟩
  · exact (e.symm.contDiff).comp (hΘ'sm.comp e.contDiff)
  · exact (e.symm.contDiff).comp (hΦ'sm.comp e.contDiff)
  · intro ξ
    change e.symm (Φ' (e (e.symm (Θ' (e ξ))))) = ξ
    rw [ContinuousLinearEquiv.apply_symm_apply, hleft' (e ξ),
      ContinuousLinearEquiv.symm_apply_apply]
  · intro ξ
    change e.symm (Θ' (e (e.symm (Φ' (e ξ))))) = ξ
    rw [ContinuousLinearEquiv.apply_symm_apply, hright' (e ξ),
      ContinuousLinearEquiv.symm_apply_apply]
  · rintro ξ hξ
    exact ⟨e ξ, hCOe ⟨ξ, hξ, rfl⟩, e.symm_apply_apply ξ⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hOeO' hy
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hz
  · rintro ξ ⟨y, hy, rfl⟩
    have h := hagree y hy
    simp only [θ'] at h
    change e.symm (Θ' (e (e.symm y))) = θ (e.symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply, h, ContinuousLinearEquiv.symm_apply_apply]

end Work.Drive.PushDisc
