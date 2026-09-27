import Mathlib
import Submission.Work.Drive.PushDisc.thetaMapDefs
import Submission.Work.Drive.PushDisc.lensThetaRows
import Submission.Work.Drive.PushDisc.exists_globalDiffeo_of_embedding
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.injOn_nhds_of_compact_euclidean
import Submission.Work.Drive.PushDisc.exists_globalDiffeo_mdl
import Submission.Work.Drive.PushDisc.exists_open_injOn_det_ne

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold

/-!
# The global framing diffeomorphism of the `θ`-assembly

This file proves `Work.Drive.PushDisc.lensThetaGlobal`: the map

    θ (x,y,u,v) = Δ (x,y) + Σᵢ uᵢ • Uᵢ (x,y) + Σⱼ (r vⱼ) • Wⱼ (x,y)
                   + [ S₂ (x, r • v) - Δ (x, c x) - (fderiv ℝ (fun w => S₂ (x,w)) 0) (r • v) ]

of the framing assembly (`thetaMapDefs.lean`) — which is a local diffeomorphism (injective
derivative) and injective on a compact star-convex set `C` containing both the plane tube
(`hCplane`) and the finger tube (`hCfinger`) — agrees with a global `C^∞` diffeomorphism of the
model space on an open neighbourhood `O ⊇ C`.

The proof splits into three pieces.

* `exists_open_injOn_det_ne` (delegated, `exists_open_injOn_det_ne.lean`): given a `C^∞` map `θ`
  whose derivative is injective on a compact star-convex `C ∋ 0` on which `θ` is injective, there
  is an open `O ⊇ C` on which `θ` is injective and on which the determinant of the derivative has
  a *constant sign*.
* `exists_globalDiffeo_mdl` (delegated, `exists_globalDiffeo_mdl.lean`): the model-space form
  (`Mdl k` instead of `EuclideanSpace ℝ (Fin m)`) of `exists_globalDiffeo_of_embedding` — a `C^∞`
  embedding of an open neighbourhood of `C` with *positive* determinant agrees with a global `C^∞`
  diffeomorphism on an open neighbourhood of `C`.
* the present file: if the sign produced by the first lemma is positive one applies the second
  lemma directly; if it is negative one post-composes `θ` with `flipX k`, the linear involution of
  `Mdl k` negating the first coordinate (determinant `-1`), which turns a negative determinant into
  a positive one, and inverts the flip again at the end.
-/

section Helpers

/-- The involution of the model space `Mdl k` negating the first coordinate.  It is a linear
equivalence of determinant `-1`; it is the orientation flip used to repair the sign of the
determinant of `fderiv ℝ θ`. -/
noncomputable def flipX (k : ℕ) : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun ξ := (-ξ.1, ξ.2.1, ξ.2.2.1, ξ.2.2.2)
  invFun ξ := (-ξ.1, ξ.2.1, ξ.2.2.1, ξ.2.2.2)
  left_inv ξ := by ext <;> simp
  right_inv ξ := by ext <;> simp
  map_add' ξ η := by ext <;> simp [add_comm]
  map_smul' a ξ := by ext <;> simp

@[simp] theorem flipX_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    flipX k ξ = (-ξ.1, ξ.2.1, ξ.2.2.1, ξ.2.2.2) := rfl

/-- `flipX` is an involution. -/
theorem flipX_flipX {k : ℕ} (ξ : Work.Drive.Whitney.Mdl k) : flipX k (flipX k ξ) = ξ := by
  simp

/-- The determinant of `flipX` is `-1`. -/
theorem det_flipX (k : ℕ) : ((flipX k).toLinearMap).det = -1 := by
  have h : (flipX k).toLinearMap
      = LinearMap.prodMap ((-1:ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
          (LinearMap.id : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ]
            ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))) :=
    LinearMap.ext (fun ξ => by simp [flipX, LinearMap.prodMap_apply])
  rw [h, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]
  norm_num

/-- `flipX` is smooth. -/
theorem contDiff_flipX (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : Work.Drive.Whitney.Mdl k => flipX k ξ) := by
  have hfun : (fun ξ : Work.Drive.Whitney.Mdl k => flipX k ξ)
      = fun ξ => (-ξ.1, ξ.2.1, ξ.2.2.1, ξ.2.2.2) := rfl
  rw [hfun]
  fun_prop

/-- Post-composition with `flipX` preserves smoothness. -/
theorem contDiff_flipX_comp {k : ℕ} {θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k}
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ => flipX k (θ ξ)) :=
  (contDiff_flipX k).comp hθ

/-- Post-composition with `flipX` preserves injectivity on a set. -/
theorem injOn_flipX_comp {k : ℕ} {θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k}
    {O : Set (Work.Drive.Whitney.Mdl k)} (h : Set.InjOn θ O) :
    Set.InjOn (fun ξ => flipX k (θ ξ)) O := by
  intro x hx y hy hxy
  have h2 : flipX k (flipX k (θ x)) = flipX k (flipX k (θ y)) := congrArg (flipX k) hxy
  simp only [flipX_flipX] at h2
  exact h hx hy h2

/-- The determinant of the derivative of `flipX ∘ θ` is the negative of the determinant of the
derivative of `θ`. -/
theorem det_fderiv_flipX_comp {k : ℕ} (θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (ξ : Work.Drive.Whitney.Mdl k) (hθ : DifferentiableAt ℝ θ ξ) :
    (fderiv ℝ (fun ξ => flipX k (θ ξ)) ξ).toLinearMap.det
      = -((fderiv ℝ θ ξ).toLinearMap.det) := by
  have hfun : (fun ξ : Work.Drive.Whitney.Mdl k => flipX k (θ ξ))
      = fun ξ => (LinearMap.toContinuousLinearMap (flipX k).toLinearMap) (θ ξ) := by
    funext ξ
    show (flipX k) (θ ξ) = (LinearMap.toContinuousLinearMap (flipX k).toLinearMap).toLinearMap (θ ξ)
    rw [LinearMap.coe_toContinuousLinearMap]
    rfl
  rw [hfun]
  have hfd : fderiv ℝ (fun ξ => (LinearMap.toContinuousLinearMap (flipX k).toLinearMap) (θ ξ)) ξ
      = (LinearMap.toContinuousLinearMap (flipX k).toLinearMap).comp (fderiv ℝ θ ξ) := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.hasFDerivAt (LinearMap.toContinuousLinearMap (flipX k).toLinearMap)).comp ξ
        hθ.hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  have h2 : (LinearMap.toContinuousLinearMap (flipX k).toLinearMap).toLinearMap.det = -1 := by
    rw [LinearMap.coe_toContinuousLinearMap]; exact det_flipX k
  rw [h2]; ring

end Helpers

theorem lensThetaGlobal {k : ℕ}
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (X' : ℝ) (hX' : 1 < X') (r : ℝ) (hr : 0 < r)
    (C : Set (Work.Drive.Whitney.Mdl k)) (hC : IsCompact C)
    (hCstar : StarConvex ℝ (0 : Work.Drive.Whitney.Mdl k) C)
    (hCplane : ∀ (x y : ℝ) (u : EuclideanSpace ℝ (Fin k)),
      |x| ≤ X' → 0 ≤ y → y ≤ Work.Drive.PushDisc.arch x → ‖u‖ ≤ 1 → (x, y, u, 0) ∈ C)
    (hCfinger : ∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)),
      |x| ≤ X' → ‖v‖ ≤ 1 → (x, Work.Drive.PushDisc.arch x, 0, v) ∈ C)
    (hInj : Set.InjOn (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) C)
    (hImm : ∀ ξ ∈ C, Function.Injective (fderiv ℝ (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) ξ)) :
    ∃ (Θg Θgi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
      (O : Set (Work.Drive.Whitney.Mdl k)),
      IsOpen O ∧ C ⊆ O ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θg ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θgi ∧
      Function.LeftInverse Θgi Θg ∧ Function.RightInverse Θgi Θg ∧
      (∀ ξ ∈ O, Θg ξ = Work.Drive.PushDisc.thetaMap Δ U W S₂ c r ξ) := by
  classical
  set θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k :=
    Work.Drive.PushDisc.thetaMap Δ U W S₂ c r with hθdef
  -- `θ` is smooth: it is an explicit sum of smooth terms
  have hθsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    rw [hθdef]
    have hfun : Work.Drive.PushDisc.thetaMap Δ U W S₂ c r = (fun ξ : Work.Drive.Whitney.Mdl k =>
        Δ (ξ.1, ξ.2.1) + (∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
          + (∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j)
          + (S₂ (ξ.1, r • ξ.2.2.2) - Δ (ξ.1, c ξ.1)
              - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0)
                  (r • ξ.2.2.2))) := by
      funext ξ; rfl
    rw [hfun]
    fun_prop
  -- the origin lies in `C`: it is the centre of the star-convexity and a point of the plane tube
  have h0C : (0 : Work.Drive.Whitney.Mdl k) ∈ C := by
    have h := hCplane 0 0 0 (by simp only [abs_zero]; linarith) (le_refl 0)
      (by simp [Work.Drive.PushDisc.arch]) (by simp)
    show ((0:ℝ), (0:ℝ), (0:EuclideanSpace ℝ (Fin k)), (0:EuclideanSpace ℝ (Fin k))) ∈ C
    exact h
  -- an open neighbourhood of `C` on which `θ` is injective and the determinant has constant sign
  obtain ⟨O, hO, hCO, hInjO, hsign⟩ := exists_open_injOn_det_ne θ hθsm C hC hCstar h0C hImm hInj
  rcases hsign with hpos | hneg
  · -- the determinant is positive on `O`: apply the model-space globalisation directly
    obtain ⟨Θg, Θgi, hΘg, hΘgi, hl, hr, O', hO', hCO', hOO', hagr⟩ :=
      exists_globalDiffeo_mdl C hC hCstar O hO hCO θ hθsm.contDiffOn hInjO hpos
    exact ⟨Θg, Θgi, O', hO', hCO', hΘg, hΘgi, hl, hr, hagr⟩
  · -- the determinant is negative on `O`: flip the first coordinate, then globalise, then flip back
    have hθ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ => flipX k (θ ξ)) :=
      contDiff_flipX_comp hθsm
    have hInjO' : Set.InjOn (fun ξ => flipX k (θ ξ)) O := injOn_flipX_comp hInjO
    have hpos' : ∀ ξ ∈ O, 0 < (fderiv ℝ (fun ξ => flipX k (θ ξ)) ξ).toLinearMap.det := by
      intro ξ hξ
      rw [det_fderiv_flipX_comp θ ξ ((hθsm.differentiable (by simp)).differentiableAt)]
      linarith [hneg ξ hξ]
    obtain ⟨Θ', Φ', hΘ', hΦ', hl', hr', O', hO', hCO', hOO', hagr⟩ :=
      exists_globalDiffeo_mdl C hC hCstar O hO hCO (fun ξ => flipX k (θ ξ)) hθ'.contDiffOn
        hInjO' hpos'
    refine ⟨fun ξ => flipX k (Θ' ξ), fun ξ => Φ' (flipX k ξ), O', hO', hCO', ?_, ?_, ?_, ?_, ?_⟩
    · exact (contDiff_flipX k).comp hΘ'
    · exact hΦ'.comp (contDiff_flipX k)
    · intro ξ
      change Φ' (flipX k (flipX k (Θ' ξ))) = ξ
      rw [flipX_flipX]
      exact hl' ξ
    · intro ξ
      change flipX k (Θ' (Φ' (flipX k ξ))) = ξ
      rw [hr' (flipX k ξ), flipX_flipX]
    · intro ξ hξ
      change flipX k (Θ' ξ) = θ ξ
      rw [hagr ξ hξ, flipX_flipX]

end Work.Drive.PushDisc
