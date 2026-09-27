import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# Coordinate linear maps on the model space `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`

Auxiliary definitions and lemmas for `Work.Drive.PushDisc.lensThetaRows`: the coordinate
projections of the model space as continuous linear maps, together with their evaluation rules,
and the derivative of a coordinate of a smooth family on the `(x,y)`-plane.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff

section CoordCLM

variable {k : ℕ}

/-- The `x`-coordinate of the model space. -/
noncomputable def prX : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)))

/-- The `y`-coordinate of the model space. -/
noncomputable def prY : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))))

/-- The pair of the two `ℝ^k`-coordinates. -/
noncomputable def prUV : Work.Drive.Whitney.Mdl k →L[ℝ]
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))))

/-- The `u`-coordinate of the model space. -/
noncomputable def prU : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).comp prUV

/-- The `v`-coordinate of the model space. -/
noncomputable def prV : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).comp prUV

/-- The `i`-th coordinate of the `u`-block. -/
noncomputable def coU (i : Fin k) : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin k => ℝ) i).comp prU

/-- The `j`-th coordinate of the `v`-block. -/
noncomputable def coV (j : Fin k) : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin k => ℝ) j).comp prV

@[simp] theorem prX_apply (ξ : Work.Drive.Whitney.Mdl k) : prX ξ = ξ.1 := rfl

@[simp] theorem prY_apply (ξ : Work.Drive.Whitney.Mdl k) : prY ξ = ξ.2.1 := rfl

@[simp] theorem prU_apply (ξ : Work.Drive.Whitney.Mdl k) : prU ξ = ξ.2.2.1 := rfl

@[simp] theorem prV_apply (ξ : Work.Drive.Whitney.Mdl k) : prV ξ = ξ.2.2.2 := rfl

@[simp] theorem coU_apply (ξ : Work.Drive.Whitney.Mdl k) (i : Fin k) : coU i ξ = ξ.2.2.1 i := by
  simp only [coU, ContinuousLinearMap.comp_apply, prU_apply, PiLp.proj_apply]

@[simp] theorem coV_apply (ξ : Work.Drive.Whitney.Mdl k) (j : Fin k) : coV j ξ = ξ.2.2.2 j := by
  simp only [coV, ContinuousLinearMap.comp_apply, prV_apply, PiLp.proj_apply]

/-- The projection `(x,y,u,v) ↦ (x,y)`. -/
noncomputable def piXY : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ × ℝ := prX.prod prY

/-- The map `(x,y,u,v) ↦ (x, r • v)`. -/
noncomputable def kapV (r : ℝ) : Work.Drive.Whitney.Mdl k →L[ℝ] ℝ × EuclideanSpace ℝ (Fin k) :=
  prX.prod (r • prV)

/-- The map `(x,y,u,v) ↦ (x, y, v)`. -/
noncomputable def rhoXYV : Work.Drive.Whitney.Mdl k →L[ℝ]
    (ℝ × (ℝ × EuclideanSpace ℝ (Fin k))) := prX.prod (prY.prod prV)

/-- The derivative of a coordinate of a smooth family on the `(x,y)`-plane. -/
theorem hasFDerivAt_coord (U : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U) (x y : ℝ) (i : Fin k) :
    HasFDerivAt (fun q : ℝ × ℝ => U q i)
      ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ U (x,y))) (x,y) := by
  have hdU : HasFDerivAt U (fderiv ℝ U (x,y)) (x,y) :=
    (hU.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun u : Fin k → Work.Drive.Whitney.Mdl k => u i)
      (ContinuousLinearMap.proj (R := ℝ) i) (U (x,y)) := by
    convert (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) i)
      : HasFDerivAt (ContinuousLinearMap.proj (R := ℝ) i) _ (U (x,y))) using 1
    funext u
    exact (ContinuousLinearMap.proj_apply i u).symm
  exact h1.comp (x,y) hdU

/-- Derivative of the `u`-frame term of `θ` at a point of the plane `{u = 0, v = 0}`. -/
theorem hasFDerivAt_usum (U : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U) (x y : ℝ) :
    HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => ∑ i : Fin k, ξ.2.2.1 i • U (ξ.1,ξ.2.1) i)
      (∑ i : Fin k, (coU i).smulRight (U (x,y) i)) (x,y,0,0) := by
  have key : HasFDerivAt
      (Finset.univ.sum (fun i : Fin k =>
        fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.1 i • U (ξ.1,ξ.2.1) i))
      (Finset.univ.sum (fun i : Fin k => (coU i).smulRight (U (x,y) i))) (x,y,0,0) :=
    HasFDerivAt.sum (fun i _ => by
      have hci : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.1 i) (coU i)
          (x,y,0,0) := by
        convert (coU i).hasFDerivAt using 1
        funext ξ
        simp
      have h2 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => U (ξ.1,ξ.2.1) i)
          (((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ U (x,y))) ∘SL piXY)
          (x,y,0,0) :=
        (hasFDerivAt_coord U hU x y i).comp (x,y,0,0) (ContinuousLinearMap.hasFDerivAt piXY)
      have hs := hci.smul h2
      have hz : ((x,y,0,0) : Work.Drive.Whitney.Mdl k).2.2.1 i = 0 := by simp
      convert hs using 1
      all_goals first | (funext ξ; simp [hz]) | (rw [hz]; simp))
  convert key using 1
  funext ξ
  simp only [Finset.sum_apply]

/-- The `v`-slot partial derivative of a smooth family `S₂` at `v = 0`, as a linear map. -/
noncomputable def sndDeriv (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (x : ℝ) : EuclideanSpace ℝ (Fin k) →L[ℝ] Work.Drive.Whitney.Mdl k :=
  fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0

@[simp] theorem kapV_apply (r : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    kapV r ξ = (ξ.1, r • ξ.2.2.2) := rfl

@[simp] theorem piXY_apply (ξ : Work.Drive.Whitney.Mdl k) : piXY ξ = (ξ.1, ξ.2.1) := rfl

@[simp] theorem rhoXYV_apply (ξ : Work.Drive.Whitney.Mdl k) : rhoXYV ξ = (ξ.1, ξ.2.1, ξ.2.2.2) := rfl

/-- `sndDeriv S₂` is smooth when `S₂` is. -/
theorem contDiff_sndDeriv (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sndDeriv S₂) := by
  have hunc : Function.uncurry
      (fun (x' : ℝ) (w : EuclideanSpace ℝ (Fin k)) => S₂ (x', w)) = S₂ := by
    funext p
    obtain ⟨a, b⟩ := p
    rfl
  have h := ContDiff.fderiv (𝕜 := ℝ) (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun (x' : ℝ) (w : EuclideanSpace ℝ (Fin k)) => S₂ (x', w))
    (g := fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin k)))
    (by rw [hunc]; exact hS₂) contDiff_const (by simp)
  have hfun : (fun x : ℝ => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
      = sndDeriv S₂ := by
    funext x
    rfl
  rw [hfun] at h
  exact h

/-- The chain rule in the `v`-slot: `fderiv` of the `v`-slice is the `inr`-restriction. -/
theorem sndDeriv_eq_comp_inr (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂) (x : ℝ) :
    sndDeriv S₂ x = (fderiv ℝ S₂ (x, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
  have hS₂x : HasFDerivAt S₂ (fderiv ℝ S₂ (x, 0)) (x, 0) :=
    (hS₂.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin k) => (x, w))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) (0 : EuclideanSpace ℝ (Fin k)) :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) x (0 : EuclideanSpace ℝ (Fin k))
  have h2 := hS₂x.comp (0 : EuclideanSpace ℝ (Fin k)) h1
  have h3 := h2.fderiv
  have hL : sndDeriv S₂ x
      = fderiv ℝ (S₂ ∘ (fun w : EuclideanSpace ℝ (Fin k) => (x, w))) 0 := rfl
  rw [hL, h3]

/-- The chain rule in the `x`-slot of the arch curve `x ↦ Δ (x, c x)`, using `hS₂0`. -/
theorem fderiv_arch_eq_comp_inl (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hS₂0 : ∀ x : ℝ, S₂ (x, 0) = Δ (x, c x)) (x : ℝ) :
    fderiv ℝ (fun x' : ℝ => Δ (x', c x')) x
      = (fderiv ℝ S₂ (x, 0)).comp (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
  have hfun : (fun x' : ℝ => Δ (x', c x')) = (fun x' : ℝ => S₂ (x', 0)) := by
    funext x'
    exact (hS₂0 x').symm
  rw [hfun]
  have hS₂x : HasFDerivAt S₂ (fderiv ℝ S₂ (x, 0)) (x, 0) :=
    (hS₂.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun x' : ℝ => (x', (0 : EuclideanSpace ℝ (Fin k))))
      (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) x :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) x (0 : EuclideanSpace ℝ (Fin k))
  have h2 := hS₂x.comp x h1
  have h3 := h2.fderiv
  simpa [Function.comp_def] using h3

/-- Derivative of the `Δ`-term of `θ` at a point of the plane `{u = 0, v = 0}`. -/
theorem hasFDerivAt_delta (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ) (x y : ℝ) :
    HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => Δ (ξ.1, ξ.2.1))
      ((fderiv ℝ Δ (x,y)).comp piXY) (x,y,0,0) := by
  have hd : HasFDerivAt Δ (fderiv ℝ Δ (x,y)) (x,y) :=
    (hΔ.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasFDerivAt (Δ ∘ piXY) ((fderiv ℝ Δ (x,y)) ∘SL piXY)
      ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
    hd.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k) (ContinuousLinearMap.hasFDerivAt piXY)
  exact hcomp

/-- Derivative of the `v`-frame term of `θ` at a point of the plane `{u = 0, v = 0}`. -/
theorem hasFDerivAt_vsum (W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (r : ℝ) (x y : ℝ) :
    HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
        ∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1,ξ.2.1) j)
      (∑ j : Fin k, (r • coV j).smulRight (W (x,y) j)) (x,y,0,0) := by
  have key : HasFDerivAt
      (Finset.univ.sum (fun j : Fin k =>
        fun ξ : Work.Drive.Whitney.Mdl k => (r * ξ.2.2.2 j) • W (ξ.1,ξ.2.1) j))
      (Finset.univ.sum (fun j : Fin k => (r • coV j).smulRight (W (x,y) j))) (x,y,0,0) :=
    HasFDerivAt.sum (fun j _ => by
      have hcj : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => r * ξ.2.2.2 j)
          (r • coV j) (x,y,0,0) := by
        convert (ContinuousLinearMap.hasFDerivAt (r • coV j)) using 1
        funext ξ
        simp
      have h2 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => W (ξ.1,ξ.2.1) j)
          (((ContinuousLinearMap.proj (R := ℝ) j).comp (fderiv ℝ W (x,y))) ∘SL piXY)
          (x,y,0,0) :=
        (hasFDerivAt_coord W hW x y j).comp (x,y,0,0) (ContinuousLinearMap.hasFDerivAt piXY)
      have hs := hcj.smul h2
      have hz : ((x,y,0,0) : Work.Drive.Whitney.Mdl k).2.2.2 j = 0 := by simp
      convert hs using 1
      all_goals first | (funext ξ; simp [hz]) | (rw [hz]; simp))
  convert key using 1
  funext ξ
  simp only [Finset.sum_apply]

/-- The bracket of `θ` has zero derivative on the plane `{u = 0, v = 0}`. -/
theorem hasFDerivAt_bracket (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hS₂0 : ∀ x : ℝ, S₂ (x, 0) = Δ (x, c x)) (r : ℝ) (x y : ℝ) :
    HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
        S₂ (ξ.1, r • ξ.2.2.2) - Δ (ξ.1, c ξ.1)
          - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0) (r • ξ.2.2.2))
      (0 : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) (x,y,0,0) := by
  have hB1 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => S₂ (ξ.1, r • ξ.2.2.2))
      ((fderiv ℝ S₂ (x,0)).comp (kapV r)) (x,y,0,0) := by
    have hpt : (kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) = (x, 0) := by
      simp [kapV_apply]
    have hd : HasFDerivAt S₂ (fderiv ℝ S₂ ((kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k)))
        ((kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k)) := by
      rw [hpt]
      exact (hS₂.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have hcomp := hd.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k)
      (ContinuousLinearMap.hasFDerivAt (kapV r))
    rw [hpt] at hcomp
    exact hcomp
  have hB2 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => Δ (ξ.1, c ξ.1))
      ((fderiv ℝ (fun x' : ℝ => Δ (x', c x')) x).comp prX) (x,y,0,0) := by
    have hdΔ : DifferentiableAt ℝ Δ (x, c x) := hΔ.contDiffAt.differentiableAt (by simp)
    have hdc : DifferentiableAt ℝ c x := hc.contDiffAt.differentiableAt (by simp)
    have hd : DifferentiableAt ℝ (fun x' : ℝ => Δ (x', c x')) x :=
      hdΔ.comp x (differentiableAt_id.prodMk (hdc.comp x differentiableAt_id))
    have hcomp : HasFDerivAt ((fun x' : ℝ => Δ (x', c x')) ∘ prX)
        ((fderiv ℝ (fun x' : ℝ => Δ (x', c x')) x) ∘SL prX)
        ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
      hd.hasFDerivAt.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k)
        (ContinuousLinearMap.hasFDerivAt prX)
    exact hcomp
  have hB3 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
        (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0) (r • ξ.2.2.2))
      ((sndDeriv S₂ x).comp (r • prV)) (x,y,0,0) := by
    have hΛ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sndDeriv S₂) := contDiff_sndDeriv S₂ hS₂
    have hdΛ : DifferentiableAt ℝ (sndDeriv S₂) x :=
      (hΛ.differentiable (by simp)).differentiableAt
    have hcl : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => sndDeriv S₂ ξ.1)
        ((fderiv ℝ (sndDeriv S₂) x).comp prX) (x,y,0,0) := by
      have hcomp : HasFDerivAt (sndDeriv S₂ ∘ prX)
          ((fderiv ℝ (sndDeriv S₂) x) ∘SL prX) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
        hdΛ.hasFDerivAt.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k)
          (ContinuousLinearMap.hasFDerivAt prX)
      exact hcomp
    have hu : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => r • ξ.2.2.2)
        (r • prV) (x,y,0,0) := by
      have hcomp : HasFDerivAt (r • prV) (r • prV) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
        ContinuousLinearMap.hasFDerivAt (r • prV)
      exact hcomp
    have h3 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
          sndDeriv S₂ ξ.1 (r • prV ξ)) ((sndDeriv S₂ x).comp (r • prV)) (x,y,0,0) := by
      have h := hcl.clm_apply hu
      have hderiv : (sndDeriv S₂ x) ∘SL (r • prV)
          + ((fderiv ℝ (sndDeriv S₂) x).comp prX).flip
              ((r • prV) ((x,y,0,0) : Work.Drive.Whitney.Mdl k))
          = (sndDeriv S₂ x).comp (r • prV) := by
        simp
      exact h.congr_fderiv hderiv
    exact h3
  have hD := (hB1.sub hB2).sub hB3
  have hzero : ((fderiv ℝ S₂ (x, 0)).comp (kapV r))
      - ((fderiv ℝ (fun x' : ℝ => Δ (x', c x')) x).comp prX)
      - ((sndDeriv S₂ x).comp (r • prV)) = 0 := by
    have hk : kapV r = (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp prX
        + (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp (r • prV) := by
      apply ContinuousLinearMap.ext
      intro ξ
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, kapV_apply,
        smul_apply, prV_apply, prX_apply]
      ext <;> simp
    rw [hk, fderiv_arch_eq_comp_inl Δ S₂ c hS₂ hS₂0 x, sndDeriv_eq_comp_inr S₂ hS₂ x,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc]
    abel
  rw [hzero] at hD
  exact hD

/-- Appending two coefficient families and two frame families: the sum splits. -/
theorem sum_fin_append_smul {m n : ℕ} {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (g₁ : Fin m → ℝ) (g₂ : Fin n → ℝ) (F₁ : Fin m → α) (F₂ : Fin n → α) :
    ∑ i : Fin (m + n), (Fin.append g₁ g₂ i) • (Fin.append F₁ F₂ i)
      = ∑ i : Fin m, g₁ i • F₁ i + ∑ i : Fin n, g₂ i • F₂ i := by
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left, Fin.append_left])
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_right, Fin.append_right])

end CoordCLM

end Work.Drive.PushDisc
