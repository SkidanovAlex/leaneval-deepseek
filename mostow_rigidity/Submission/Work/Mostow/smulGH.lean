import Mathlib
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.minkTangent
import Submission.Work.Mostow.BusemannDeriv

/-!
# `smulGH`: the `PO n 1`-action preserves the chart metric `gH`

For `g : PO n 1` and `u v : E n`,
`gH (g • u) (fderiv ℝ (fun w => g • w) u v) = gH u v`:
the action of `PO n 1` is a Riemannian isometry of `ℍⁿ = E n`.

The proof is the intrinsic (hyperboloid) one.  Write `A = rep g`, so that `g • w = actO A w`
for all `w` (this is the `POActionProp` clause `(A : PO n 1) • u = actO A u` together with
`Quotient.out_eq'`).  Then

* the chart derivative of `actO A` is the linear action on the *tangent lift* of the vector:
  `fderiv ℝ (fun w => actO A w) u v = spatial (tsign A • (mat A) *ᵥ liftTan u v)`
  (`smul_fderiv_actO`).  This is the chain rule applied to the pointwise identity
  `hlift (actO A w) = tsign A • (mat A) *ᵥ hlift w` (`Hyper.hlift_actO`) and the fact that the
  derivative of `hlift` is `liftTan`.
* the ambient vector `W = tsign A • (mat A) *ᵥ liftTan u v` is Minkowski-tangent to the
  hyperboloid at `hlift (actO A u)`, and the Minkowski form is preserved by `mat A`
  (`Hyper.mink_mulVec`) and by the sign `tsign A` (`Hyper.tsign_mul_self`), so
  `mink_localIsomDefs W W = mink_localIsomDefs (liftTan u v) (liftTan u v) = gH u v`.
* on the tangent space of the hyperboloid the Minkowski form *is* `gH`
  (`Work.Mostow.minkTangent`), hence `gH (actO A u) (spatial W) = gH u v`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The two Minkowski forms -/

/-- `Work.Mostow.mink_localIsomDefs` (explicit sum) and `Submission.Mostow.Hyper.mink` (`J`-matrix form) are the
same bilinear form. -/
theorem mink_eq_hyperMink (x y : Fin n ⊕ Fin 1 → ℝ) : Hyper.mink x y = mink_localIsomDefs x y := by
  rw [Hyper.mink_apply]; rfl

/-- Homogeneity of `mink_localIsomDefs` in both variables. -/
theorem mink_smul' (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs (r • x) (s • y) = r * s * mink_localIsomDefs x y := by
  rw [← mink_eq_hyperMink, Hyper.mink_smul, mink_eq_hyperMink]

/-- `mink_localIsomDefs` is preserved by any `J`-orthogonal matrix. -/
theorem mink_mulVec' (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hM : M.transpose * pmOneMat * M = pmOneMat) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs (M.mulVec x) (M.mulVec y) = mink_localIsomDefs x y := by
  rw [← mink_eq_hyperMink, Hyper.mink_mulVec M hM, mink_eq_hyperMink]

/-- The tangent lift `liftTan u v` is Minkowski-orthogonal to the hyperboloid point `hlift u`. -/
theorem mink_liftTan_hlift (u v : E n) : mink_localIsomDefs (liftTan u v) (hlift u) = 0 := by
  have h1 : mink_localIsomDefs (liftTan u v) (hlift u) = Hyper.mink (liftTan u v) (hlift u) := by
    rw [Hyper.mink_apply]; rfl
  rw [h1, Hyper.mink_apply]
  simp only [liftTan, Sum.elim_inl, Sum.elim_inr, hlift]
  rw [show (∑ i, v i * u i) = ∑ i, u i * v i from Finset.sum_congr rfl fun i _ => by ring]
  rw [← Hyper.inner_eq_sum u v, div_mul_cancel₀ _ (ne_of_gt (Hyper.tpart_pos u)), sub_self]

/-- The Minkowski square of the tangent lift `liftTan u v` is the hyperbolic metric `gH u v`. -/
theorem mink_liftTan_self (u v : E n) : mink_localIsomDefs (liftTan u v) (liftTan u v) = gH u v := by
  have hsum : (∑ i : Fin n, v i * v i) = ‖v‖ ^ 2 := (Hyper.norm_sq_eq_sum v).symm
  rw [mink_localIsomDefs, liftTan, gH]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hsum, ← Hyper.sq_tpart u]
  field_simp

/-! ## The derivative of `actO` -/

/-- The spatial block of `mat A`, as an `n × n` matrix. -/
private def spatBlock (A : O1 n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mat A (Sum.inl i) (Sum.inl j)

/-- The time column of `mat A`, as a vector of the chart space. -/
private def timeCol (A : O1 n) : E n :=
  WithLp.toLp 2 (fun i : Fin n => mat A (Sum.inl i) (Sum.inr 0))

/-- Coordinates of `Matrix.toEuclideanCLM M`: it is the ordinary matrix-vector product. -/
private theorem toEuclideanCLM_apply_ofLp (M : Matrix (Fin n) (Fin n) ℝ) (w : E n) (i : Fin n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M w).ofLp i = ∑ j, M i j * w j := by
  rw [show WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M w)
      = M.mulVec (WithLp.ofLp w) from Matrix.ofLp_toEuclideanCLM M w]
  simp [Matrix.mulVec, dotProduct]

/-- `actO A w = tsign A • (spatBlock A *ᵥ w + tpart w • timeCol A)`: the action of `A` on the
chart is the sign `tsign A` times (the spatial block applied to `w`, plus the time column scaled
by the time coordinate of the lift). -/
private theorem actO_eq_clm (A : O1 n) (w : E n) :
    actO A w = tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) w
      + tpart w • timeCol A) := by
  ext i
  simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply]
  rw [toEuclideanCLM_apply_ofLp (spatBlock A) w i]
  simp only [actO, spatBlock, timeCol, Matrix.mulVec, dotProduct, hlift, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_sum_type, Fin.sum_univ_one, WithLp.ofLp_toLp]
  ring

/-- **Derivative of `actO A`**: the chart derivative at `u`, applied to `v`, is the spatial part of
`tsign A • (mat A) *ᵥ liftTan u v`, i.e. the linear action of `A` on the tangent lift of `v`. -/
theorem smul_fderiv_actO (n : ℕ) (A : O1 n) (u v : E n) :
    fderiv ℝ (fun w : E n => actO A w) u v
      = spatial (tsign A • (mat A).mulVec (liftTan u v)) := by
  have hder : HasFDerivAt (fun w : E n => actO A w)
      (tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) +
        (innerSL ℝ ((tpart u)⁻¹ • u)).smulRight (timeCol A))) u := by
    have h1 : HasFDerivAt (fun w : E n => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
        (spatBlock A) w) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A)) u :=
      ContinuousLinearMap.hasFDerivAt _
    have h2 : HasFDerivAt (fun w : E n => tpart w) (innerSL ℝ ((tpart u)⁻¹ • u)) u :=
      hasFDerivAt_tpart n u
    have h3 := h2.smul_const (timeCol A)
    have h45 : HasFDerivAt
        (fun w : E n => tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) w
          + tpart w • timeCol A))
        (tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) +
          (innerSL ℝ ((tpart u)⁻¹ • u)).smulRight (timeCol A))) u :=
      (h1.add h3).const_smul (tsign A)
    rw [show (fun w : E n => tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
          (spatBlock A) w + tpart w • timeCol A)) = (fun w : E n => actO A w) from
      funext fun w => (actO_eq_clm A w).symm] at h45
    exact h45
  have hL : (tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) +
        (innerSL ℝ ((tpart u)⁻¹ • u)).smulRight (timeCol A))) v
      = tsign A • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) v
          + ((tpart u)⁻¹ * inner ℝ u v) • timeCol A) := by
    simp [innerSL_apply_apply]
  have hE : spatial ((mat A).mulVec (liftTan u v))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (spatBlock A) v
        + ((tpart u)⁻¹ * inner ℝ u v) • timeCol A := by
    ext i
    simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply]
    rw [toEuclideanCLM_apply_ofLp (spatBlock A) v i]
    simp only [spatial, liftTan, spatBlock, timeCol, Matrix.mulVec, dotProduct,
      Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type, Fin.sum_univ_one, WithLp.ofLp_toLp]
    ring
  rw [hder.fderiv, hL, spatial_smul, hE]

/-! ## The main lemma -/

/-- The action of `PO n 1` on the chart preserves the hyperbolic metric `gH`. -/
theorem smulGH (n : ℕ) (hA : POActionProp n) (g : PO n 1) (u v : E n) :
    gH (g • u) (fderiv ℝ (fun w : E n => g • w) u v) = gH u v := by
  set A : O1 n := rep g with hAdef
  have hcoeg : ((A : O1 n) : PO n 1) = g := by rw [hAdef]; exact Quotient.out_eq' g
  have hcoe : ∀ w : E n, g • w = actO A w := by
    intro w
    have h := hA.2.1 A w
    rw [hcoeg] at h
    exact h
  have hfun : (fun w : E n => g • w) = (fun w : E n => actO A w) := funext hcoe
  rw [hfun, hcoe u, smul_fderiv_actO n A u v]
  set W : Fin n ⊕ Fin 1 → ℝ := tsign A • (mat A).mulVec (liftTan u v) with hW
  have htan : mink_localIsomDefs W (hlift (actO A u)) = 0 := by
    rw [hW, Hyper.hlift_actO A u, mink_smul', mink_mulVec' (mat A) (Hyper.mat_conj A),
      Hyper.tsign_mul_self, one_mul, mink_liftTan_hlift]
  have hWW : mink_localIsomDefs W W = gH u v := by
    rw [hW, mink_smul', mink_mulVec' (mat A) (Hyper.mat_conj A), Hyper.tsign_mul_self, one_mul,
      mink_liftTan_self]
  obtain ⟨hm, -⟩ := minkTangent (actO A u) W htan
  rw [← hm]
  exact hWW

end

end Work.Mostow
