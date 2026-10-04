import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.KSBP

/-- The second derivative of the one-dimensional slice `s ↦ Ψ (a - s • v)` of a `C²` map `Ψ`.

Indeed, for `g s = Ψ (a - s • v)` one has `g' s = -(DΨ(a - s•v)) v`, so the two sign flips give
`g'' t = (D(DΨ)(a - t•v)) v v`, which is the derivative of `w ↦ (DΨ w) v` at `a - t•v` evaluated
at `v`. -/
private lemma slice_deriv_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E → F) (hΨ : ContDiff ℝ 2 Ψ) (a v : E) (t : ℝ) :
    deriv (deriv (fun s : ℝ => Ψ (a - s • v))) t
      = fderiv ℝ (fun w : E => (fderiv ℝ Ψ w) v) (a - t • v) v := by
  let c : ℝ → E := fun s => a - s • v
  change deriv (deriv (fun s : ℝ => Ψ (c s))) t
      = fderiv ℝ (fun w : E => (fderiv ℝ Ψ w) v) (c t) v
  -- the affine slice has constant velocity `-v`
  have hc : ∀ s, HasDerivAt c (-v) s := fun s => by
    have h : HasDerivAt (fun s : ℝ => a - s • v) ((0 : E) - (1 : ℝ) • v) s :=
      (hasDerivAt_const (x := s) a).sub ((hasDerivAt_id s).smul_const v)
    simpa [c] using h
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  -- `DΨ` is differentiable because `Ψ` is `C²`
  have hfd : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hA : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (c t)) (c t) :=
    (hfd (c t)).hasFDerivAt
  let P : E → F := fun w => (fderiv ℝ Ψ w) (-v)
  -- `deriv (Ψ ∘ c) = P ∘ c`
  have hPg : deriv (fun s : ℝ => Ψ (c s)) = P ∘ c := by
    funext s
    exact ((hΨd (c s)).hasFDerivAt.comp_hasDerivAt s (hc s)).deriv
  -- derivative of `P` at `c t`
  have hDP : HasFDerivAt P ((fderiv ℝ (fderiv ℝ Ψ) (c t)).flip (-v)) (c t) := by
    have h := hA.clm_apply (hasFDerivAt_const (-v) (c t))
    simpa [P] using h
  have hlhs : deriv (deriv (fun s : ℝ => Ψ (c s))) t
      = (fderiv ℝ (fderiv ℝ Ψ) (c t)) (-v) (-v) := by
    have hPg2 : deriv (P ∘ c) t = ((fderiv ℝ (fderiv ℝ Ψ) (c t)).flip (-v)) (-v) :=
      (hDP.comp_hasDerivAt t (hc t)).deriv
    rw [hPg, hPg2, ContinuousLinearMap.flip_apply]
  -- the right hand side
  have hDQ : HasFDerivAt (fun w : E => (fderiv ℝ Ψ w) v)
      ((fderiv ℝ (fderiv ℝ Ψ) (c t)).flip v) (c t) := by
    have h := hA.clm_apply (hasFDerivAt_const v (c t))
    simpa using h
  have hrhs : fderiv ℝ (fun w : E => (fderiv ℝ Ψ w) v) (c t) v
      = (fderiv ℝ (fderiv ℝ Ψ) (c t)) v v := by
    rw [hDQ.fderiv, ContinuousLinearMap.flip_apply]
  rw [hlhs, hrhs]
  -- `(D²Ψ) (-v) (-v) = (D²Ψ) v v` by linearity
  simp [ContinuousLinearMap.map_neg, neg_apply]

theorem deriv_deriv_slice_eq {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Ψ : (Fin n → ℝ) → F) (hΨ : ContDiff ℝ 2 Ψ) (i : Fin n) (z : Fin n → ℝ) (t : ℝ) :
    deriv (deriv (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ)))) t
      = fderiv ℝ (fun w : Fin n → ℝ => fderiv ℝ Ψ w (Pi.single i (1 : ℝ)))
          (z - t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  exact slice_deriv_deriv Ψ hΨ z (Pi.single i (1 : ℝ)) t

end Work.Diff.STE.Lead.KSBP
