import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.PressureOn.materialDeriv_eq_gradient_sub_cross

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.FTS.PressureOn.CurlGrad

open FiniteTimeSingularity Work.FTS.PressureOn

/-! ## The `Fin 3 → ℝ` cores

Writing `eᵢ = Pi.single i 1` for the standard basis of `Fin 3 → ℝ`, both sides below are
polynomial identities in the matrix entries of the linear map `B` and the coordinates of the
vector `a` (resp. `w`), so `ring` closes them after the two finite sums over `Fin 3` are expanded
and the cross-product components are unfolded by `cross_apply`. -/

/-- **The left core**: `∑ᵢ ⟪(B eᵢ) × a, eᵢ⟫ = ⟪∑ᵢ eᵢ × (B eᵢ), a⟫`. -/
private theorem cross_curl_left_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, (crossProduct (B (Pi.single i (1 : ℝ))) a) i)
      = ∑ r : Fin 3,
        (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (B (Pi.single i (1 : ℝ)))) r * a r := by
  simp only [Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- **The right core**: `∑ᵢ ⟪w, eᵢ × (B eᵢ)⟫ = -⟪w, ∑ᵢ eᵢ × (B eᵢ)⟫`. -/
private theorem cross_curl_right_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (w : Fin 3 → ℝ) :
    (∑ i : Fin 3, (crossProduct w (B (Pi.single i (1 : ℝ)))) i)
      = -∑ r : Fin 3,
        w r * (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (B (Pi.single i (1 : ℝ)))) r := by
  simp only [Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- `∑ᵢ (D eᵢ × a)ᵢ = ⟪curl D, a⟫`: the diagonal entries of the matrix `i ↦ D eᵢ × a` sum to the
inner product with the curl of the linear field `D`. -/
private theorem sum_diag_crossVec_left (D : R3 →L[ℝ] R3) (a : R3) :
    ∑ i : Fin 3, (crossVec (D (e i)) a).ofLp i = inner ℝ (curlVec D) a := by
  rw [inner_eq_sum]
  have h1 : (∑ i : Fin 3, (crossVec (D (e i)) a).ofLp i)
      = ∑ i : Fin 3, (crossProduct (conjLin D (Pi.single i (1 : ℝ))) a.ofLp) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [h1]
  exact cross_curl_left_core (conjLin D) a.ofLp

/-- `∑ᵢ (w × D eᵢ)ᵢ = -⟪w, curl D⟫`. -/
private theorem sum_diag_crossVec_right (D : R3 →L[ℝ] R3) (w : R3) :
    ∑ i : Fin 3, (crossVec w (D (e i))).ofLp i = -inner ℝ w (curlVec D) := by
  rw [inner_eq_sum]
  have h1 : (∑ i : Fin 3, (crossVec w (D (e i))).ofLp i)
      = ∑ i : Fin 3, (crossProduct w.ofLp (conjLin D (Pi.single i (1 : ℝ)))) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [h1]
  exact cross_curl_right_core (conjLin D) w.ofLp

/-- **The divergence of a cross product.**  For fields `F G : ℝ³ → ℝ³` differentiable at `x`,
`div (F ⨯ G) x = ⟪curl F x, G x⟫ - ⟪F x, curl G x⟫`, where `div` is the trace of the Fréchet
derivative (`FiniteTimeSingularity.div`), `vorticity` is the curl
(`FiniteTimeSingularity.vorticity`) and `crossVec a b = WithLp.toLp 2 (a ⨯₃ b)`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.div_crossVec_eq`.

Proof hints (all available in this workspace): `Work.FTS.PressureOn.vorticityCross_div_eq_sum_diag`
(`div g x = ∑ i, (fderiv ℝ g x (e i)) i`), `Work.FTS.PressureOn.vorticityCross_fderiv_crossVec_apply`
(the product rule `fderiv ℝ (fun y => crossVec (F y) (G y)) x (e i) =
crossVec (fderiv ℝ F x (e i)) (G x) + crossVec (F x) (fderiv ℝ G x (e i))`) — both in
`Submission/Work/FTS/PressureOn/vorticity_cross_eq.lean` — and the `Fin 3` algebra in the style of
`curl_inner_core` in `Submission/Work/FTS/PressureOn/materialDeriv_eq_gradient_sub_cross.lean`.
The sign has been checked by hand on the example `F = x₁ e₀`, `G = x₂ e₁`. -/
theorem div_crossVec_eq {F G : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {x : Work.FTS.PressureOn.R3}
    (hF : HasFDerivAt F (fderiv ℝ F x) x) (hG : HasFDerivAt G (fderiv ℝ G x) x) :
    FiniteTimeSingularity.div (fun y => Work.FTS.PressureOn.crossVec (F y) (G y)) x
      = inner ℝ (FiniteTimeSingularity.vorticity F x) (G x)
        - inner ℝ (F x) (FiniteTimeSingularity.vorticity G x) := by
  -- `div` is the trace, i.e. the sum of the diagonal entries in the basis `e`.
  rw [vorticityCross_div_eq_sum_diag]
  -- product rule for the pointwise cross product, direction by direction
  have hd : ∀ i : Fin 3, (fderiv ℝ (fun y => crossVec (F y) (G y)) x) (e i)
      = crossVec ((fderiv ℝ F x) (e i)) (G x) + crossVec (F x) ((fderiv ℝ G x) (e i)) :=
    fun i => vorticityCross_fderiv_crossVec_apply i hF hG
  simp only [hd, WithLp.ofLp_add, Pi.add_apply, Finset.sum_add_distrib]
  -- the two families of diagonal entries are `⟪curl F, G⟫` and `-⟪F, curl G⟫`
  rw [sum_diag_crossVec_left (fderiv ℝ F x) (G x),
    sum_diag_crossVec_right (fderiv ℝ G x) (F x)]
  rfl

end Work.FTS.PressureOn.CurlGrad
