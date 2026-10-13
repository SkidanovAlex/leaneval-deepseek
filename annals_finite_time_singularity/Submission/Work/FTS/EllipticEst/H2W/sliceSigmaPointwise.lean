import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `σ`-weighted slice identity (`sliceSigmaPointwise`)

Fix `η = Work.Spaces.eta` and write `a = (1+η)/2`, `S = sin(2θ)`, `C = cos(2θ)`,
`U = u θ`, `D = deriv u θ`.  For any `u` differentiable at the interior point
`θ ∈ (0, π/2)` one has the pointwise identity

  `D² S^{-η} - 4 a² U² S^{-(2+η)} = (∂_θ(u S^{-a}))² S^{2a-η} + ∂_θ(2a cos(2θ) U² S^{-(1+η)})
      + 4 a (1-a) U² S^{-η}`.

The identity is the pointwise form of `sliceSigmaSubinterval` (Elgindi's `§H2` weighted
angular Hardy/coercivity estimate): integrating it over `[a,b] ⊆ (0,π/2)` and using
`2a - η = 1`, `C² + S² = 1`, the total derivative in the middle integrates to the boundary
difference of `2a cos(2θ) u² sin(2θ)^{-(1+η)}` and the first term is a square, so the
difference of the first two terms of the left hand side is controlled by the right hand side.

## Proof

The two `deriv`s are computed with `HasDerivAt` (`Real.hasDerivAt_rpow_const` for the
`rpow` factor, the product rule for the products), and the resulting identity is the
algebraic lemma `sliceSigma_alg`, obtained by multiplying with `S^{2+η} ≠ 0` and reducing
every product `S^r · S^s` to `S^{r+s}` (`Real.rpow_add`); after that all `S`-powers combine
to `S^0, S^1, S^2` and the remaining ring identity is exactly `C² + S² = 1` together with
`2a = 1+η`.
-/

namespace Work.FTS.EllipticEst.H2W

/-- Pure algebra behind `sliceSigmaPointwise`, for positive `S` with `C²+S² = 1` and
`2a = 1+η`.  It is the statement obtained after substituting the two derivatives. -/
private lemma sliceSigma_alg {S C D U a η : ℝ} (hS : 0 < S) (hcs : C ^ 2 + S ^ 2 = 1)
    (ha : 2 * a = 1 + η) :
    D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η))
      = (D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        + (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + 4 * a * (1 - a) * U ^ 2 * S ^ (-η) := by
  -- `S^r · S^s = S^(r+s)` for positive `S`.
  have hprod : ∀ r s t : ℝ, r + s = t → S ^ r * S ^ s = S ^ t :=
    fun r s t h => by rw [← Real.rpow_add hS, h]
  have e1 : S ^ (-η) * S ^ (2 + η) = S ^ 2 := by
    rw [hprod (-η) (2 + η) (2 : ℝ) (by ring), Real.rpow_two]
  have e2 : S ^ (-(2 + η)) * S ^ (2 + η) = 1 := by
    rw [hprod (-(2 + η)) (2 + η) (0 : ℝ) (by ring), Real.rpow_zero]
  have e3 : S ^ (-(1 + η)) * S ^ (2 + η) = S := by
    rw [hprod (-(1 + η)) (2 + η) (1 : ℝ) (by ring), Real.rpow_one]
  -- factor the bracket of the square
  have hfac : D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)
      = S ^ (-a - 1) * (D * S - 2 * a * C * U) := by
    have h : S ^ (-a - 1) * S ^ (1 : ℝ) = S ^ (-a) := hprod (-a - 1) 1 (-a) (by ring)
    rw [Real.rpow_one] at h
    calc D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)
        = D * (S ^ (-a - 1) * S) - 2 * a * C * U * S ^ (-a - 1) := by rw [h]
      _ = S ^ (-a - 1) * (D * S - 2 * a * C * U) := by ring
  have hsq : (S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η) = S ^ (-(2 + η)) := by
    have h2 : S ^ (-a - 1) * S ^ (-a - 1) = S ^ (-2 * a - 2) :=
      hprod (-a - 1) (-a - 1) (-2 * a - 2) (by ring)
    calc (S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        = (S ^ (-a - 1) * S ^ (-a - 1)) * S ^ (2 * a - η) := by ring
      _ = S ^ (-2 * a - 2) * S ^ (2 * a - η) := by rw [h2]
      _ = S ^ (-(2 + η)) := by rw [hprod (-2 * a - 2) (2 * a - η) (-(2 + η)) (by ring)]
  have ht1 : S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η))
      = (D * S - 2 * a * C * U) ^ 2 := by
    rw [hfac]
    calc S ^ (2 + η) * ((S ^ (-a - 1) * (D * S - 2 * a * C * U)) ^ 2 * S ^ (2 * a - η))
        = (D * S - 2 * a * C * U) ^ 2
            * ((S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η) * S ^ (2 + η)) := by ring
      _ = (D * S - 2 * a * C * U) ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by rw [hsq]
      _ = (D * S - 2 * a * C * U) ^ 2 * 1 := by rw [e2]
      _ = (D * S - 2 * a * C * U) ^ 2 := by ring
  have ht2 : S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
          - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
      = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 := by
    calc S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
          - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        = -4 * a * S * U ^ 2 * (S ^ (-(1 + η)) * S ^ (2 + η))
            + 4 * a * C * U * D * (S ^ (-(1 + η)) * S ^ (2 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by ring
      _ = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * 1 :=
            by rw [e3, e2]
      _ = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 := by ring
  have ht3 : S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η))
      = 4 * a * (1 - a) * U ^ 2 * S ^ 2 := by
    calc S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η))
        = 4 * a * (1 - a) * U ^ 2 * (S ^ (-η) * S ^ (2 + η)) := by ring
      _ = 4 * a * (1 - a) * U ^ 2 * S ^ 2 := by rw [e1]
  have hL : S ^ (2 + η) * (D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η)))
      = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 := by
    calc S ^ (2 + η) * (D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        = D ^ 2 * (S ^ (-η) * S ^ (2 + η))
            - 4 * a ^ 2 * U ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by ring
      _ = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 * 1 := by rw [e1, e2]
      _ = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 := by ring
  -- multiply by the positive factor `S^(2+η)` and cancel it
  apply mul_left_cancel₀ (a := S ^ (2 + η)) (ne_of_gt (Real.rpow_pos_of_pos hS (2 + η)))
  rw [hL]
  rw [show S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        + (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + 4 * a * (1 - a) * U ^ 2 * S ^ (-η))
      = S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η))
        + S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η)) from by ring]
  rw [ht1, ht2, ht3]
  -- the remaining identity is `C² + S² = 1` and `2a = 1 + η`
  rw [show (1 + η) = 2 * a by linarith]
  linear_combination (4 * a ^ 2 * U ^ 2) * hcs

theorem sliceSigmaPointwise {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : DifferentiableAt ℝ u θ) :
    (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      - 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
    = (deriv (fun θ' : ℝ => u θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta)
      + deriv (fun θ' : ℝ => 2 * ((1 + Work.Spaces.eta) / 2) * Real.cos (2 * θ') * (u θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta))) θ
      + 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  set a : ℝ := (1 + Work.Spaces.eta) / 2 with ha_def
  set S : ℝ := Real.sin (2 * θ) with hS_def
  set C : ℝ := Real.cos (2 * θ) with hC_def
  set D : ℝ := deriv u θ with hD_def
  set U : ℝ := u θ with hU_def
  have hSpos : 0 < S := by
    rw [hS_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hcs : C ^ 2 + S ^ 2 = 1 := by
    rw [hC_def, hS_def]
    exact Real.cos_sq_add_sin_sq (2 * θ)
  have hint : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * C) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hint
    refine h.congr_deriv ?_
    rw [hC_def]; ring
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * S) θ := by
    have h := (Real.hasDerivAt_cos (2 * θ)).comp θ hint
    refine h.congr_deriv ?_
    rw [hS_def]; ring
  have hpow1 : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-a))
      (-a * S ^ (-a - 1) * (2 * C)) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := S) (p := -a) (Or.inl hSne)).comp θ hsin
    refine h.congr_deriv ?_
    ring
  have hd1 : HasDerivAt (fun θ' : ℝ => u θ' * (Real.sin (2 * θ')) ^ (-a))
      (D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) θ := by
    have h := hu.hasDerivAt.mul hpow1
    refine h.congr_deriv ?_
    rw [hD_def, hU_def]; ring
  have hu2 : HasDerivAt (fun θ' : ℝ => (u θ') ^ 2) (2 * U * D) θ := by
    have h := hu.hasDerivAt.pow 2
    have hd : (↑2 * u θ ^ (2 - 1) * deriv u θ : ℝ) = 2 * U * D := by
      rw [hU_def, hD_def]; norm_num
    exact h.congr_deriv hd
  have hpow2 : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta)))
      (-(1 + Work.Spaces.eta) * S ^ (-(1 + Work.Spaces.eta) - 1) * (2 * C)) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := S) (p := -(1 + Work.Spaces.eta))
      (Or.inl hSne)).comp θ hsin
    refine h.congr_deriv ?_
    ring
  have hd2 : HasDerivAt (fun θ' : ℝ => 2 * a * Real.cos (2 * θ') * (u θ') ^ 2
        * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta)))
      (-4 * a * S * U ^ 2 * S ^ (-(1 + Work.Spaces.eta)) + 4 * a * C * U * D * S ^ (-(1 + Work.Spaces.eta))
        - 4 * a * (1 + Work.Spaces.eta) * C ^ 2 * U ^ 2 * S ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := (((hasDerivAt_const θ (2 * a)).mul hcos).mul hu2).mul hpow2
    refine h.congr_deriv ?_
    rw [hU_def, hD_def, hC_def, hS_def]
    simp only [Pi.mul_apply]
    ring_nf
  rw [hd1.deriv, hd2.deriv]
  refine sliceSigma_alg hSpos hcs ?_
  rw [ha_def]; ring

end Work.FTS.EllipticEst.H2W
