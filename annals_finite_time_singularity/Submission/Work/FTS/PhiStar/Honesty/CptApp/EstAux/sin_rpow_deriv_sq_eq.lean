import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.H2.mixed_sin_bound
import Submission.Work.Blocks.alphaDz_pth_core_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sin(2θ)^(2-γ)·(∂_θ D_z^s F · w)² = (D_z^s D_θ F · W)²`

The two facts behind the identity of the linearised angular Hardy estimate: at an interior
point `(z,θ)` of the open quadrant and for a datum `F` smooth there,

* the angular derivative `D_θ F = sin(2θ) ∂_θ F` commutes with `D_z^s = (z ∂_z)^s`, i.e.
  `D_z^s D_θ F = sin(2θ)·∂_θ(D_z^s F)`
  (`mixed_one_eq_sin_mul_pth`, from `DzIter_const_mul_apply` + Clairaut);
* the weight identity `sin(2θ)^(2-γ) = (sin(2θ)·sin(2θ)^(-γ/2))²`
  (`sin_rpow_sq_factor`, pure `Real.rpow` algebra on the positive base `sin(2θ)`).

Together they give `sin(2θ)^(2-γ)·(∂_θD_z^sF · w)² = (D_z^sD_θF · w·sin(2θ)^(-γ/2))²`, which is
the statement below after unfolding `Wt = w·w_θ` and `w_θ = sin(2θ)^(-γ/2)`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-- **The angular derivative of the radial iterates.**  For `F` smooth on the open quadrant and
`(z,θ)` an interior point, `D_z^s D_θ F = sin(2θ)·∂_θ(D_z^s F)`.

The factor `sin(2θ)` of `D_θ` is `z`-independent, so it passes through the iterated curvilinear
radial derivative (`Work.FTS.H2.DzIter_const_mul_apply`); the remaining identity
`D_z^s (∂_θ F) = ∂_θ (D_z^s F)` is Clairaut's theorem in the form valid on the open quadrant
(`Work.Blocks.pth_DzIter_eqOn_Q0`). -/
theorem mixed_one_eq_sin_mul_pth (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (s : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed s 1 F z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter s F) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  -- the `sin(2θ)`-factor of `D_θ` passes through the radial iterates
  have h2 : Work.Spaces.DzIter s (Work.Spaces.Dth F) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter s (Work.Spaces.pth F) z θ := by
    rw [show Work.Spaces.Dth F
          = (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth F z θ) from rfl]
    exact Work.FTS.H2.DzIter_const_mul_apply (fun θ => Real.sin (2 * θ))
      (Work.Spaces.pth F) s z θ
  -- Clairaut: `∂_θ` commutes with `D_z^s` on the open quadrant
  have h3 : Work.Spaces.DzIter s (Work.Spaces.pth F) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter s F) z θ :=
    (Work.Blocks.pth_DzIter_eqOn_Q0 hF s hmem).symm
  rw [show Work.Spaces.mixed s 1 F = Work.Spaces.DzIter s (Work.Spaces.Dth F) from rfl,
    h2, h3]

/-- **The weight identity.**  For `S > 0`, `S^(2-γ) = (S·S^(-γ/2))²`.

Pure `Real.rpow` algebra: first `S^(-γ/2)·S^(-γ/2) = S^(-γ/2 + -γ/2)` (`Real.rpow_add`),
then `S·S = S^2` (`Real.rpow_two`) and `S^2·S^(-γ) = S^(2-γ)` (`Real.rpow_add` again).  All
the `rpow` steps are on the positive base `S`, so no degeneracy of `sin(2θ)` or of the
exponent `2-γ` can occur. -/
theorem sin_rpow_sq_factor (γ S : ℝ) (hS : 0 < S) :
    S ^ (2 - γ) = (S * S ^ (-(γ / 2))) ^ 2 := by
  have hs2 : (S ^ (-(γ / 2))) ^ 2 = S ^ (-(γ / 2) + -(γ / 2)) := by
    rw [sq, ← Real.rpow_add hS]
  rw [mul_pow, hs2, ← Real.rpow_two, ← Real.rpow_add hS]
  congr 1
  ring

theorem sin_rpow_deriv_sq_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (s : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  -- the identity `D_z^s D_θ F = sin(2θ) ∂_θ(D_z^s F)`, with `∂_θ` spelled `deriv`
  have hmix : Work.Spaces.mixed s 1 F z θ
      = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ := by
    rw [mixed_one_eq_sin_mul_pth F hF s hz hθ]
    rfl
  rw [hmix, Work.Spaces.Wt, Work.Spaces.wTheta]
  -- the base of every `rpow` below is positive
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hinner := sin_rpow_sq_factor (Work.Spaces.gam α) (Real.sin (2 * θ)) hS
  -- `(sin(2θ) ∂_θ(D_z^sF) (w·sin(2θ)^(-γ/2)))² = (sin(2θ)·sin(2θ)^(-γ/2))²·(∂_θ(D_z^sF)·w)²`
  have hsq : (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 := by
    rw [show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
        = (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
          * (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) by ring,
      mul_pow]
  exact (hsq.trans (by rw [hinner])).symm

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
