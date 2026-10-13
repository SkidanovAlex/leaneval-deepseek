import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.Dev6
import Submission.Work.FTS_BSIdentP.Slim.Dev11
import Submission.Work.FTS_BSIdentP.Slim.RhoMulRpowWeightLeTwo
import Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux
import Submission.Work.FTS_BSIdentP.Slim.MerPsiOriginAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The meridian stream function and its two first partials vanish at the origin

This file proves `Work.FTS.BSIdentP.Levels.merPsiT_origin_profiles`: along the half-plane
`r > 0`, the quotient `ψ/r` and the partial derivatives `∂_zψ`, `∂_rψ` of the meridian stream
function

  `ψ(r,z) = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^p/B(τ), θ(r,z), τ)`,  `p = 3α`,  `τ = clockInv C t`,

tend to `0` as `(r,z) → (0,0)`.

The mechanism is the *vanishing of the coefficients* in the chain rule: with `ρ = rhoP r z`,
`θ = thetaP r z`, `w = ρ^p/B(τ)`, `c = A(τ)⁻¹`, `G = Φ̂(·,·,τ)`,

  `ψ/r = ρ c (G(w,θ)/cos θ)`,
  `∂_zψ = 2 z c G + c (p z w ∂_wG + r ∂_θG)`,
  `∂_rψ = 2 r c G + c (p r w ∂_wG - z ∂_θG)`,

and every coefficient on the right is `O(ρ)` while `G(w,θ)`, `∂_wG(w,θ)`, `∂_θG(w,θ)` stay
bounded.  The quotient `G(w,θ)/cos θ` is bounded because the odd extension loses the factor
`π/2 - |θ|`, which Jordan's inequality compares with `cos θ`.

The partials are computed by `_dev6` on the open quadrant (`z ≠ 0`) and by `_dev11` on the
plane `z = 0`; the half-plane `z < 0` is reduced to `z > 0` by the oddness of `ψ` in `z`.
The limiting step is a squeeze against `K·rhoP r z`, using `rhoP r z → 0`.  The pointwise
bounds live in `merPsiT_origin_aux` and `merPsiT_origin_aux2`; this file assembles them.
-/

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

theorem merPsiT_origin_profiles {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t p.1 p.2 / p.1)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) ∧
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) ∧
    Filter.Tendsto (fun p : ℝ × ℝ =>
        Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
  have hp : 0 ≤ Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').1
  have hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').2.1
  have hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam) :=
    fun w θ hw hθ hθ' => (hrate w θ hw hθ hθ').2.2
  refine ⟨?_, ?_, ?_⟩
  · exact tendsto_zero_of_rhoP_bound
      (abs_div_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hB hlam hC₀.le hzeroPlane hval)
  · exact tendsto_zero_of_rhoP_bound
      (abs_pdR_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hsm hB hzeroPlane hp hlam hC₀.le hval hwd hth)
  · exact tendsto_zero_of_rhoP_bound
      (abs_pdZ_merPsiT_le (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
        hsm hB hzeroPlane hp hlam hC₀.le hval hwd hth)

end Work.FTS.BSIdentP.Levels
