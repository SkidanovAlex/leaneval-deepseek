import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient
import Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_pi_div_two
import Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_neg_pi_div_two
import Submission.Work.FTS.BSIdent.Weyl.Levels.continuousAt_pdZ_G_zero
import Submission.Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_decay_bounds_ne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
open Filter Set
open scoped Topology

-- Bridge module: re-exports the delegated lemmas under the `DevStub` names used by the
-- development files below (the real proofs live in the imported `Work.FTS.BSIdent.Weyl.Levels`
-- modules).
namespace Work.FTS.BSIdent.Weyl.DevStub

theorem tendsto_slice_quotient {f : ℝ → ℝ → ℝ} {w₀ θ₀ δ : ℝ} (hδ : 0 < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ))
    (hz : ∀ w, |w - w₀| < δ → f w θ₀ = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / (p.2 - θ₀))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀))
      (𝓝 (deriv (fun θ => f w₀ θ) θ₀)) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient hδ hsm hz

theorem tendsto_PhiOdd_div_cos_at_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)))) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_pi_div_two hsm hπ hw₀

theorem tendsto_PhiOdd_div_cos_at_neg_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0}] (w₀, -(Real.pi / 2)))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_neg_pi_div_two hsm hπ hw₀

theorem continuousAt_pdZ_G_zero {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) p.1 p.2)
      (w₀, 0) := by
  exact Work.FTS.BSIdent.Weyl.Levels.continuousAt_pdZ_G_zero hsm h0 hw₀

theorem rho_mul_rpow_weight_le_two {p lam b ρ : ℝ} (hp : 0 < p) (hlam : 0 < lam) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hpl : 2 ≤ p * lam) :
    ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
  exact Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two hp hlam hb hρ hpl

theorem merPsiT_decay_bounds_ne {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r z : ℝ, 0 < r → z ≠ 0 →
      |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z| / r ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) := by
  exact Work.FTS.BSIdent.Weyl.Levels.merPsiT_decay_bounds_ne hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate

end Work.FTS.BSIdent.Weyl.DevStub
