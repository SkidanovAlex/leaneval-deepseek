import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.integrable_mul_latWave
import Submission.Work.BoseBoxFock.L1Tails.integral_mul_latWave_eq_conj_kinFT
import Submission.Work.BoseBoxFock.L1Tails.latCoeff_mul_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.pairLatPsi` — the exact pairing identity of the lattice Coulomb bound

The trial function of the duality argument is `ψ = φ_ℓ·P` with `P = Σ_{n∈S} c_n e^{i⟪κ_n,·⟫}` the
trigonometric polynomial of the dual coefficients `c_n = Ŵ(κ_n)/‖κ_n‖²`.  Because the bump `φ_ℓ` is
`≡ 1` on `ball 0 (ℓ/4)` and the weight `W` is supported there, the bump drops out of the pairing

  `∫ W ψ = Σ_{n∈S} c_n ∫ W e^{i⟪κ_n,·⟫} = Σ_{n∈S} c_n conj(Ŵ(κ_n)) = Σ_{n∈S} ‖Ŵ(κ_n)‖²/‖κ_n‖²`.

That last sum is `latSum ℓ S W`.  This module proves that identity; it is the second input of
`latCoulomb_le` (the first being the duality inequality `coulombDual`).

The three analytic/algebraic bricks are delegated:
* `integral_mul_latWave_eq_conj_kinFT` — `∫ W e^{i⟪κ,·⟫} = conj(Ŵ(κ))` (the `kinFT` convention is
  `Ŵ(p) = ∫ e^{−i⟪p,y⟫}W y`);
* `integrable_mul_latWave` — integrability of the product (unit modulus of the plane wave);
* `latCoeff_mul_conj` — `(Ŵ(κ)/‖κ‖²)·conj(Ŵ(κ)) = ‖Ŵ(κ)‖²/‖κ‖²`.

Nothing needs the hypothesis `0 ∉ S`: the algebra is unconditional (both sides vanish at the zero
mode), so `hS` is not used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

theorem pairLatPsi {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W)
    (hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), ℓ / 4 ≤ ‖x‖ → W x = 0)
    (S : Finset (Fin 3 → ℤ)) (hS : (0 : Fin 3 → ℤ) ∉ S) :
    ∫ x, ((W x : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.latPsi ℓ S (Work.BoseBoxFock.L1Tails.latCoeff ℓ W) x
      = ((Work.BoseBoxFock.L1Tails.latSum ℓ S W : ℝ) : ℂ) := by
  -- The bump may be dropped: `W x · φ_ℓ x = W x` pointwise, because `φ_ℓ ≡ 1` on the support of
  -- `W`.
  have hpt : ∀ x, (W x : ℂ) * latPsi ℓ S (latCoeff ℓ W) x
      = ∑ n ∈ S, (W x : ℂ) * (latCoeff ℓ W n * latWave (Work.BoseBoxFock.kappaL ℓ n) x) := by
    intro x
    have hb : (W x : ℂ) * (bumpFun ℓ x : ℂ) = (W x : ℂ) := by
      rcases lt_or_ge ‖x‖ (ℓ / 4) with h | h
      · rw [bumpFun_eq_one hℓ h.le, Complex.ofReal_one, mul_one]
      · rw [hsupp x h, Complex.ofReal_zero, zero_mul]
    simp only [latPsi, latPoly]
    rw [← mul_assoc, hb, Finset.mul_sum]
  -- Each summand is integrable, so the finite sum may be integrated term by term.
  have hInt : ∀ n ∈ S,
      Integrable (fun x => (W x : ℂ) * (latCoeff ℓ W n * latWave (Work.BoseBoxFock.kappaL ℓ n) x)) := by
    intro n _
    have heq : (fun x => (W x : ℂ) * (latCoeff ℓ W n * latWave (Work.BoseBoxFock.kappaL ℓ n) x))
        = (fun x => latCoeff ℓ W n * ((W x : ℂ) * latWave (Work.BoseBoxFock.kappaL ℓ n) x)) := by
      funext x; ring
    rw [heq]
    exact (integrable_mul_latWave hWi (Work.BoseBoxFock.kappaL ℓ n)).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum S hInt, latSum,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have h1 : ∫ x, (W x : ℂ) * (latCoeff ℓ W n * latWave (Work.BoseBoxFock.kappaL ℓ n) x)
      = latCoeff ℓ W n * (∫ x, (W x : ℂ) * latWave (Work.BoseBoxFock.kappaL ℓ n) x) := by
    rw [show (fun x => (W x : ℂ) * (latCoeff ℓ W n * latWave (Work.BoseBoxFock.kappaL ℓ n) x))
          = (fun x => latCoeff ℓ W n * ((W x : ℂ) * latWave (Work.BoseBoxFock.kappaL ℓ n) x)) from by
        funext x; ring]
    rw [integral_const_mul]
  rw [h1, integral_mul_latWave_eq_conj_kinFT W (Work.BoseBoxFock.kappaL ℓ n), latCoeff_mul_conj]

end Work.BoseBoxFock.L1Tails
