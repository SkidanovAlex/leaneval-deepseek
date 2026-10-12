import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.coulombDual
import Submission.Work.BoseBoxFock.L1Tails.latDirichlet
import Submission.Work.BoseBoxFock.L1Tails.pairLatPsi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.latCoulomb_le` — the lattice Coulomb sum bound (design T4)

For a weight `W ≥ 0` with `supp W ⊆ ball 0 (ℓ/4)` and finite Coulomb energy
`∬ W(x)W(y)/‖x−y‖ < ∞`, the lattice Fourier samples of `W` satisfy

    ℓ⁻³ Σ_{n ∈ S, n ≠ 0} ‖Ŵ(κ_n)‖²/‖κ_n‖² ≤ C₀ ∬ W(x)W(y)/‖x−y‖ ,

with `κ_n = 2πn/ℓ` and a universal constant `C₀` (no rate in `ℓ`).

The proof is the duality argument: with the dual coefficients `c_n = Ŵ(κ_n)/‖κ_n‖²` and the trial
function `ψ = φ_ℓ·Σ_{n∈S} c_n e^{i⟪κ_n,x⟫}` (`latDefs`),

* `∫ W ψ = Σ_{n∈S} ‖Ŵ(κ_n)‖²/‖κ_n‖²` exactly (`pairLatPsi`) — the bump `φ_ℓ` is `1` on `supp W`;
* `‖∫Wψ‖² ≤ (4π)⁻¹ (∬WW/r)·∑_j∫‖∂_jψ‖²` (`coulombDual`, the Ḣ⁻¹–Ḣ¹ duality);
* `∑_j∫‖∂_jψ‖² ≤ latConst·ℓ³·Σ_{n∈S}‖c_n‖²‖κ_n‖²` (`latDirichlet`, via the lattice
  orthogonality and the Poincaré bound `‖κ_n‖ ≥ 2π/ℓ`).

Hence `A² ≤ (4π)⁻¹ E·latConst·ℓ³·A` with `A = Σ_{n∈S}‖Ŵ(κ_n)‖²/‖κ_n‖² ≥ 0`, so
`ℓ⁻³ A ≤ (latConst/4π)·E`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **The coefficients reproduce the target's sum**: `Σ_n ‖c_n‖²‖κ_n‖² = latSum`. -/
lemma latSum_eq_coeff {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) (W : E3 → ℝ)
    (hS : (0 : Fin 3 → ℤ) ∉ S) :
    ∑ n ∈ S, ‖latCoeff ℓ W n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 = latSum ℓ S W := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by rintro rfl; exact hS hn
  have hpos : 0 < ‖kappaL ℓ n‖ := lt_of_lt_of_le (by positivity) (two_pi_div_le_norm_kappaL hℓ hn0)
  have hnorm : ‖latCoeff ℓ W n‖
      = ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) (kappaL ℓ n)‖
          / ‖kappaL ℓ n‖ ^ 2 := by
    rw [latCoeff, norm_div, norm_ofReal_C, abs_of_nonneg (sq_nonneg _)]
  rw [hnorm]
  field_simp

/-- The target's sum is nonnegative. -/
lemma latSum_nonneg (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (W : E3 → ℝ) : 0 ≤ latSum ℓ S W :=
  Finset.sum_nonneg fun n _ => by positivity

theorem latCoulomb_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ {ℓ : ℝ}, 0 < ℓ → ∀ {W : EuclideanSpace ℝ (Fin 3) → ℝ}, MeasureTheory.Integrable W →
      (∀ᵐ x, 0 ≤ W x) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ℓ / 4 ≤ ‖x‖ → W x = 0) →
      MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W) →
      ∀ S : Finset (Fin 3 → ℤ), (0 : Fin 3 → ℤ) ∉ S →
        (ℓ ^ 3)⁻¹ * ∑ n ∈ S,
            ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
          ≤ C₀ * ∫ p, Work.BoseBoxFock.coulInt W p := by
  refine ⟨latConst / (4 * Real.pi), div_nonneg latConst_nonneg (by positivity), ?_⟩
  intro ℓ hℓ W hWi hW0 hsupp hJ S hS
  set A : ℝ := latSum ℓ S W with hAdef
  set E : ℝ := ∫ p, Work.BoseBoxFock.coulInt W p with hEdef
  have hAnn : 0 ≤ A := latSum_nonneg ℓ S W
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    have hrew : (∫ q : E3 × E3, Work.BoseBoxFock.coulInt W q)
        = ∫ q : E3 × E3, W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹ := rfl
    have hprod : (∫ q : E3 × E3, W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹)
        = ∫ x : E3, ∫ y : E3, W x * W y * (‖x - y‖ : ℝ)⁻¹ :=
      MeasureTheory.integral_prod
        (fun q : E3 × E3 => W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹) hJ
    rw [hrew, hprod]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hW0] with x hx
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hW0] with y hy
    exact mul_nonneg (mul_nonneg hx hy) (inv_nonneg.mpr (norm_nonneg _))
  -- the trial function
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (latPsi ℓ S (latCoeff ℓ W)) := latPsi_contDiff ℓ S _
  have hψc : HasCompactSupport (latPsi ℓ S (latCoeff ℓ W)) := latPsi_hasCompactSupport hℓ S _
  -- (1) the pairing identity
  have hpair : (∫ x : E3, ((W x : ℝ) : ℂ) * latPsi ℓ S (latCoeff ℓ W) x) = ((A : ℝ) : ℂ) := by
    rw [hAdef]
    exact pairLatPsi hℓ hWi hsupp S hS
  have hnormSq : ‖∫ x : E3, ((W x : ℝ) : ℂ) * latPsi ℓ S (latCoeff ℓ W) x‖ ^ 2 = A ^ 2 := by
    rw [hpair, norm_ofReal_C, sq_abs]
  -- (2) the duality and the Dirichlet bound
  have hdual := coulombDual hWi hW0 hJ hψ hψc
  have hdir : ∑ j : Fin 3,
      ∫ x : E3, ‖fderiv ℝ (latPsi ℓ S (latCoeff ℓ W)) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ latConst * ℓ ^ 3 * A := by
    refine le_trans (dirichletLatPsi hℓ S (latCoeff ℓ W) hS) ?_
    rw [hAdef]
    exact le_of_eq (by rw [latSum_eq_coeff hℓ S W hS])
  -- (3) the quadratic inequality
  have hmain : A ^ 2 ≤ ((4 * Real.pi)⁻¹ * E * latConst * ℓ ^ 3) * A := by
    calc A ^ 2
        = ‖∫ x : E3, ((W x : ℝ) : ℂ) * latPsi ℓ S (latCoeff ℓ W) x‖ ^ 2 := hnormSq.symm
      _ ≤ (4 * Real.pi)⁻¹ * E * (∑ j : Fin 3,
            ∫ x : E3, ‖fderiv ℝ (latPsi ℓ S (latCoeff ℓ W)) x
              (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
          rw [hEdef]
          exact hdual
      _ ≤ (4 * Real.pi)⁻¹ * E * (latConst * ℓ ^ 3 * A) :=
          mul_le_mul_of_nonneg_left hdir (mul_nonneg (by positivity) hEnn)
      _ = ((4 * Real.pi)⁻¹ * E * latConst * ℓ ^ 3) * A := by ring
  have hA_le : A ≤ (4 * Real.pi)⁻¹ * E * latConst * ℓ ^ 3 := by
    rcases eq_or_lt_of_le hAnn with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hEnn) latConst_nonneg)
        (by positivity)
    · nlinarith [hmain, hpos]
  -- (4) the normalisation
  calc (ℓ ^ 3)⁻¹ * ∑ n ∈ S,
          ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
      = (ℓ ^ 3)⁻¹ * A := by rw [hAdef, latSum]
    _ ≤ (ℓ ^ 3)⁻¹ * ((4 * Real.pi)⁻¹ * E * latConst * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hA_le (by positivity)
    _ = (latConst / (4 * Real.pi)) * ∫ p, Work.BoseBoxFock.coulInt W p := by
        rw [hEdef]
        field_simp
        try ring

end Work.BoseBoxFock.L1Tails
