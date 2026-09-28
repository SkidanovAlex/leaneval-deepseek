import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Main.conj1
import Submission.Work.HP.Q44Main.conj1_basic
import Submission.Work.HP.Q44Main.conj2
import Submission.Work.HP.Q44Main.min_compare
import Submission.Work.HP.MDEstimates.ell34_bound
import Submission.Work.HP.MDEstimates.ell44_convenient

/-!
# `Work.HP.quartic44` — BLBS §3.4 for quartic threefolds `(d,n) = (4,4)`

Target (unchanged): there is `K > 0` with, for all `Z, Δ, M, J ≥ 1`,

* `ℓ^{(1)}(Z;Δ,M) ≤ K Z^{9/2} Δ² (Z^{3/2} + Δ^{3/2}) (log 2Δ)² min(Δ, M^53)`;
* `ℓ^{(56)}(Z;Δ,J) ≤ K Z^4 Δ²⁴ J¹⁵`.

The first bound is the `min` of the unconditional pair count `ℓ^{(1)} ≤ Z⁶Δ³(log2Δ)²`
(`MDEstimates.ell34_bound`) and the "convenient" witness count `L1_bound`
(`Q44Main.conj1`), compared in `Q44Main.min_compare`.  The second is assembled from the
layer decomposition `MDEstimates.ell44_le_sum`, the per-lattice bound
`MDEstimates.q44_perlat_56` and the dyadic layer sum `Q44Main.q44_layer_sum`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP

open MvPolynomial Finset

/-- The first conjunct of `quartic44`. -/
theorem q44_conjunct_one :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M →
      (ell44 1 Z Δ M : ℝ) ≤ K * Z ^ ((9 : ℝ) / 2) * Δ ^ 2 * (Z ^ ((3 : ℝ) / 2) + Δ ^ ((3 : ℝ) / 2)) *
          Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) := by
  obtain ⟨KL, hKLpos, hL⟩ := Q44Main.L1_bound
  obtain ⟨KA, hKApos, hA⟩ := MDEstimates.ell34_bound
  obtain ⟨Kc, hKcpos, hc⟩ := Q44Main.min_compare KA KL hKApos hKLpos
  refine ⟨Kc, hKcpos, ?_⟩
  intro Z Δ M hZ hΔ hM
  have hA' : (ell44 1 Z Δ M : ℝ) ≤ KA * Z ^ (6:ℝ) * Δ ^ (3:ℝ) * Real.log (2*Δ)^2 := by
    have h1 : (ell44 1 Z Δ M : ℝ) ≤ (ellXY 4 3 Z Z Δ : ℝ) := by
      exact_mod_cast MDEstimates.ell44_le_ellXY Z Δ M
    have h2 := hA Z Δ hZ hΔ
    have e : KA * Z ^ 6 * Δ ^ 3 * Real.log (2*Δ)^2
        = KA * Z ^ (6:ℝ) * Δ ^ (3:ℝ) * Real.log (2*Δ)^2 := by
      rw [show (6:ℝ) = ((6:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (3:ℝ) = ((3:ℕ):ℝ) from rfl, Real.rpow_natCast]
    rw [e] at h2
    exact h1.trans h2
  have hL' : (ell44 1 Z Δ M : ℝ)
      ≤ KL * (M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((7:ℝ)/2) + M ^ (70:ℝ) * Z ^ (6:ℝ) * Δ ^ ((3:ℝ)/2)
        + M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((11:ℝ)/3) + M ^ (40:ℝ) * Z ^ (4:ℝ) * Δ ^ (3:ℝ)
        + M ^ (40:ℝ) * Z ^ (6:ℝ) * Δ ^ (2:ℝ)) * Real.log (2 * Δ) ^ 2 := by
    have h2 := hL Z Δ M hZ hΔ hM
    have e : KL * (M ^ 70 * Z ^ 4 * Δ ^ ((7:ℝ)/2) + M ^ 70 * Z ^ 6 * Δ ^ ((3:ℝ)/2)
        + M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) + M ^ 40 * Z ^ 4 * Δ ^ 3
        + M ^ 40 * Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2
        = KL * (M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((7:ℝ)/2) + M ^ (70:ℝ) * Z ^ (6:ℝ) * Δ ^ ((3:ℝ)/2)
        + M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((11:ℝ)/3) + M ^ (40:ℝ) * Z ^ (4:ℝ) * Δ ^ (3:ℝ)
        + M ^ (40:ℝ) * Z ^ (6:ℝ) * Δ ^ (2:ℝ)) * Real.log (2 * Δ) ^ 2 := by
      rw [show (70:ℝ) = ((70:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (4:ℝ) = ((4:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (6:ℝ) = ((6:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (40:ℝ) = ((40:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (3:ℝ) = ((3:ℕ):ℝ) from rfl, Real.rpow_natCast,
          show (2:ℝ) = ((2:ℕ):ℝ) from rfl, Real.rpow_natCast]
    rw [e] at h2
    exact h2
  have eT : Kc * Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
        * Real.log (2 * Δ) ^ 2 * min Δ (M ^ (53:ℝ))
      = Kc * Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
        * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from rfl, Real.rpow_natCast,
        show (53:ℝ) = ((53:ℕ):ℝ) from rfl, Real.rpow_natCast]
  rw [← eT]
  exact le_trans (le_min hA' hL') (hc Z Δ M hZ hΔ hM)

theorem quartic44 :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M J : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → 1 ≤ J →
      (ell44 1 Z Δ M : ℝ) ≤ K * Z ^ ((9 : ℝ) / 2) * Δ ^ 2 * (Z ^ ((3 : ℝ) / 2) + Δ ^ ((3 : ℝ) / 2)) *
          Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) ∧
      (ell44 56 Z Δ J : ℝ) ≤ K * Z ^ 4 * Δ ^ 24 * J ^ 15 := by
  obtain ⟨K1, hK1pos, h1⟩ := q44_conjunct_one
  obtain ⟨K2, hK2pos, h2⟩ := Q44Main.conj2_56
  refine ⟨max K1 K2, by positivity, ?_⟩
  intro Z Δ M J hZ hΔ hM hJ
  have hZ0 : (0:ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ
  have hD0 : (0:ℝ) < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM
  have hJ0 : (0:ℝ) ≤ J := le_trans zero_le_one hJ
  refine ⟨?_, ?_⟩
  · refine le_trans (h1 Z Δ M hZ hΔ hM) ?_
    have hpos : (0:ℝ) ≤ Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
        * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) := by
      have h1a : (0:ℝ) ≤ Z ^ ((9:ℝ)/2) := Real.rpow_nonneg hZ0.le _
      have h1b : (0:ℝ) ≤ Z ^ ((3:ℝ)/2) := Real.rpow_nonneg hZ0.le _
      have h1c : (0:ℝ) ≤ Δ ^ ((3:ℝ)/2) := Real.rpow_nonneg hD0.le _
      have h1d : (0:ℝ) ≤ min Δ (M ^ 53) := le_min hD0.le (by positivity)
      positivity
    calc K1 * Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
          * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53)
        = K1 * (Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
            * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53)) := by ring
      _ ≤ (max K1 K2) * (Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
            * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53)) :=
          mul_le_mul_of_nonneg_right (le_max_left K1 K2) hpos
      _ = (max K1 K2) * Z ^ ((9:ℝ)/2) * Δ ^ 2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
          * Real.log (2 * Δ) ^ 2 * min Δ (M ^ 53) := by ring
  · refine le_trans (h2 Z Δ J hZ hΔ hJ) ?_
    have hpos2 : (0:ℝ) ≤ Z ^ 4 * Δ ^ 24 * J ^ 15 := by positivity
    calc K2 * Z ^ 4 * Δ ^ 24 * J ^ 15
        = K2 * (Z ^ 4 * Δ ^ 24 * J ^ 15) := by ring
      _ ≤ (max K1 K2) * (Z ^ 4 * Δ ^ 24 * J ^ 15) :=
          mul_le_mul_of_nonneg_right (le_max_right K1 K2) hpos2
      _ = (max K1 K2) * Z ^ 4 * Δ ^ 24 * J ^ 15 := by ring

end Work.HP
