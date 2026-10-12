import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open Submission.BoseGases

/-- **Translation change of variable on the full space.**  For the Lebesgue
measure on `ℝ³` the reflection `u ↦ c - u` preserves the integral:
`∫ u, F (c - u) = ∫ u, F u`.  Both the translation `u ↦ u - c` and the
negation `u ↦ -u` are measure-preserving (`measure` of `volume` on a
finite-dimensional real vector space). -/
lemma nBox_integral_u_aux (F : ℝ³ → ℝ) (c : ℝ³) :
    (∫ u, F (c - u)) = ∫ u, F u := by
  have h1 : (∫ u, F (c - u)) = ∫ u, (fun v => F (-v)) (u - c) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [neg_sub]
  rw [h1, MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun v => F (-v)) c,
      MeasureTheory.integral_neg_eq_self (μ := volume) F]

/-- **`u`-integral of the localised particle number `n(u)`.**  For an
integrable density `ρ`, integrating the `B(u)`-mass
`n(u) = ∫_x ρ(x)·χ_{B(u)}(x)²` over all positions `u` of the small box
recovers the unlocalised mass against the big-box cutoff:

    ∫_u ∫_x ρ(x)·χ_M(x/ℓ)²·χ_M(x/(ℓd) − u)² dx du
      = ∫_x ρ(x)·χ_M(x/ℓ)² dx .

Route: Fubini (the joint integrand is `hρ`, exactly the uncurried form) and,
for each fixed `x`, the translation-invariance of Lebesgue measure
(`nBox_integral_u_aux`) together with the `L²`-normalisation
`∫ (χ_M)² = 1` (`chiSmall_L2`) for the `ℓd`-scale factor. -/
lemma nBox_integral_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hρ : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ρ p.1 * (Submission.BoseGases.chiSmallB M ℓ d p.2 p.1) ^ 2)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.nBox M ℓ d ρ u)
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          ρ x * (Submission.BoseGases.chiScale ℓ x) ^ 2 := by
  simp only [nBox]
  have hinner : ∀ x : ℝ³,
      ∫ u, ρ x * (chiSmallB M ℓ d u x) ^ 2
        = ρ x * (chiScale ℓ x) ^ 2 := by
    intro x
    -- factor `χ_{B(u)}(x)²` into the `ℓ`-scale square times the `ℓd`-scale square
    have hpt : ∀ u, ρ x * (chiSmallB M ℓ d u x) ^ 2
        = (ρ x * (chiScale ℓ x) ^ 2)
            * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 := by
      intro u
      simp only [chiSmallB, mul_pow]
      ring
    simp_rw [hpt]
    -- pull the `x`-dependent constant out of the `u`-integral
    rw [MeasureTheory.integral_const_mul]
    -- the remaining `u`-integral is the `L²`-mass of `χ_M`, by translation invariance
    have htr : ∫ u : ℝ³, (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 = 1 := by
      rw [nBox_integral_u_aux (fun v => (chiSmall M v) ^ 2) ((ℓ * d)⁻¹ • x)]
      exact chiSmall_L2 hM
    rw [htr, mul_one]
  -- Fubini: the joint integrand is exactly the uncurried `hρ`
  have hswap : (∫ u : ℝ³, ∫ x : ℝ³, ρ x * (chiSmallB M ℓ d u x) ^ 2)
      = ∫ x : ℝ³, ∫ u : ℝ³, ρ x * (chiSmallB M ℓ d u x) ^ 2 :=
    (MeasureTheory.integral_integral_swap hρ).symm
  have hfin : (∫ x : ℝ³, ∫ u : ℝ³, ρ x * (chiSmallB M ℓ d u x) ^ 2)
      = ∫ x : ℝ³, ρ x * (chiScale ℓ x) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall hinner
  rw [hswap, hfin]

end Work.SmallBoxSliding
