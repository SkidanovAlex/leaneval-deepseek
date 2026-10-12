import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latSum_integral_swap`

The interchange of the lattice sum `Σ'_{m ∈ ℤ³}` with the volume integral

    `∑'_m ∫_y (W y) · K (ℓ·latVec m − y) dy = ∫_y (W y) · (∑'_m K (ℓ·latVec m − y)) dy`

for `W : ℝ³ → ℝ` bounded and carried by the closed ball of radius `R` and `K : ℝ³ → ℂ` continuous
and carried by the closed ball of radius `ρ`.

## Why the interchange is honest

The two support hypotheses make every series involved a **finite** sum:

* if `W y ≠ 0` then `‖y‖ ≤ R`, and `‖ℓ·latVec m − y‖ ≥ ℓ‖latVec m‖ − ‖y‖`, so a far lattice point
  (`R + ρ < ℓ‖latVec m‖`) contributes `0` to the integrand — in particular the integral of the
  `m`-th summand vanishes identically for such `m`, and the outer `∑'` is a finite sum;
* likewise, for fixed `y` and `R + ρ < ℓ‖latVec m‖`, the term `(W y)·K (ℓ·latVec m − y)` vanishes
  (either `W y = 0`, or `‖y‖ ≤ R` and then `‖ℓ·latVec m − y‖ > ρ`, so `K` vanishes).

So both sides equal the corresponding `Finset`-sum over the (finite) set
`{m | ‖latVec m‖ ≤ (R+ρ)/ℓ}`, and the remaining content is `integral_finsetSum`.

## Contents

* `finite_setOf_norm_latVec_le` — the lattice points of `ℤ³` in a ball form a finite set
  (elementary: they sit in the `ℓ^∞` ball `|m i| ≤ ⌊c⌋ + 1`, a finite product of finite sets).
* `latSum_integral_swap` — the requested interchange.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The integer lattice points of `ℤ³` lying in a ball of radius `c` form a finite set.

Indeed, if `‖latVec m‖ ≤ c` then each coordinate obeys `|m i| ≤ ⌊max c 0⌋ + 1` (coordinatewise
comparison of the Euclidean norm with the sup norm, `PiLp.norm_apply_le`), and a finite product of
finite sets is finite. -/
lemma finite_setOf_norm_latVec_le (c : ℝ) : {m : Fin 3 → ℤ | ‖latVec m‖ ≤ c}.Finite := by
  classical
  set N : ℤ := ⌊max c 0⌋ + 1 with hN
  have hmem : ∀ m : Fin 3 → ℤ, ‖latVec m‖ ≤ c →
      m ∈ Set.univ.pi (fun _ : Fin 3 => Set.Icc (-N) N) := by
    intro m hm
    rw [Set.mem_univ_pi]
    intro i
    -- coordinatewise comparison with the Euclidean norm
    have h1 : |((m i : ℤ) : ℝ)| ≤ ‖latVec m‖ := by
      have h2 : ‖(latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
        have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
          simp [latVec, WithLp.ofLp_toLp]
        rw [h3, Real.norm_eq_abs]
      rw [← h2]
      exact PiLp.norm_apply_le (latVec m) i
    have h4 : |((m i : ℤ) : ℝ)| ≤ (max c 0 : ℝ) := le_trans h1 (le_trans hm (le_max_left _ _))
    have h4' : |((m i : ℤ) : ℝ)| < (N : ℝ) := by
      refine lt_of_le_of_lt h4 ?_
      rw [hN]
      push_cast
      exact Int.lt_floor_add_one (max c 0)
    have h5 : ((|m i| : ℤ) : ℝ) < (N : ℝ) := by rwa [Int.cast_abs]
    have h6 : |m i| ≤ N := by exact_mod_cast le_of_lt h5
    exact abs_le.mp h6
  exact (Set.Finite.pi (fun _ : Fin 3 => Set.finite_Icc (-N) N)).subset hmem

theorem latSum_integral_swap {ℓ R ρ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} {K : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0)
    (hKc : Continuous K) (hKs : ∀ x, ρ < ‖x‖ → K x = 0) :
    (∑' m : Fin 3 → ℤ, ∫ y : EuclideanSpace ℝ (Fin 3),
        (W y : ℂ) * K (ℓ • Work.BoseBoxFock.latVec m - y))
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          (W y : ℂ) * (∑' m : Fin 3 → ℤ, K (ℓ • Work.BoseBoxFock.latVec m - y)) := by
  classical
  obtain ⟨CW, hCW⟩ := hWb
  -- the finite set of lattice points that can contribute
  have hfin : {m : Fin 3 → ℤ | ‖latVec m‖ ≤ (R + ρ) / ℓ}.Finite :=
    finite_setOf_norm_latVec_le _
  set s : Finset (Fin 3 → ℤ) := hfin.toFinset with hs
  have hsmem : ∀ m : Fin 3 → ℤ, m ∈ s ↔ ‖latVec m‖ ≤ (R + ρ) / ℓ := fun m =>
    Set.Finite.mem_toFinset hfin
  -- every lattice point outside `s` is far: `R + ρ < ℓ‖latVec m‖`
  have hsbig : ∀ m : Fin 3 → ℤ, m ∉ s → R + ρ < ℓ * ‖latVec m‖ := by
    intro m hm
    have h2 : (R + ρ) / ℓ < ‖latVec m‖ :=
      lt_of_not_ge (fun h => hm ((hsmem m).mpr h))
    have h3 : R + ρ < ‖latVec m‖ * ℓ := (div_lt_iff₀ hℓ).mp h2
    linarith
  -- for a far lattice point the product `W · K` vanishes pointwise
  have hfar : ∀ m : Fin 3 → ℤ, m ∉ s →
      ∀ y : E3, (W y : ℂ) * K (ℓ • latVec m - y) = 0 := by
    intro m hm y
    by_cases hW : W y = 0
    · simp [hW]
    · have hy : ‖y‖ ≤ R := le_of_not_gt (fun hlt => hW (hWs y hlt))
      have hbig := hsbig m hm
      have h1 : ℓ * ‖latVec m‖ - ‖y‖ ≤ ‖ℓ • latVec m - y‖ := by
        have h := norm_sub_norm_le (ℓ • latVec m) y
        rwa [norm_smul, Real.norm_of_nonneg hℓ.le] at h
      have h3 : ρ < ‖ℓ • latVec m - y‖ := by linarith
      rw [hKs _ h3, mul_zero]
  -- `K` has compact support
  have hKcs : HasCompactSupport K := by
    have hsub : Function.support K ⊆ Metric.closedBall (0 : E3) ρ := by
      intro x hx
      by_contra h
      exact hx (hKs x (by
        have : ¬ ‖x‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using h
        exact not_le.mp this))
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) ρ) isClosed_closure
      (closure_minimal hsub Metric.isClosed_closedBall)
  -- hence so does every reflection-translate `y ↦ K (ℓ • latVec m − y)`, which is integrable
  have hKtrans : ∀ m : Fin 3 → ℤ, Integrable (fun y : E3 => K (ℓ • latVec m - y)) volume := by
    intro m
    exact (hKc.comp ((Homeomorph.neg E3).trans
        (Homeomorph.addLeft (ℓ • latVec m))).continuous).integrable_of_hasCompactSupport
      (hKcs.comp_homeomorph ((Homeomorph.neg E3).trans
        (Homeomorph.addLeft (ℓ • latVec m))))
  -- `y ↦ (W y : ℂ)` is a.e. strongly measurable and bounded, so the products are integrable
  have hWmeas : AEStronglyMeasurable (fun y : E3 => ((W y : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hWm
  have hWbound : ∀ᵐ y : E3 ∂volume, ‖((W y : ℝ) : ℂ)‖ ≤ CW := by
    filter_upwards with y
    simpa using hCW y
  have hInt : ∀ m : Fin 3 → ℤ,
      Integrable (fun y : E3 => (W y : ℂ) * K (ℓ • latVec m - y)) volume :=
    fun m => (hKtrans m).bdd_mul hWmeas hWbound
  -- the pointwise identification of the right-hand integrand with a finite sum
  have hpt : ∀ y : E3, (W y : ℂ) * (∑' m : Fin 3 → ℤ, K (ℓ • latVec m - y))
      = ∑ m ∈ s, (W y : ℂ) * K (ℓ • latVec m - y) := by
    intro y
    rw [← tsum_mul_left, tsum_eq_sum (s := s) (fun m hm => hfar m hm y)]
  -- the outer series is a finite sum
  have hLsum : (∑' m : Fin 3 → ℤ, ∫ y : E3, (W y : ℂ) * K (ℓ • latVec m - y))
      = ∑ m ∈ s, ∫ y : E3, (W y : ℂ) * K (ℓ • latVec m - y) := by
    refine tsum_eq_sum (s := s) (fun m hm => ?_)
    rw [show (fun y : E3 => (W y : ℂ) * K (ℓ • latVec m - y)) = fun _ => 0
        from funext (hfar m hm)]
    simp
  -- and the integral of the finite sum is the finite sum of the integrals
  have hRsum : (∫ y : E3, (W y : ℂ) * (∑' m : Fin 3 → ℤ, K (ℓ • latVec m - y)))
      = ∑ m ∈ s, ∫ y : E3, (W y : ℂ) * K (ℓ • latVec m - y) := by
    rw [funext hpt]
    exact integral_finsetSum s (fun m _ => hInt m)
  rw [hLsum, hRsum]

end Work.BoseBoxFock
