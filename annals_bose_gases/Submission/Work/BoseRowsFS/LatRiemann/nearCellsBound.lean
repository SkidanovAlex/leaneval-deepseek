import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseRowsFS.LatRiemann.ballInvSq
import Submission.Work.BoseRowsFS.LatRiemann.nearCellsValueSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.nearCellsBound`

The **near cells** of the lattice-vs-continuum comparison
(Step 3c of `Submission/Work/BoseRowsFS/FINDING_lattice_riemann_core.md`, and the `Kr`
summand of the lattice-Riemann core): the cells `hbox h m` whose lattice point satisfies
`‖latPt h m‖ < 2√3 h`.  Writing `F := Φ/‖·‖²`, the claim is

    `Σ_{m ∈ Kr} |∫_{hbox h m} F − h³ F(latPt h m)| ≤ 500 A h`.

Two independent estimates are added, each of which is proved in its own module:

* `nearCellsIntegralSum` (here) — the *integral* half.  By `m ≠ 0` the cells stay at
  distance `≥ h/2` from the origin, they are pairwise disjoint, and the near condition
  puts their union inside the ball of radius `(2√3 + √3/2)h < 5h`; so
  `Σ_m |∫_{hbox h m} F| ≤ ∫_{‖p‖<5h} A/‖p‖² = 20π A h ≤ 62.83 A h`
  (the exact value `4π·(5h)·A` of the radial integral is `ballInvSq`, polar coordinates
  in `ℝ³`).  Note that `FINDING_lattice_riemann_core.md` Step 3c asserts
  `⋃ Q_m ⊆ ball 0 4h`, which is *false* (`2√3 + √3/2 = 2.5√3 ≈ 4.33`); the conclusion
  is unaffected since the constant `20π` only needs `2.5√3 ≤ 5`.
* `nearCellsValueSum` (its own module) — the *value* half: the near indices have every
  coordinate in `[-3,3]`, so `|Kr| ≤ 7³ = 343` and each lattice value contributes at
  most `A h`: `Σ_m h³|Φ(latPt h m)|/‖latPt h m‖² ≤ 343 A h`.

Since `|X − Y| ≤ |X| + |Y|`, the two halves give
`(20π + 343) A h ≈ 405.8 A h ≤ 500 A h`, which is the constant of the statement. -/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **A near cell lies in the ball of radius `5h`.**  On `hbox h m` the point `p` is at
distance at most `h√3/2` from `latPt h m`; adding the near bound `‖latPt h m‖ < 2√3 h`
and `√3 ≤ 2` gives `‖p‖ < (2√3 + √3/2) h = (5/2)√3 h ≤ 5h`. -/
lemma hbox_subset_ball {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ}
    (hnear : ‖Work.BoseRowsFS.latPt h m‖ < 2 * Real.sqrt 3 * h) :
    hbox h m ⊆ Metric.ball (0 : ℝ³) (5 * h) := by
  intro p hp
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ h * Real.sqrt 3 / 2 := norm_sub_latPt_le hh hp
  have h2 : ‖Work.BoseRowsFS.latPt h m‖ < 2 * Real.sqrt 3 * h := hnear
  have h3 : ‖p‖ ≤ ‖Work.BoseRowsFS.latPt h m‖ + ‖p - Work.BoseRowsFS.latPt h m‖ := by
    have h4 := norm_add_le (Work.BoseRowsFS.latPt h m) (p - Work.BoseRowsFS.latPt h m)
    simpa using h4
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hs3h : h * Real.sqrt 3 ≤ 2 * h := by
    have := mul_le_mul_of_nonneg_left hs3 (le_of_lt hh)
    linarith
  linarith

/-- **The integral half of the near-cell bound.**  The near cells are pairwise disjoint
and contained in the ball of radius `5h`, so the absolute values of their integrals add
up to at most the integral of `A/‖p‖²` over that ball, which is `20π A h`. -/
theorem nearCellsIntegralSum {h A : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    {Φ : ℝ³ → ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (Kr : Finset (Fin 3 → ℤ))
    (hKr : ∀ m ∈ Kr, m ≠ 0 ∧ ¬ (2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)) :
    ∑ m ∈ Kr, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)| ≤ 20 * Real.pi * A * h := by
  classical
  set F : ℝ³ → ℝ := fun p => Φ p / ‖p‖ ^ 2 with hF
  have hne : ∀ m ∈ Kr, m ≠ 0 := fun m hm => (hKr m hm).1
  have hnear : ∀ m ∈ Kr, ‖Work.BoseRowsFS.latPt h m‖ < 2 * Real.sqrt 3 * h :=
    fun m hm => not_le.mp (hKr m hm).2
  -- Pointwise domination of the integrand by `A/‖p‖²`.
  have hFb : ∀ p : ℝ³, |F p| ≤ A / ‖p‖ ^ 2 := by
    intro p
    have h1 : |Φ p| ≤ A := by
      have h2 : (1 : ℝ) ≤ (1 + ‖p‖) ^ 4 := by
        have h0 : (1 : ℝ) ≤ 1 + ‖p‖ := by have := norm_nonneg p; linarith
        exact one_le_pow₀ h0
      have h3 : A / (1 + ‖p‖) ^ 4 ≤ A := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ 4)]
        nlinarith [hA, h2]
      exact (hΦ p).trans h3
    rw [hF]
    simp only
    rw [abs_div, abs_of_nonneg (sq_nonneg ‖p‖)]
    exact div_le_div_of_nonneg_right h1 (sq_nonneg ‖p‖)
  -- The union of the near cells lies in the ball of radius `5h`.
  have hUsub : (⋃ m ∈ Kr, hbox h m) ⊆ Metric.ball (0 : ℝ³) (5 * h) := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨m, hm, hpm⟩ := hp
    exact hbox_subset_ball hh (hnear m hm) hpm
  have hUmeas : MeasurableSet (⋃ m ∈ Kr, hbox h m) :=
    Finset.measurableSet_biUnion Kr (fun m _ => measurableSet_hbox h m)
  -- Integrability of `|F|` on each cell: the cell avoids the origin, so `|F| ≤ 4A/h²`.
  have hInt : ∀ m ∈ Kr, IntegrableOn (fun p : ℝ³ => |F p|) (hbox h m) volume := by
    intro m hm
    refine IntegrableOn.of_bound ?_ ?_ (4 * A / h ^ 2) ?_
    · rw [volume_hbox]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
    · exact ((hcont.measurable.div (continuous_norm.pow 2).measurable).abs).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' (measurableSet_hbox h m)]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hge : h / 2 ≤ ‖p‖ := norm_ge_of_mem_hbox (hne m hm) hh hp
      have h2 : A / ‖p‖ ^ 2 ≤ 4 * A / h ^ 2 := by
        have hp2 : h ^ 2 ≤ 4 * ‖p‖ ^ 2 := by nlinarith [hge, hh, norm_nonneg p]
        rw [div_le_div_iff₀ (by nlinarith [hge, hh] : (0 : ℝ) < ‖p‖ ^ 2)
          (by positivity : (0 : ℝ) < h ^ 2)]
        nlinarith [hp2, hA]
      have hb : |F p| ≤ 4 * A / h ^ 2 := le_trans (hFb p) h2
      simpa [Real.norm_eq_abs] using hb
  -- The disjoint-union identity and the two monotonicity steps.
  have hpair : Set.Pairwise (↑Kr) (Function.onFun Disjoint (fun m => hbox h m)) := by
    intro a _ b _ hab
    exact disjoint_hbox hh hab
  have hunion : ∫ p in (⋃ m ∈ Kr, hbox h m), |F p| = ∑ m ∈ Kr, ∫ p in hbox h m, |F p| :=
    MeasureTheory.integral_biUnion_finset Kr (fun m _ => measurableSet_hbox h m) hpair hInt
  have hFU : IntegrableOn (fun p : ℝ³ => |F p|) (⋃ m ∈ Kr, hbox h m) volume :=
    MeasureTheory.integrableOn_finset_iUnion.mpr hInt
  have hGU : IntegrableOn (fun p : ℝ³ => A / ‖p‖ ^ 2) (⋃ m ∈ Kr, hbox h m) volume :=
    (ballInvSq (A := A) (R := 5 * h) hA (by linarith [hh])).1.mono_set hUsub
  have hstep1 : ∫ p in (⋃ m ∈ Kr, hbox h m), |F p|
      ≤ ∫ p in (⋃ m ∈ Kr, hbox h m), A / ‖p‖ ^ 2 :=
    MeasureTheory.setIntegral_mono_on hFU hGU hUmeas (fun p _ => hFb p)
  have hstep2 : ∫ p in (⋃ m ∈ Kr, hbox h m), A / ‖p‖ ^ 2
      ≤ ∫ p in Metric.ball (0 : ℝ³) (5 * h), A / ‖p‖ ^ 2 :=
    MeasureTheory.setIntegral_mono_set (ballInvSq (A := A) (R := 5 * h) hA (by linarith [hh])).1
      (Filter.Eventually.of_forall (fun p => div_nonneg hA (sq_nonneg ‖p‖)))
      (Filter.Eventually.of_forall hUsub)
  have hstep3 : ∫ p in Metric.ball (0 : ℝ³) (5 * h), A / ‖p‖ ^ 2 ≤ 20 * Real.pi * A * h := by
    have h45 : (4 : ℝ) * Real.pi * A * (5 * h) = 20 * Real.pi * A * h := by ring
    linarith [(ballInvSq (A := A) (R := 5 * h) hA (by linarith [hh])).2, h45]
  calc ∑ m ∈ Kr, |∫ p in hbox h m, Φ p / ‖p‖ ^ 2|
      = ∑ m ∈ Kr, |∫ p in hbox h m, F p| := by simp only [hF]
    _ ≤ ∑ m ∈ Kr, ∫ p in hbox h m, |F p| := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        have h4 := MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (hbox h m)) (fun p : ℝ³ => F p)
        simpa [Real.norm_eq_abs] using h4
    _ = ∫ p in (⋃ m ∈ Kr, hbox h m), |F p| := hunion.symm
    _ ≤ 20 * Real.pi * A * h := le_trans hstep1 (le_trans hstep2 hstep3)

/-- **The near cells of the lattice-vs-continuum comparison.**  Splitting each summand
as `|X − Y| ≤ |X| + |Y|` and applying the two halves: `Σ_m |∫ F| ≤ 20π A h`
(`nearCellsIntegralSum`) and `Σ_m h³|F(latPt h m)| ≤ 343 A h` (`nearCellsValueSum`),
whence `(20π + 343) A h ≤ 500 A h` since `π < 4`. -/
theorem nearCellsBound {h A : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (Kr : Finset (Fin 3 → ℤ))
    (hKr : ∀ m ∈ Kr, m ≠ 0 ∧ ¬ (2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)) :
    ∑ m ∈ Kr, |(∫ p in Work.BoseRowsFS.LatRiemann.hbox h m, Φ p / ‖p‖ ^ 2)
        - h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ 500 * A * h := by
  have h1 := nearCellsIntegralSum hh hA hcont hΦ Kr hKr
  have h2 := nearCellsValueSum hh hA hΦ Kr hKr
  have hsplit : ∑ m ∈ Kr, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
        - h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ ∑ m ∈ Kr, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)|
        + ∑ m ∈ Kr, |h ^ 3 * Φ (Work.BoseRowsFS.latPt h m)
            / ‖Work.BoseRowsFS.latPt h m‖ ^ 2| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun m _ => ?_)
    have hX := le_abs_self (∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
    have hX' := neg_le_abs (∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
    have hY := le_abs_self (h ^ 3 * Φ (Work.BoseRowsFS.latPt h m)
      / ‖Work.BoseRowsFS.latPt h m‖ ^ 2)
    have hY' := neg_le_abs (h ^ 3 * Φ (Work.BoseRowsFS.latPt h m)
      / ‖Work.BoseRowsFS.latPt h m‖ ^ 2)
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hAh : 0 ≤ A * h := mul_nonneg hA (le_of_lt hh)
  have hpi : (20 : ℝ) * Real.pi + 343 ≤ 500 := by linarith [Real.pi_lt_four]
  nlinarith [hsplit, h1, h2, hAh, hpi]

end Work.BoseRowsFS.LatRiemann
