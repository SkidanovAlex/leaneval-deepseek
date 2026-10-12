import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LGW.PeriodiseLe` — the periodisation estimate

Let `g : ℝ³ → ℝ` be continuous, nonnegative, bounded by `B ≥ 0` and supported in the ball
`‖x‖ ≤ 2ℓ`, and let `u : ℝ³ → ℝ` be continuous, nonnegative and periodic for the lattice
`ℓℤ³` (`u (x + lat ℓ n) = u x`).  Then

    ∫ g u ≤ 125 · B · ∫_{cell ℓ} u .

The constant is the number of cells of the `ℓℤ³`-tiling that meet the ball of radius `2ℓ`:
a point of that ball has all coordinates in `[-2ℓ, 2ℓ]`, hence lies in one of the boxes
`cell ℓ + lat ℓ n` with `|n i| ≤ 2` (`5³ = 125` boxes).

Route (all in `Submission/Work/BoseFixR/`):

* `tiling_integral` — the tiling identity `∫_ℝ³ f = Σ'_n ∫_{cell ℓ} f(· + lat ℓ n)`;
* off the finite index set `K = {n | ∀ i, |n i| ≤ 2}` the summand vanishes on `cell ℓ`
  (a non-zero `g (x + lat ℓ n)` forces `‖x + lat ℓ n‖ ≤ 2ℓ`, whence `|ℓ n i| ≤ 2ℓ + ℓ/2`),
  so the `tsum` collapses to the finite sum over `K` (`tsum_eq_sum`);
* periodicity of `u` turns each summand into `∫_{cell ℓ} g (· + lat ℓ n) · u`;
* `Finset.sum_le_card_nsmul` bounds the "fold" `Σ_{n ∈ K} g (x + lat ℓ n) ≤ 125 B` on the cell;
* `setIntegral_mono_on` and `integral_const_mul` finish.
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter Metric

namespace Work.BoseFixR.LGW

set_option linter.unusedVariables false

theorem PeriodiseLe {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {g u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B)
    (hgsupp : ∀ x, 2 * ℓ < ‖x‖ → g x = 0)
    (hgc : Continuous g) (hu0 : ∀ x, 0 ≤ u x) (huc : Continuous u)
    (huper : ∀ (n : Fin 3 → ℤ) (x : EuclideanSpace ℝ (Fin 3)),
      u (x + Work.BoseFixR.lat ℓ n) = u x) :
    ∫ x, g x * u x ≤ 125 * B * ∫ y in Work.BoseFixR.cell ℓ, u y := by
  classical
  have hcellmeas : MeasurableSet (Work.BoseFixR.cell ℓ) := Work.BoseFixR.measurableSet_boxL ℓ
  have hcomp : IsCompact (Work.BoseFixR.cell ℓ) := by
    have h : Work.BoseFixR.cell ℓ = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
        (Set.Icc (fun _ : Fin 3 => -(ℓ / 2)) (fun _ => ℓ / 2)) := by
      ext y
      simp only [Work.BoseFixR.cell, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc,
        Pi.le_def, abs_le]
      exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
    rw [h]
    exact (Homeomorph.isCompact_preimage _).mpr isCompact_Icc
  -- integrability of the product `g·u` (continuous, compactly supported)
  have hsupp_g : Function.support g ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * ℓ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hx (hgsupp x (not_le.mp h))
  have hcs2 : HasCompactSupport (fun x => g x * u x) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * ℓ))
      (fun x hx => hsupp_g (by
        rw [Function.mem_support] at hx ⊢
        intro hg0
        exact hx (by rw [hg0, zero_mul])))
  have hf_int : Integrable (fun x => g x * u x) :=
    (hgc.mul huc).integrable_of_hasCompactSupport hcs2
  -- the 125 lattice labels of the cells meeting the ball of radius `2ℓ`
  set K : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2)
    with hKdef
  have hmemK : ∀ n : Fin 3 → ℤ, n ∈ K ↔ ∀ i, |n i| ≤ 2 := by
    intro n
    rw [hKdef, Fintype.mem_piFinset]
    exact forall_congr' (fun i => by rw [Finset.mem_Icc, abs_le])
  have hcardK : K.card = 125 := by
    rw [hKdef, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [Int.card_Icc]
  -- off `K` the translated `g` vanishes on the cell
  have hzero : ∀ n : Fin 3 → ℤ, n ∉ K → ∀ x ∈ Work.BoseFixR.cell ℓ,
      g (x + Work.BoseFixR.lat ℓ n) = 0 := by
    intro n hnK x hx
    by_contra hne
    apply hnK
    rw [hmemK]
    intro i
    have hnorm : ‖x + Work.BoseFixR.lat ℓ n‖ ≤ 2 * ℓ := by
      by_contra h
      exact hne (hgsupp _ (not_le.mp h))
    have hxi : |x i| ≤ ℓ / 2 := hx i
    have hcoord : |(x + Work.BoseFixR.lat ℓ n) i| ≤ 2 * ℓ :=
      le_trans (by simpa using PiLp.norm_apply_le (x + Work.BoseFixR.lat ℓ n) i) hnorm
    have hsub : (x + Work.BoseFixR.lat ℓ n) i - x i = ℓ * (n i : ℝ) := by
      simp [Work.BoseFixR.lat]
    have hle : |ℓ * (n i : ℝ)| ≤ 2 * ℓ + ℓ / 2 := by
      calc |ℓ * (n i : ℝ)| = |(x + Work.BoseFixR.lat ℓ n) i - x i| := by rw [hsub]
        _ ≤ |(x + Work.BoseFixR.lat ℓ n) i| + |x i| := by
              simpa using abs_sub_le ((x + Work.BoseFixR.lat ℓ n) i) 0 (x i)
        _ ≤ 2 * ℓ + ℓ / 2 := add_le_add hcoord hxi
    have habs : |(n i : ℝ)| ≤ 5 / 2 := by
      rw [abs_mul, abs_of_pos hℓ] at hle
      have h2 : ℓ * |(n i : ℝ)| ≤ ℓ * (5 / 2) := by linarith
      exact le_of_mul_le_mul_left h2 hℓ
    have hfloor : ⌊(5 : ℝ) / 2⌋ = (2 : ℤ) := by norm_num
    have : |n i| ≤ 2 := by
      rw [← hfloor]
      exact Int.le_floor.mpr (by rw [Int.cast_abs]; simpa using habs)
    exact this
  -- the tiling identity
  have h1 : ∫ x, g x * u x
      = ∑' n, ∫ x in Work.BoseFixR.cell ℓ,
          g (x + Work.BoseFixR.lat ℓ n) * u (x + Work.BoseFixR.lat ℓ n) :=
    Work.BoseFixR.tiling_integral hℓ (fun x => g x * u x) hf_int
  -- periodicity of `u`
  have h2 : ∑' n, ∫ x in Work.BoseFixR.cell ℓ,
        g (x + Work.BoseFixR.lat ℓ n) * u (x + Work.BoseFixR.lat ℓ n)
      = ∑' n, ∫ x in Work.BoseFixR.cell ℓ, g (x + Work.BoseFixR.lat ℓ n) * u x := by
    refine tsum_congr (fun n => ?_)
    exact MeasureTheory.setIntegral_congr_fun hcellmeas (fun x _ => by rw [huper n x])
  -- only the finitely many labels in `K` contribute
  have h3 : ∑' n, ∫ x in Work.BoseFixR.cell ℓ, g (x + Work.BoseFixR.lat ℓ n) * u x
      = ∑ n ∈ K, ∫ x in Work.BoseFixR.cell ℓ, g (x + Work.BoseFixR.lat ℓ n) * u x := by
    refine tsum_eq_sum (s := K) (fun n hn => ?_)
    rw [show (∫ x in Work.BoseFixR.cell ℓ, g (x + Work.BoseFixR.lat ℓ n) * u x)
        = ∫ x in Work.BoseFixR.cell ℓ, (0 : ℝ) from
      MeasureTheory.setIntegral_congr_fun hcellmeas
        (fun x hx => by rw [hzero n hn x hx, zero_mul])]
    simp
  -- recombine the finite sum into the integral of the fold
  have h4 : ∑ n ∈ K, ∫ x in Work.BoseFixR.cell ℓ, g (x + Work.BoseFixR.lat ℓ n) * u x
      = ∫ x in Work.BoseFixR.cell ℓ, (∑ n ∈ K, g (x + Work.BoseFixR.lat ℓ n)) * u x := by
    rw [← MeasureTheory.integral_finsetSum]
    · exact MeasureTheory.setIntegral_congr_fun hcellmeas (fun x _ => by rw [Finset.sum_mul])
    · intro n hn
      exact ContinuousOn.integrableOn_compact hcomp
        ((hgc.comp (continuous_id.add continuous_const)).mul huc).continuousOn
  have hcontfold : Continuous (fun x => ∑ n ∈ K, g (x + Work.BoseFixR.lat ℓ n)) :=
    continuous_finsetSum K (fun n _ => hgc.comp (continuous_id.add continuous_const))
  -- the fold is at most `125 · B` on the cell
  have h5 : ∫ x in Work.BoseFixR.cell ℓ, (∑ n ∈ K, g (x + Work.BoseFixR.lat ℓ n)) * u x
      ≤ ∫ x in Work.BoseFixR.cell ℓ, (125 * B) * u x := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hcellmeas (fun x hx => ?_)
    · exact ContinuousOn.integrableOn_compact hcomp (hcontfold.mul huc).continuousOn
    · exact ContinuousOn.integrableOn_compact hcomp (continuous_const.mul huc).continuousOn
    · have hG : ∑ n ∈ K, g (x + Work.BoseFixR.lat ℓ n) ≤ 125 * B := by
        have h := Finset.sum_le_card_nsmul K (fun n => g (x + Work.BoseFixR.lat ℓ n)) B
          (fun n _ => hgB _)
        rw [hcardK] at h
        simpa using h
      exact mul_le_mul_of_nonneg_right hG (hu0 x)
  have h6 : ∫ x in Work.BoseFixR.cell ℓ, (125 * B) * u x
      = 125 * B * ∫ x in Work.BoseFixR.cell ℓ, u x := by
    rw [MeasureTheory.integral_const_mul]
  calc ∫ x, g x * u x
      = _ := h1
    _ = _ := h2
    _ = _ := h3
    _ = _ := h4
    _ ≤ _ := h5
    _ = 125 * B * ∫ y in Work.BoseFixR.cell ℓ, u y := h6

end Work.BoseFixR.LGW
