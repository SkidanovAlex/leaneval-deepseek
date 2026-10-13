import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1
import Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- The two endpoints `0`, `π/2` carry no mass, so `Iθ` and the open interval define the same
restricted measure; hence integrability on the open interval transfers to `Iθ`. -/
private theorem integrableOn_Iθ_of_integrableOn_Ioo {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  show MeasureTheory.Integrable f (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hms]
  exact h

/-- **Integrability of the `Lzero1`-integrands on `Iθ`.**

For `v` of class `C²` within `[0, π/2]` whose `Lzero1 v` is bounded on the open interval
(hypothesis `hbdd`, supplied by the companion lemma `lzero1_bdd_on_Ioo`), the two integrands that
the `e_m`-pairing argument needs are `Iθ`-integrable:

* `θ ↦ (Lzero1 v θ)² · cos θ`  (the numerator of the mode bound), and
* `θ ↦ Lzero1 v θ · eFam m θ · cos θ`  (the pairing integrand).

The junk values of the total `deriv` at the two endpoints `0, π/2` are irrelevant: they form a
null set for `volume.restrict Iθ`.

*Route.*  `Ioo 0 (π/2)` is conull in `Iθ` (`Measure.restrict_congr_set` applied to
`MeasureTheory.Ioo_ae_eq_Icc`), so it suffices to prove the two `IntegrableOn (… (Ioo 0 (π/2)))`.
There `θ ↦ Lzero1 v θ` is continuous (`SliceLocal.continuousOn_Lzero1_of_contDiffOn_two`, from the
`ContDiffOn ℝ 2` datum restricted to the open interval), hence a.e.-strongly measurable; each
integrand is the product of `Lzero1 v` (bounded by `hbdd` on `Ioo`) with bounded factors
(`|eFam m θ · cos θ| ≤ C_φ` by `exists_bound_eFam_mul_cos`, `|Real.cos θ| ≤ 1`), so
`IntegrableOn.of_bound` applies because `volume (Ioo 0 (π/2)) < ⊤`. -/
theorem integrableOn_Lzero1_mul_cos {v : ℝ → ℝ} {m : ℕ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.EllipticEst.Lzero1 v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 v θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) Work.Spaces.Iθ := by
  obtain ⟨M, hM⟩ := hbdd
  -- `M` is nonnegative (evaluate the bound at an interior point)
  have hM0 : 0 ≤ M := by
    have h45 : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hM (Real.pi / 4) h45)
  -- the open interval has finite measure
  have hfin : MeasureTheory.volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  -- `Lzero1 v` is continuous on the open interval
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcL : ContinuousOn (Work.FTS.EllipticEst.Lzero1 v)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two v (hv.mono hsub)
  -- `eFam m` is continuous
  have hcont_eFam : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
    change Continuous (fun θ : ℝ => Real.cos θ
      * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  -- the uniform bound `|eFam m θ · cos θ| ≤ Cφ` on `Iθ`
  obtain ⟨Cφ, hCφ0, hCφ⟩ := Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos m
  have hbdI : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ Cφ :=
    fun θ hθ => hCφ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  constructor
  · refine integrableOn_Iθ_of_integrableOn_Ioo
      (MeasureTheory.IntegrableOn.of_bound hfin ?_ (M ^ 2) ?_)
    · exact ((hcL.pow 2).mul Real.continuous_cos.continuousOn).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hb : |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M := hM θ hθ
      have hb2 : |Work.FTS.EllipticEst.Lzero1 v θ| ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc |Work.FTS.EllipticEst.Lzero1 v θ| ^ 2 * |Real.cos θ|
          ≤ M ^ 2 * 1 := mul_le_mul hb2 hc (abs_nonneg _) (sq_nonneg M)
        _ = M ^ 2 := by ring
  · refine integrableOn_Iθ_of_integrableOn_Ioo
      (MeasureTheory.IntegrableOn.of_bound hfin ?_ (M * Cφ) ?_)
    · exact (((hcL.mul hcont_eFam.continuousOn).mul
        Real.continuous_cos.continuousOn).aestronglyMeasurable measurableSet_Ioo)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hb : |Work.FTS.EllipticEst.Lzero1 v θ| ≤ M := hM θ hθ
      have he : |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ Cφ := hbdI θ hθ
      rw [Real.norm_eq_abs]
      have hre : Work.FTS.EllipticEst.Lzero1 v θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Real.cos θ
          = Work.FTS.EllipticEst.Lzero1 v θ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by ring
      rw [hre, abs_mul]
      exact mul_le_mul hb he (abs_nonneg _) hM0

end Work.FTS.PhiStar.Honesty
