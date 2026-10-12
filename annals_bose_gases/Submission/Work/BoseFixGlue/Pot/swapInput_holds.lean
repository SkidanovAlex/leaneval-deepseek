import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Pot.abs_potWordU_le
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
import Submission.Work.BoseFixGlue.Pot.ellB_ge
import Submission.Work.BoseFixGlue.Pot.integrable_abox_pair_domination
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Pot.swapInput_holds` — the `swap` clause of the C-side inputs

This module discharges `Work.BoseFixGlue.SwapInput` (`Work/BoseFixGlue/Residuals.lean`), the
joint `(u,x)`-integrability of `Φ²·potWordU` — the Fubini input of FS `lem:LocPotential`
consumed by `Work.BoseKinLoc.Compare.compare_box_energy_v2`.

## What is proved

There is `ε₀ > 0` such that for every admissible chemical potential (`Adm v ε₀ μ`), every
particle number `N`, every box side `L ≥ ℓ(μ) := ℓB v μ` and every smooth state `Φ`
supported in the centred box `abox N L`, the function

`(u,x) ↦ (Φ x)² · potWordU N v (g₀ v h) (ℓB v μ) μ u x`

is integrable on `volume.prod volume`.

## Route

Write `U := coverBoxU (ℓB v μ) L` for the support-adapted localisation cover.  The integrand
is dominated pointwise by

`G(u,x) := 1_U(u) · (Φ x)² · (A + B·Σ_{q∈pairSet N} |v(x_{q.1}−x_{q.2})|)`,
`A := |μ|·N·(2·chiSup²·∫|g₀|)`, `B := 2·chiSup²`,

because

* on `abox N L` with `u ∈ U` the pointwise bound `abs_potWordU_le` applies termwise
  (`abs_potBr_le` for the chemical part, `abs_wLoc_pair_le` for the pairs), and the sum over
  the subtype `{i < j}` is dominated by the sum over the corpus' `pairSet N` (all ordered
  pairs, nonnegative summands);
* off `abox N L` the state `Φ` vanishes, and off `U` the word `potWordU` vanishes
  (`potWordU_eq_zero_of_not_mem_coverBoxU`).

`G` is a product of a function of `u` (the indicator of `U`, integrable because
`volume U = (L+ℓ)³/ℓ³ < ∞`) and a function of `x` (integrable by
`integrable_abox_pair_domination`), hence integrable on the product measure
(`Integrable.mul_prod`); the a.e. strong measurability of the integrand is
`aestronglyMeasurable_potWordU_weight` (with `MemLp v 1` supplying the a.e. measurability of
`v` and `g₀`).  `Integrable.mono'` finishes.  The diluteness threshold is supplied by
`ellB_ge`, which also gives the positivity of the box side needed by the cover.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Work.BoseFixGlue.Pot

set_option linter.style.haveILetI false

theorem swapInput_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ Work.BoseFixGlue.SwapInput v h ε₀ := by
  obtain ⟨ε₀, hε₀, hprop⟩ := ellB_ge (v := v) (R := R) hav hR
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hμ N L hL Φ hΦ hsym hsupp
  obtain ⟨hμpos, hμle, _⟩ := hμ
  obtain ⟨hℓpos, hRℓ⟩ := hprop μ hμpos hμle
  have hLpos : 0 < L := lt_of_lt_of_le hℓpos hL
  have hC : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ Submission.BoseGases.chiR0 →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z :=
    fun z hz => Submission.BoseGases.chiR0_half z hz
  -- ## the dominating function is integrable
  have hGint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        (Work.BoseKinLoc.Compare.coverBoxU (Work.BoseFixGlue.ℓB v μ) L).indicator
            (fun _ => (1 : ℝ)) p.1 *
          ((Φ p.2) ^ 2 *
            (|μ| * ((N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h))
              + (2 * Work.BoseBox.chiSup ^ 2) *
                  (∑ q ∈ Submission.BoseGases.pairSet N, |v (p.2 q.1 - p.2 q.2)|))))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) := by
    have hUmeas : MeasurableSet
        (Work.BoseKinLoc.Compare.coverBoxU (Work.BoseFixGlue.ℓB v μ) L) :=
      Work.BoseKinLoc.Compare.measurableSet_coverBoxU hℓpos hLpos.le
    have hUfin : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Work.BoseKinLoc.Compare.coverBoxU (Work.BoseFixGlue.ℓB v μ) L) ≠ ∞ := by
      rw [Work.BoseKinLoc.Compare.volume_coverBoxU hℓpos hLpos.le]
      exact ENNReal.ofReal_ne_top
    have h1 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseKinLoc.Compare.coverBoxU (Work.BoseFixGlue.ℓB v μ) L).indicator
          (fun _ => (1 : ℝ)) u)
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      (MeasureTheory.integrable_indicator_iff hUmeas).mpr
        (MeasureTheory.integrableOn_const hUfin (by simp))
    have h2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 *
          (|μ| * ((N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h))
            + (2 * Work.BoseBox.chiSup ^ 2) *
                (∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|)))
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N)) :=
      integrable_abox_pair_domination hLpos hv1 hΦ hsupp
    exact h1.mul_prod h2
  -- ## a.e. strong measurability of the integrand
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        (Φ p.2) ^ 2 * Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h)
          (Work.BoseFixGlue.ℓB v μ) μ p.1 p.2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
    aestronglyMeasurable_potWordU_weight hv1.aemeasurable
      (Submission.BoseGases.g0_integrable hR hv_supp h).aemeasurable hΦ.continuous
  -- ## the pointwise domination
  refine MeasureTheory.Integrable.mono' hGint hFmeas ?_
  filter_upwards with p
  by_cases hx : p.2 ∈ Submission.BoseGases.abox N L
  · by_cases hu : p.1 ∈ Work.BoseKinLoc.Compare.coverBoxU (Work.BoseFixGlue.ℓB v μ) L
    · have hb := abs_potWordU_le (N := N) (h := h) (R := R)
        (r₀ := Submission.BoseGases.chiR0) (ℓ := Work.BoseFixGlue.ℓB v μ) (μ := μ)
        hR hv_supp hC hℓpos hRℓ p.1 p.2
      -- the subtype pair-sum is dominated by the corpus' `pairSet` pair-sum
      have hkey : (∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
            |v (p.2 ij.1.1 - p.2 ij.1.2)|)
          = ∑ q ∈ (Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2)),
              |v (p.2 q.1 - p.2 q.2)| :=
        (Finset.sum_subtype
          (s := Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2))
          (fun q => by simp) (fun q => |v (p.2 q.1 - p.2 q.2)|)).symm
      have hmono : (∑ q ∈ (Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2)),
            |v (p.2 q.1 - p.2 q.2)|)
          ≤ ∑ q ∈ Submission.BoseGases.pairSet N, |v (p.2 q.1 - p.2 q.2)| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq => by
            simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
              true_and] at hq ⊢
            exact ne_of_lt hq)
          (fun q _ _ => abs_nonneg _)
      have hstep : Work.BoseBox.chiSup ^ 2 *
            (∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              (2 : ℝ) * |v (p.2 ij.1.1 - p.2 ij.1.2)|)
          ≤ (2 * Work.BoseBox.chiSup ^ 2) *
              (∑ q ∈ Submission.BoseGases.pairSet N, |v (p.2 q.1 - p.2 q.2)|) := by
        rw [← Finset.mul_sum]
        have h2 : (∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              |v (p.2 ij.1.1 - p.2 ij.1.2)|)
            ≤ ∑ q ∈ Submission.BoseGases.pairSet N, |v (p.2 q.1 - p.2 q.2)| := by
          rw [hkey]; exact hmono
        calc Work.BoseBox.chiSup ^ 2 *
              (2 * (∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
                |v (p.2 ij.1.1 - p.2 ij.1.2)|))
            = (2 * Work.BoseBox.chiSup ^ 2) *
                (∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
                  |v (p.2 ij.1.1 - p.2 ij.1.2)|) := by ring
          _ ≤ (2 * Work.BoseBox.chiSup ^ 2) *
                (∑ q ∈ Submission.BoseGases.pairSet N, |v (p.2 q.1 - p.2 q.2)|) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) (sq_nonneg _))
      rw [Set.indicator_of_mem hu, one_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (Φ p.2))]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Φ p.2))
      exact le_trans hb (add_le_add (le_refl _) hstep)
    · have hpz : Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h)
          (Work.BoseFixGlue.ℓB v μ) μ p.1 p.2 = 0 :=
        Work.BoseKinLoc.Compare.potWordU_eq_zero_of_not_mem_coverBoxU hℓpos hx hu
      rw [Set.indicator_of_notMem hu, zero_mul, hpz, mul_zero, norm_zero]
  · have hΦ0 : Φ p.2 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Φ) (fun hmem => hx (hsupp hmem))
    rw [hΦ0]
    simp

end Work.BoseFixGlue.Pot
