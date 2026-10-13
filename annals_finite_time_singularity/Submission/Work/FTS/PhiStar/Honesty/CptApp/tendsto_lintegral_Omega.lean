/-
# `tendsto_lintegral_Omega`: the tail of the `ℋ^k`-energy over the shrinking region

`Work.FTS.PhiStar.Honesty.CptApp.tendsto_lintegral_Omega`: for `F ∈ ℋ^k` (i.e. `HkMem α k F`,
`Submission/Work/Spaces/Defs.lean`),

  `∫⁻_{(Ω_n ∩ Dom)} ofReal (HkIntegrand α k F) ⟶ 0`  as `n → ∞`,

where `Ω_n` is the shrinking region
`{z < 2/n} ∪ {n < z} ∪ {θ < 2/n} ∪ {π/2 - 2/n < θ}` of `CptApp/Defs.lean`, on which the
cutoffs `chiR n`, `zetaR n` of the approximation `approx n F` are not both equal to `1`.

## Route

* `Ω_n ∩ Dom` is *antitone* for `n ≥ 1` (`Omega_succ_subset`), and its intersection
  over the shifted index `n ↦ n+1` is contained in the coordinate lines
  `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` (`Omega_iInter_subset_boundary`), a Lebesgue-null set
  (`volume_boundary_union_zero`).  (Note that the intersection is *not* empty: the three
  coordinate lines belong to every `Ω_{n+1} ∩ Dom`; it is only null.)
* The `lintegral` of `ofReal (HkIntegrand α k F)` over `Dom` is finite: `HkMem` gives the
  integrability of the slices `θ ↦ HkIntegrand α k F z θ` for every `z ∈ Iz` and the
  integrability of `z ↦ ∫_θ HkIntegrand α k F z θ`; the inequality form of Tonelli
  (`lintegral_prod_le`, which needs **no** joint measurability, unlike `lintegral_prod`)
  converts the product integral into the iterated one, which
  `ofReal_integral_eq_lintegral_ofReal` then evaluates.
* Put `ν := (volume.restrict Dom).withDensity (ofReal ∘ HkIntegrand)`; then
  `ν (Ω_n ∩ Dom)` *is* the `lintegral` in question, `ν` is a finite measure, and continuity of a
  finite measure from above (`tendsto_measure_iInter_atTop`) gives `ν (Ω_{n+1} ∩ Dom) → 0`.
  The sequence is shifted once (`Ω_{n+1}` is antitone in `n` from the start, `Ω_n` only from
  `n = 1`, because `Ω_0` evaluates `2 / 0 = 0`).

Nothing here uses measurability of `(z,θ) ↦ HkIntegrand α k F z θ` (which `HkMem` does not
provide); the only measure-theoretic input is the inequality form of Tonelli.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Omega_succ_subset
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Omega_iInter_subset_boundary
import Submission.Work.FTS.PhiStar.Honesty.CptApp.volume_boundary_union_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

theorem tendsto_lintegral_Omega {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k F) :
    Filter.Tendsto (fun n : ℕ =>
        MeasureTheory.lintegral
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Work.FTS.PhiStar.Honesty.CptApp.Omega n ∩ Work.Spaces.Dom))
          (fun p => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)))
      Filter.atTop (nhds 0) := by
  classical
  set g : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2) with hg
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIth : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hDom : MeasurableSet Work.Spaces.Dom := hIz.prod hIth
  have hOmeas : ∀ n : ℕ, MeasurableSet (Omega n ∩ Work.Spaces.Dom) :=
    fun n => (Omega_measurable n).inter hDom
  -- Finiteness of the total integral over `Dom`.
  have hprod : (volume : Measure (ℝ × ℝ)).restrict Work.Spaces.Dom
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Dom]
    exact (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  have hfin : ∫⁻ p, g p ∂(volume.restrict Work.Spaces.Dom) < ⊤ := by
    calc ∫⁻ p, g p ∂(volume.restrict Work.Spaces.Dom)
        = ∫⁻ p, g p ∂((volume.restrict Work.Spaces.Iz).prod
            (volume.restrict Work.Spaces.Iθ)) := by
          rw [hprod]
      _ ≤ ∫⁻ z, ∫⁻ θ, g (z, θ) ∂(volume.restrict Work.Spaces.Iθ)
              ∂(volume.restrict Work.Spaces.Iz) := lintegral_prod_le g
      _ = ∫⁻ z, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
              ∂(volume.restrict Work.Spaces.Iz) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
          exact (ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)).symm
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hF.2]
          exact Eventually.of_forall fun z =>
            integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- The finite measure `ν` whose masses are the wanted lintegrals.
  set ν : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Dom).withDensity g with hν
  have hνuniv : ν Set.univ < ⊤ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ]
    simpa using hfin
  have hA : ∀ n : ℕ,
      (∫⁻ p, g p ∂(volume.restrict (Omega n ∩ Work.Spaces.Dom)))
        = ν (Omega n ∩ Work.Spaces.Dom) := by
    intro n
    rw [hν, withDensity_apply _ (hOmeas n), Measure.restrict_restrict (hOmeas n),
      Set.inter_assoc, Set.inter_self]
  -- The decreasing family `t n = Ω_{n+1} ∩ Dom`.
  set t : ℕ → Set (ℝ × ℝ) := fun n => Omega (n + 1) ∩ Work.Spaces.Dom with ht
  have ht_meas : ∀ n : ℕ, MeasurableSet (t n) := fun n => hOmeas (n + 1)
  have ht_anti : Antitone t := antitone_nat_of_succ_le fun n =>
    Set.inter_subset_inter (Omega_succ_subset (m := n + 1) (by omega)) (subset_refl _)
  have hνt0 : ν (t 0) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) hνuniv).ne
  have hνnull : ν (⋂ n, t n) = 0 := by
    have hBmeas : MeasurableSet ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) :=
      ((measurable_fst (measurableSet_singleton 0)).union
        (measurable_snd (measurableSet_singleton 0))).union
        (measurable_snd (measurableSet_singleton _))
    have hbase : (volume.restrict Work.Spaces.Dom)
        ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
          ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
      rw [Measure.restrict_apply hBmeas]
      exact measure_mono_null Set.inter_subset_left volume_boundary_union_zero
    have hνB : ν ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
      rw [hν, withDensity_apply' g _]
      exact setLIntegral_measure_zero _ g hbase
    exact measure_mono_null Omega_iInter_subset_boundary hνB
  have hlim : Tendsto (fun n => ν (t n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := t)
      (fun n => (ht_meas n).nullMeasurableSet) ht_anti ⟨0, hνt0⟩
    rw [hνnull] at h
    exact h
  -- `ν (Ω_{n+1} ∩ Dom)` is the lintegral of the shifted index.
  have hshift : Tendsto (fun n : ℕ =>
      ∫⁻ p, g p ∂(volume.restrict (Omega (n + 1) ∩ Work.Spaces.Dom))) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards with n
    exact (hA (n + 1)).symm
  -- Shift the index back: `Ω_n = Ω_{(n-1)+1}` for `n ≥ 1`.
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun a ha => by omega⟩
  have hcomp : Tendsto (fun n : ℕ =>
      ∫⁻ p, g p ∂(volume.restrict (Omega (n - 1 + 1) ∩ Work.Spaces.Dom))) atTop (𝓝 0) :=
    hshift.comp hpred
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Nat.sub_add_cancel hn]

end Work.FTS.PhiStar.Honesty.CptApp
