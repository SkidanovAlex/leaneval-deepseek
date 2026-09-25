import Mathlib
import Submission.Work.BourgainPlan.Maximal.lwtCZDefs

/-!
# The CZ good part preserves the integral over a cell disjoint from the maximal cells

Let `σ : ℝ → ℝ≥0∞`, `c : ℝ≥0∞` and let `czMax σ c` be the maximal dyadic cells of the
Calderón--Zygmund decomposition of `σ` at height `c`, so that `lwtOm σ c = ⋃ p ∈ czMax σ c, dyCell p`
(see `lwtOm`).  Let `ψ : ℝ → ℝ` be nonnegative and integrable and let `lwtGood ψ σ c` be the
associated good part: it equals `ψ` off `lwtOm σ c` and equals the `ψ`-average over the (unique)
maximal CZ cell containing the point on `lwtOm σ c`.

If no maximal cell contains the dyadic cell `dyCell m k` (hypothesis `hR`), then every maximal cell
meeting `dyCell m k` is *strictly inside* `dyCell m k`; consequently `dyCell m k ∩ lwtOm σ c` is a
disjoint union of maximal CZ cells, and on each of them the good part has the same integral as `ψ`.

The main result `lintegral_lwtGood_eq` is the resulting identity

`∫⁻ y in dyCell m k, ofReal (lwtGood ψ σ c y) = ∫⁻ y in dyCell m k, ofReal (ψ y)`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- If no maximal CZ cell contains `dyCell m k`, then `dyCell m k ∩ lwtOm σ c` is exactly the union
of the maximal CZ cells that are contained in `dyCell m k` (a disjoint union). -/
lemma dyCell_inter_lwtOm_eq {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {m k : ℤ}
    (hR : ∀ p : ℤ × ℤ, p ∈ czMax σ c → ¬ dyCell m k ⊆ dyCell p.1 p.2) :
    dyCell m k ∩ lwtOm σ c
      = ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ c ∧ dyCell p.1 p.2 ⊆ dyCell m k},
          dyCell p.1.1 p.1.2 := by
  ext y
  constructor
  · rintro ⟨hyA, hyOm⟩
    rw [lwtOm, mem_iUnion₂] at hyOm
    obtain ⟨p, hp, hyp⟩ := hyOm
    rcases lt_trichotomy p.1 m with hlt | heq | hgt
    · exact mem_iUnion.mpr ⟨⟨p, hp, dyCell_subset_of_meet hlt.le hyp hyA⟩, hyp⟩
    · exfalso
      have hyA' : y ∈ dyCell p.1 k := by rw [heq]; exact hyA
      have hcell : dyCell m k = dyCell p.1 p.2 := by
        rw [← heq]
        exact (dyCell_eq_of_meet hyp hyA').symm
      exact hR p hp hcell.le
    · exact absurd (dyCell_subset_of_meet hgt.le hyA hyp) (hR p hp)
  · intro hy
    rcases mem_iUnion.mp hy with ⟨p, hyp⟩
    exact ⟨p.2.2 hyp, mem_iUnion₂.mpr ⟨p.1, p.2.1, hyp⟩⟩

/-- On a maximal CZ cell, the good part has the same integral as `ψ` (the average replaces `ψ`
without changing the integral). -/
lemma lintegral_lwtGood_dyCell_eq {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {ψ : ℝ → ℝ}
    (hψ : ∀ y, 0 ≤ ψ y) (hψint : MeasureTheory.Integrable ψ) {p : ℤ × ℤ}
    (hp : p ∈ czMax σ c) :
    ∫⁻ y in dyCell p.1 p.2, ENNReal.ofReal (lwtGood ψ σ c y)
      = ∫⁻ y in dyCell p.1 p.2, ENNReal.ofReal (ψ y) := by
  have hC : MeasurableSet (dyCell p.1 p.2) := dyCell_measurable _ _
  have h1 : ∫⁻ y in dyCell p.1 p.2, ENNReal.ofReal (lwtGood ψ σ c y)
      = ENNReal.ofReal (lwtCellAvg ψ p) * volume (dyCell p.1 p.2) := by
    have hcongr : EqOn (fun y => ENNReal.ofReal (lwtGood ψ σ c y))
        (fun _ => ENNReal.ofReal (lwtCellAvg ψ p)) (dyCell p.1 p.2) :=
      fun y hy => by
        show ENNReal.ofReal (lwtGood ψ σ c y) = ENNReal.ofReal (lwtCellAvg ψ p)
        rw [lwtGood_eq_lwtCellAvg hψ hp hy]
    rw [setLIntegral_congr_fun hC hcongr]
    exact setLIntegral_const _ _
  have h2 : ENNReal.ofReal (lwtCellAvg ψ p) * volume (dyCell p.1 p.2)
      = ENNReal.ofReal (∫ y in dyCell p.1 p.2, ψ y) := by
    rw [dyCell_volume_eq, ← ENNReal.ofReal_mul (lwtCellAvg_nonneg hψ p)]
    congr 1
    rw [lwtCellAvg, mul_assoc, mul_comm (∫ y in dyCell p.1 p.2, ψ y) ((2 : ℝ) ^ p.1),
      ← mul_assoc, inv_mul_cancel₀ (zpow_two_pos p.1).ne', one_mul]
  rw [h1, h2]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hψint.integrableOn (s := dyCell p.1 p.2))
    (Filter.Eventually.of_forall hψ)

theorem lintegral_lwtGood_eq {σ : ℝ → ENNReal} {c : ENNReal}
    {ψ : ℝ → ℝ} (hψ : ∀ y, 0 ≤ ψ y) (hψm : Measurable ψ) (hψint : MeasureTheory.Integrable ψ)
    {m k : ℤ}
    (hR : ∀ p : ℤ × ℤ, p ∈ Work.BourgainPlan.Maximal.czMax σ c →
      ¬ Work.BourgainPlan.Maximal.dyCell m k ⊆ Work.BourgainPlan.Maximal.dyCell p.1 p.2) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Work.BourgainPlan.Maximal.dyCell m k))
        (fun y => ENNReal.ofReal (Work.BourgainPlan.Maximal.lwtGood ψ σ c y))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Work.BourgainPlan.Maximal.dyCell m k))
        (fun y => ENNReal.ofReal (ψ y)) := by
  have hOm : MeasurableSet (lwtOm σ c) := measurableSet_lwtOm σ c
  have hCm : MeasurableSet (dyCell m k) := dyCell_measurable m k
  have hdisj : Pairwise (Function.onFun Disjoint
      fun p : {p : ℤ × ℤ // p ∈ czMax σ c ∧ dyCell p.1 p.2 ⊆ dyCell m k} =>
        dyCell p.1.1 p.1.2) := by
    intro p q hpq
    exact czMax_disjoint p.2.1 q.2.1 (fun h => hpq (Subtype.ext h))
  have hmeas : ∀ p : {p : ℤ × ℤ // p ∈ czMax σ c ∧ dyCell p.1 p.2 ⊆ dyCell m k},
      MeasurableSet (dyCell p.1.1 p.1.2) := fun p => dyCell_measurable _ _
  have hcover := dyCell_inter_lwtOm_eq (σ := σ) (c := c) (m := m) (k := k) hR
  have hsumG := lintegral_iUnion (μ := volume) hmeas hdisj (fun y => ENNReal.ofReal (lwtGood ψ σ c y))
  have hsumF := lintegral_iUnion (μ := volume) hmeas hdisj (fun y => ENNReal.ofReal (ψ y))
  have hcell : ∀ p : {p : ℤ × ℤ // p ∈ czMax σ c ∧ dyCell p.1 p.2 ⊆ dyCell m k},
      ∫⁻ y in dyCell p.1.1 p.1.2, ENNReal.ofReal (lwtGood ψ σ c y)
        = ∫⁻ y in dyCell p.1.1 p.1.2, ENNReal.ofReal (ψ y) :=
    fun p => lintegral_lwtGood_dyCell_eq hψ hψint p.2.1
  have hIntOm : ∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y)
      = ∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (ψ y) := by
    rw [hcover, hsumG, hsumF]
    exact tsum_congr hcell
  have hsdiff : ∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y)
      = ∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (ψ y) := by
    refine setLIntegral_congr_fun (hCm.diff hOm) (fun y hy => ?_)
    show ENNReal.ofReal (lwtGood ψ σ c y) = ENNReal.ofReal (ψ y)
    rw [lwtGood_of_notMem hy.2]
  have hsplitG : ∫⁻ y in dyCell m k, ENNReal.ofReal (lwtGood ψ σ c y)
      = (∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y))
        + (∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y)) :=
    (lintegral_inter_add_sdiff (μ := volume) (fun y => ENNReal.ofReal (lwtGood ψ σ c y))
      (dyCell m k) hOm).symm
  have hsplitF : ∫⁻ y in dyCell m k, ENNReal.ofReal (ψ y)
      = (∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (ψ y))
        + (∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (ψ y)) :=
    (lintegral_inter_add_sdiff (μ := volume) (fun y => ENNReal.ofReal (ψ y))
      (dyCell m k) hOm).symm
  calc ∫⁻ y in dyCell m k, ENNReal.ofReal (lwtGood ψ σ c y)
      = (∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y))
        + (∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (lwtGood ψ σ c y)) := hsplitG
    _ = (∫⁻ y in dyCell m k ∩ lwtOm σ c, ENNReal.ofReal (ψ y))
        + (∫⁻ y in dyCell m k \ lwtOm σ c, ENNReal.ofReal (ψ y)) := by rw [hIntOm, hsdiff]
    _ = ∫⁻ y in dyCell m k, ENNReal.ofReal (ψ y) := hsplitF.symm

end Work.BourgainPlan.Maximal
