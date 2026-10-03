import Mathlib
import Submission.Work.KMTAreas.A7LoPoly.varRhoFromGeneral
import Submission.Port.Aesm

/-!
# Finitely supported inputs to all inputs, for a *family* of variation caps

`Work.KMTAreas.A7LoPoly.varRhoFromGeneral` upgrades the `ℓᵖ`-bound for the `r`-variation
`varRhoFrom r κ` of the low-pass Ionescu--Wainger walk `n ↦ lpf ρ l₁ m₀ n f` from finitely
supported inputs to all inputs, at a *single* variation cap `κ`.  Here the cap is allowed to depend
on the major-arc parameters `(l₁, m₀)` through a family `K : ℕ → ℕ → ℕ`, and the finitely supported
bound is assumed for `K l₁ m₀` on each good major arc.  The proof is the same density/extension
argument, applied with `κ := K l₁ m₀`; the auxiliary lemmas of the sibling module
(`Work.KMTAreas.A7LoPoly.liminf_le_liminf_ennreal_of_eventually`,
`…exists_finsupp_coe_truncZ_aux`, `…norm_truncZ_le`, `…bound_of_memLp_count_ne_zero`,
`…kmtProj_tendsto_truncZ_of_pos`) are imported and reused verbatim.
-/

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory Filter Finset
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1000000

theorem varRhoFromGeneralK (ρ : ℝ) (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : 0 < p)
    (Cρ C : ℝ) (hC : 0 < C) (K : ℕ → ℕ → ℕ)
    (hfin : ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
      ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (K l₁ m₀)
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count) :
    ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (K l₁ m₀)
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  intro l₁ m₀ hgood f
  let κ : ℕ := K l₁ m₀
  rcases eq_or_ne (MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count) ⊤
    with htop | hne
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
    exact le_top
  · have hfmem : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
      (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hne))
    -- the variation is lower semicontinuous along the truncations
    have hpoint : ∀ y : ℤ,
        Work.BourgainPlan.Maximal.varRhoFrom r κ
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y)
        ≤ Filter.liminf (fun j : ℕ => Work.BourgainPlan.Maximal.varRhoFrom r κ
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
              (Work.KMTContract.truncZ j f) y)) Filter.atTop := by
      intro y
      refine Work.BourgainPlan.IonescuWainger.varRhoFrom_r_le_liminf hr κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y)
        (fun j n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
          (Work.KMTContract.truncZ j f) y) ?_
      intro n
      simpa only [Work.KMTAreas.A7Hi.lpf] using
        kmtProj_tendsto_truncZ_of_pos ρ l₁ (-((m₀ : ℤ) + (n : ℤ))) hp hfmem y
    -- Fatou for `eLpNorm`
    have hFat := Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
      (fun j y => Work.BourgainPlan.Maximal.varRhoFrom r κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
          (Work.KMTContract.truncZ j f) y))
      (fun y => Work.BourgainPlan.Maximal.varRhoFrom r κ
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f y))
      hp hpoint
    refine hFat.trans ?_
    -- the finitely supported bound, uniformly in the truncation parameter
    have hj : ∀ j : ℕ, MeasureTheory.eLpNorm (fun y : ℤ =>
          Work.BourgainPlan.Maximal.varRhoFrom r κ
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
              (Work.KMTContract.truncZ j f) y))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
      intro j
      obtain ⟨F, hF⟩ := exists_finsupp_coe_truncZ_aux j f
      have hb := hfin l₁ m₀ hgood F
      rw [hF] at hb
      exact hb.trans (mul_le_mul_right (MeasureTheory.eLpNorm_mono (hf := by pw_aesm) (norm_truncZ_le j f))
        (ENNReal.ofReal C))
    calc Filter.liminf (fun j : ℕ => MeasureTheory.eLpNorm (fun y : ℤ =>
            Work.BourgainPlan.Maximal.varRhoFrom r κ
              (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n
                (Work.KMTContract.truncZ j f) y))
            (ENNReal.ofReal p) MeasureTheory.Measure.count) Filter.atTop
        ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal C *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count)
            Filter.atTop :=
          liminf_le_liminf_ennreal_of_eventually (Filter.Eventually.of_forall hj)
      _ = ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := Filter.liminf_const _

end Work.KMTAreas.A7LoPoly
