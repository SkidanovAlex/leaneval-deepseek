import Mathlib


set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

-- Note for the prover: the identity `s.indicator f + sᶜ.indicator f = f` is available as
-- `Commons.Analysis.MeasureTheory.banach_indicator_add_compl` (file
-- Submission/Commons/Analysis/MeasureTheory/marcinkiewicz_weak_one_strong_two_banach.lean); the
-- `p₀ = ∞` analogue of this statement is `Work.BourgainPlan.Maximal.weak_type_truncation_bound`
-- in Submission/Work/BourgainPlan/Maximal/weak_type_truncation_bound.lean (that file should be
-- importable for the pattern).
theorem two_weak_truncation_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    (T : (α → ℂ) → (β → ENNReal))
    (hsub : ∀ f h : α → ℂ, ∀ x : β, T (f + h) x ≤ T f x + T h x)
    {q p₀ A B : ℝ} (hq : 0 < q) (hp₀ : 0 < p₀)
    (hweakq : ∀ (f : α → ℂ) (lam : ℝ), 0 < lam →
      ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal (A / lam) ^ q * (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q)
    (hweakp : ∀ (f : α → ℂ) (lam : ℝ), 0 < lam →
      ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal (B / lam) ^ p₀ * (MeasureTheory.eLpNorm f (ENNReal.ofReal p₀) μ) ^ p₀)
    (f : α → ℂ) (hf : AEStronglyMeasurable f μ) {lam σ : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          MeasureTheory.lintegral μ
            (fun x => Set.indicator {x : α | σ * lam < ‖f x‖}
              (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x)
        + ENNReal.ofReal (2 * B / lam) ^ p₀ *
          MeasureTheory.lintegral μ
            (fun x => Set.indicator {x : α | ‖f x‖ ≤ σ * lam}
              (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x) := by
  set S : Set α := {x : α | σ * lam < ‖f x‖} with hS
  set S' : Set α := {x : α | ‖f x‖ ≤ σ * lam} with hS'
  have hSc : S' = Sᶜ := by
    rw [hS', hS]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact not_lt.symm
  set h : α → ℂ := S.indicator f with hh
  set g : α → ℂ := S'.indicator f with hg
  have hgh : h + g = f := by
    rw [hh, hg, hSc]
    funext x
    rw [Pi.add_apply]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem ((Set.mem_compl_iff S x).mpr hx)]
      simp
  have hhm : AEStronglyMeasurable h μ := by
    have hF : Measurable (fun z : ℂ => Set.indicator {z : ℂ | σ * lam < ‖z‖} id z) :=
      measurable_id.indicator (measurableSet_lt measurable_const measurable_norm)
    exact (hF.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ := by
    have hF : Measurable (fun z : ℂ => Set.indicator {z : ℂ | ‖z‖ ≤ σ * lam} id z) :=
      measurable_id.indicator (measurableSet_le measurable_norm measurable_const)
    exact (hF.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  -- the `L^q` identity for the high part
  have hHeq : (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q
      = ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal q)
        (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hhm, ENNReal.toReal_ofReal hq.le]
    rw [← ENNReal.rpow_mul, show (1 / q) * q = 1 by field_simp, ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [hh, enorm_indicator_eq_indicator_enorm]
    rw [show (Set.indicator S (fun a => ‖f a‖ₑ) x) ^ q
          = Set.indicator S (fun a => (‖f a‖ₑ) ^ q) x from by
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq]]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hq.le]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  -- the `L^{p₀}` identity for the low part
  have hGeq : (MeasureTheory.eLpNorm g (ENNReal.ofReal p₀) μ) ^ p₀
      = ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p₀)
        (ENNReal.ofReal_pos.mpr hp₀).ne' ENNReal.ofReal_ne_top hgm, ENNReal.toReal_ofReal hp₀.le]
    rw [← ENNReal.rpow_mul, show (1 / p₀) * p₀ = 1 by field_simp, ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [hg, enorm_indicator_eq_indicator_enorm]
    rw [show (Set.indicator S' (fun a => ‖f a‖ₑ) x) ^ p₀
          = Set.indicator S' (fun a => (‖f a‖ₑ) ^ p₀) x from by
        by_cases hx : x ∈ S'
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp₀]]
    by_cases hx : x ∈ S'
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp₀.le]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  -- the high part is controlled by the weak (q,q) bound
  have termh : ν {x : β | ENNReal.ofReal (lam / 2) < T h x}
      ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
    calc ν {x : β | ENNReal.ofReal (lam / 2) < T h x}
        ≤ ENNReal.ofReal (A / (lam / 2)) ^ q *
            (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q :=
          hweakq h (lam / 2) (by linarith)
      _ = ENNReal.ofReal (2 * A / lam) ^ q *
            (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q := by
          rw [show A / (lam / 2) = 2 * A / lam by field_simp]
      _ = ENNReal.ofReal (2 * A / lam) ^ q *
            ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
          rw [hHeq]
  -- the low part is controlled by the weak (p₀,p₀) bound
  have termp : ν {x : β | ENNReal.ofReal (lam / 2) < T g x}
      ≤ ENNReal.ofReal (2 * B / lam) ^ p₀ *
          ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
    calc ν {x : β | ENNReal.ofReal (lam / 2) < T g x}
        ≤ ENNReal.ofReal (B / (lam / 2)) ^ p₀ *
            (MeasureTheory.eLpNorm g (ENNReal.ofReal p₀) μ) ^ p₀ :=
          hweakp g (lam / 2) (by linarith)
      _ = ENNReal.ofReal (2 * B / lam) ^ p₀ *
            (MeasureTheory.eLpNorm g (ENNReal.ofReal p₀) μ) ^ p₀ := by
          rw [show B / (lam / 2) = 2 * B / lam by field_simp]
      _ = ENNReal.ofReal (2 * B / lam) ^ p₀ *
            ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
          rw [hGeq]
  -- level-set inclusion and union bound
  have hsubset : {x : β | ENNReal.ofReal lam < T f x} ⊆
      {x : β | ENNReal.ofReal (lam / 2) < T h x} ∪ {x : β | ENNReal.ofReal (lam / 2) < T g x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hcon
    rw [not_or] at hcon
    have hsum : T f x ≤ T h x + T g x := by
      have h1 := hsub h g x
      rwa [hgh] at h1
    have hle : T f x ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal (lam / 2) :=
      hsum.trans (add_le_add (not_lt.mp hcon.1) (not_lt.mp hcon.2))
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      show lam / 2 + lam / 2 = lam by ring] at hle
    exact absurd hle (not_le.mpr hx)
  calc ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ν ({x : β | ENNReal.ofReal (lam / 2) < T h x} ∪
            {x : β | ENNReal.ofReal (lam / 2) < T g x}) := measure_mono hsubset
    _ ≤ ν {x : β | ENNReal.ofReal (lam / 2) < T h x} +
          ν {x : β | ENNReal.ofReal (lam / 2) < T g x} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ
        + ENNReal.ofReal (2 * B / lam) ^ p₀ *
          ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ :=
        add_le_add termh termp

end Work.BourgainPlan.Maximal
