import Mathlib
import Submission.Work.EKLC6Core.box_mass_asymptotic_condExp
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.log_mass_conjBox_eq_sum
import Submission.Work.EKLC6Core.box_UBox_comparison
import Submission.Work.EKLComp.prove_Birkhoff

/-!
# `box_mass_asymptotic_condExp_mp` — Pisa 7.18 with the measure-preserving hypothesis only at `t`

The sibling theorem `Work.EKLC6Core.box_mass_asymptotic_condExp` assumes the full
`A`-invariance `IsAInvariant μ` (measure preservation for *every* `t : Fin 3 → ℝ`), and then
uses it only twice: at the given `t` and at its natural multiples `j • t` (`j : ℕ`).  This
module repeats the very same Birkhoff-average computation with the weaker hypothesis that
`x ↦ aDiag t • x` alone is measure preserving; measure preservation at the multiples `j • t`
is recovered from `MeasurePreserving.iterate` and the identity `iterate_aDiag`.

The content is otherwise identical to `box_mass_asymptotic_condExp`: computing the exponential
growth rate of the `ν x`-masses of the conjugated entry boxes `conjBy (-n t) (UBox (Uminus t) R)`
as the Birkhoff average of `growthFun (Uminus t) ν t`, whose limit is the conditional
expectation onto the invariants of the `aDiag t`-action.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core.HcondSigFree

open Work.EKLC6Core Work.EKLContract

theorem box_mass_asymptotic_condExp_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {R : ℝ} (hR : 2 ≤ R) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log ((ν x (Work.EKLC6Core.conjBy
        (-(((n : ℝ)) • t)) (Work.EKLC6Core.UBox (Work.EKLC6Core.Uminus t) R))).toReal))
      Filter.atTop (nhds (MeasureTheory.condExp (MeasurableSpace.invariants
        (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)) μ
        (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) x)) := by
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  set g : X3 → ℝ := growthFun (Uminus t) ν t with hg
  set T : X3 → X3 := fun x => aDiag t • x with hT
  have hmpT : MeasurePreserving T μ μ := hmp
  set L : X3 → ℝ := condExp (MeasurableSpace.invariants T) μ g with hLdef
  have hBox1UBox : Box1 (Uminus t) ⊆ UBox (Uminus t) R := (box_UBox_comparison t hR1).1
  obtain ⟨KU, hKU⟩ := (box_UBox_comparison t hR1).2
  -- The multiples of `t` are measure preserving, by iteration of `hmp`.
  have hAinv_n : ∀ j : ℕ, MeasurePreserving (fun x : X3 => aDiag (((j : ℝ)) • t) • x) μ μ := by
    intro j
    have h1 : MeasurePreserving (fun x : X3 => aDiag t • x)^[j] μ μ := hmp.iterate j
    have heq : (fun x : X3 => aDiag t • x)^[j]
        = (fun x : X3 => aDiag (((j : ℝ)) • t) • x) := by
      funext x
      exact iterate_aDiag t j x
    rwa [heq] at h1
  -- the a.e. orbit conditions
  have haeX' : ∀ᵐ x ∂μ, x ∈ X' :=
    MeasureTheory.ae_iff.mpr (by simpa [Set.compl_def] using hL.conull)
  have haeX'' : ∀ᵐ x ∂μ, x ∈ X'' :=
    MeasureTheory.ae_iff.mpr (by simpa [Set.compl_def] using hX'')
  have haeX : ∀ᵐ x ∂μ, x ∈ X' ∩ X'' := haeX'.and haeX''
  have hae_orbit : ∀ᵐ x ∂μ, ∀ j : ℕ, aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'' := by
    refine MeasureTheory.ae_all_iff.mpr (fun j => ?_)
    exact (hAinv_n j).quasiMeasurePreserving.ae haeX
  -- (A) the telescoping identity
  have htel : ∀ᵐ x ∂μ, ∀ n : ℕ, bmce_logMass t ν (-(((n : ℝ)) • t)) x
      = ∑ j ∈ Finset.range n, g (T^[j + 1] x) := by
    refine MeasureTheory.ae_all_iff.mpr (fun n => ?_)
    filter_upwards [hae_orbit] with x hx
    have h := log_mass_conjBox_eq_sum t hL hcov n x (fun j _ => hx j)
    rw [show bmce_logMass t ν (-(((n : ℝ)) • t)) x
        = Real.log ((ν x (conjBox (Uminus t) (-(((n : ℝ)) • t)))).toReal) from rfl, h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hvec : (((j + 1 : ℕ) : ℝ) • t : Fin 3 → ℝ) = ((j : ℝ) + 1) • t := by
      rw [show (((j + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) by push_cast; ring]
    simp only [hg, hT]
    rw [iterate_aDiag, hvec]
  -- (B) the Birkhoff averages converge to `L`
  have hbirk : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA T g n x) atTop (𝓝 (L x)) := by
    filter_upwards [Work.EKLComp.birkhoff_all μ T hmpT g hint] with x hx
    simpa [L] using hx
  -- (C) the shifted averages
  have hAtend : ∀ᵐ x ∂μ,
      Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, g (T^[j + 1] x))
        atTop (𝓝 (L x)) := by
    filter_upwards [hbirk] with x hx
    have hsumid : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), g (T^[k] x)) - g x
        = ∑ j ∈ Finset.range n, g (T^[j + 1] x) := by
      intro n
      rw [Finset.sum_range_succ', Function.iterate_zero_apply]
      ring
    have hinv0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g (T^[k] x))
        atTop (𝓝 (L x)) := by
      have hbirk' : Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          atTop (𝓝 (L x)) := hx.comp (tendsto_add_atTop_nat 1)
      have hratio : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hinv0
        rw [add_zero] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      have hprod : Tendsto (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) * Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          atTop (𝓝 (1 * L x)) := hratio.mul hbirk'
      rw [one_mul] at hprod
      have heq : (fun n : ℕ =>
            (((n + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) * Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g (T^[k] x)) := by
        funext n
        rw [Work.EKLComp.Birkhoff.birkA_def]
        by_cases hn : n = 0
        · subst hn; simp
        · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
          have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          field_simp
      rw [heq] at hprod
      exact hprod
    have h2 : Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (n + 1), g (T^[k] x)) - (n : ℝ)⁻¹ * g x)
        atTop (𝓝 (L x)) := by
      have h := h1.sub (hinv0.mul_const (g x))
      simpa using h
    have heq2 : (fun n : ℕ => (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (n + 1), g (T^[k] x))
          - (n : ℝ)⁻¹ * g x)
        = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (T^[j + 1] x)) := by
      funext n
      rw [← mul_sub, hsumid n]
    rw [heq2] at h2
    exact h2
  -- (D) rewrite the telescoping identity in `bmce_logMass` form
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-(((n : ℝ)) • t)) x)
        atTop (𝓝 (L x)) := by
    filter_upwards [hAtend, htel] with x hA ht
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-(((n : ℝ)) • t)) x)
        = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (T^[j + 1] x)) := by
      funext n
      rw [ht n]
    rw [← heq] at hA
    exact hA
  -- (E) the `KU`-shift of the same limit
  have hlimS : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-((((n + KU : ℕ) : ℝ)) • t)) x)
        atTop (𝓝 (L x)) := by
    filter_upwards [hAtend, htel] with x hA ht
    have hinv0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hφtop : Tendsto (fun n : ℕ => n + KU) atTop atTop := tendsto_add_atTop_nat KU
    have hφratio : Tendsto (fun n : ℕ => (((n + KU : ℕ) : ℝ)) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => 1 + (KU : ℝ) * (n : ℝ)⁻¹) atTop
          (𝓝 (1 + (KU : ℝ) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinv0)
      rw [mul_zero, add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
      rw [Nat.cast_add]
      field_simp
    have hmain := bmce_tendsto_inv_mul_sum_shift hA hφtop hφratio
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + KU), g (T^[j + 1] x))
        = (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-((((n + KU : ℕ) : ℝ)) • t)) x) := by
      funext n
      rw [ht (n + KU)]
    rw [heq] at hmain
    exact hmain
  -- (F) the final sandwich with the `UBox`-box
  have hsubLow : ∀ n : ℕ, conjBox (Uminus t) (-(((n : ℝ)) • t))
      ⊆ conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R) :=
    fun n => conjBy_mono (-(((n : ℝ)) • t)) hBox1UBox
  have hsubUp : ∀ n : ℕ, conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R)
      ⊆ conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)) := by
    intro n
    have hstep : UBox (Uminus t) R ⊆ conjBox (Uminus t) (-(((KU : ℕ) : ℝ) • t)) := by
      have h := conjBy_mono (-(((KU : ℕ) : ℝ) • t)) (hKU KU le_rfl)
      rwa [conjBy_neg_conjBy] at h
    have h2 := conjBy_mono (-(((n : ℝ)) • t)) hstep
    have h3 : conjBy (-(((n : ℝ)) • t)) (conjBox (Uminus t) (-(((KU : ℕ) : ℝ) • t)))
        = conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)) := by
      rw [← conjBox_add]
      congr 1
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rwa [h3] at h2
  filter_upwards [haeX, hlim, hlimS] with x hxX hxlim hxupU
  have hgoal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal)) atTop (𝓝 (L x)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hxlim hxupU ?_ ?_
    · filter_upwards with n
      have hfin : ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R)) < ⊤ :=
        (hL.radon x hxX.1).lt_top_of_isCompact (bmce_isCompact_conjBy_UBox t hR0 _)
      have hle := bmce_log_mass_le hL hxX.1 (hsubLow n)
        (bmce_box1_subset_conjBox_neg_nsmul t n) hfin
      have hle' : Real.log ((ν x (conjBox (Uminus t) (-(((n : ℝ)) • t)))).toReal)
          ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal) := hle
      exact mul_le_mul_of_nonneg_left hle' (inv_nonneg.mpr (Nat.cast_nonneg n))
    · filter_upwards with n
      have hfin : ν x (conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t))) < ⊤ :=
        (conjBox_mass_pos hL hU _ hxX.1).2
      have hA : Box1 (Uminus t) ⊆ conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R) :=
        (bmce_box1_subset_conjBox_neg_nsmul t n).trans (hsubLow n)
      have hle := bmce_log_mass_le hL hxX.1 (hsubUp n) hA hfin
      have hle' : Real.log ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal)
          ≤ Real.log ((ν x (conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)))).toReal) := hle
      exact mul_le_mul_of_nonneg_left hle' (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact hgoal

end Work.EKLC6Core.HcondSigFree
