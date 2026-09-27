import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLComp.MaxLeafAux
import Submission.Work.EKLComp.atom_bad_bound
import Submission.Work.EKLComp.condexp_atom_bound

namespace Work.EKLComp

open MeasureTheory
open Work.EKLContract
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- The indicator bound `⨆_n ofReal (min a n) = ofReal a` for `a ≥ 0`. -/
private lemma iSup_ofReal_min (a : ℝ) (ha : 0 ≤ a) :
    (⨆ n : ℕ, ENNReal.ofReal (min a (n : ℝ))) = ENNReal.ofReal a := by
  apply le_antisymm
  · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
  · obtain ⟨n, hn⟩ := exists_nat_ge a
    exact le_iSup_of_le n (le_of_eq (by rw [min_eq_left hn]))

theorem condexp_atom_bound_borel (N : ℕ) (i j : Fin 3) (hij : i ≠ j)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (X' : Set Work.EKLContract.X3)
    (hν : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X')
    (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfint : MeasureTheory.Integrable f μ) (α : ℝ) (hα : 0 < α)
    (Z : Set Work.EKLContract.X3) (Y'' : Set Work.EKLContract.X3)
    (hY'' : @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 Y'')
    (hY''Z : Y'' ⊆ Z)
    (m : MeasurableSpace Work.EKLContract.X3)
    (hplaque : Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z m)
    (hpoint : ∀ x ∈ Z ∩ X', ENNReal.ofReal α *
        ν x {u : Work.EKLContract.SL3 |
          u ∈ Work.EKLContract.shape m (Work.EKLContract.Uij hij) x ∧ u • x ∈ Y''}
      ≤ (N : ENNReal) * ∫⁻ u in Work.EKLContract.shape m (Work.EKLContract.Uij hij) x,
          ENNReal.ofReal (f (u • x)) ∂(ν x)) :
    α * (μ Y'').toReal ≤ (N : ℝ) * ∫ x, f x ∂μ := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  have hZb : MeasurableSet Z := hplaque.1 Z hplaque.2.2.1
  have hY''b : MeasurableSet Y'' := hY''
  have hXae : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff, show {a : X3 | ¬ a ∈ X'} = X'ᶜ from rfl]
    exact hν.conull
  have hmuYtop : μ Y'' < ⊤ := by
    have h1 : μ Y'' ≤ 1 := by
      rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ Y'')
    exact lt_of_le_of_lt h1 ENNReal.one_lt_top
  -- The pointwise identity for the indicator of `Y''`
  have hident : ∀ x : X3, (∫⁻ u in shape m (Uij hij) x,
        ENNReal.ofReal ((Y''.indicator (fun _ : X3 => (1:ℝ))) (u • x)) ∂(ν x))
      = ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''} := by
    intro x
    have hset : MeasurableSet {u : SL3 | u • x ∈ Y''} := hY''b.preimage (measurable_smul_x x)
    have hfun : (fun u : SL3 => ENNReal.ofReal ((Y''.indicator (fun _ : X3 => (1:ℝ))) (u • x)))
        = {u : SL3 | u • x ∈ Y''}.indicator (fun _ => (1 : ENNReal)) := by
      funext u
      by_cases h : u • x ∈ Y''
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ {u : SL3 | u • x ∈ Y''} from h)]
        simp
      · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show u ∉ {u : SL3 | u • x ∈ Y''} from h)]
        simp
    rw [hfun]
    rw [show (∫⁻ u in shape m (Uij hij) x,
          {u : SL3 | u • x ∈ Y''}.indicator (fun _ => (1 : ENNReal)) u ∂(ν x))
        = ∫⁻ u, {u : SL3 | u • x ∈ Y''}.indicator (fun _ => (1 : ENNReal)) u
            ∂((ν x).restrict (shape m (Uij hij) x)) from rfl]
    rw [MeasureTheory.lintegral_indicator hset]
    rw [lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply hset, one_mul]
    congr 1
    ext u; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  -- Step 1: the indicator integral
  have hA_eq : (∫⁻ x in Z, (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''})
        / (ν x (shape m (Uij hij) x)) ∂μ) = μ Y'' := by
    have hgmeas : Measurable (Y''.indicator (fun _ : X3 => (1:ℝ))) :=
      Measurable.indicator measurable_const hY''b
    have hg0 : ∀ x, 0 ≤ (Y''.indicator (fun _ : X3 => (1:ℝ))) x := by
      intro x; by_cases hx : x ∈ Y''
      · rw [Set.indicator_of_mem hx]; norm_num
      · simp [Set.indicator_of_notMem hx]
    have hgb : ∃ C, ∀ x, |(Y''.indicator (fun _ : X3 => (1:ℝ))) x| ≤ C := by
      refine ⟨1, fun x => ?_⟩
      by_cases hx : x ∈ Y''
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    have hQ := lintegral_ratio_eq hij μ ν X' hν (Y''.indicator (fun _ : X3 => (1:ℝ)))
      hgmeas hg0 hgb m Z hplaque
    rw [show (∫⁻ x in Z, (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''})
            / (ν x (shape m (Uij hij) x)) ∂μ)
          = ∫⁻ x in Z, (∫⁻ u in shape m (Uij hij) x,
              ENNReal.ofReal ((Y''.indicator (fun _ : X3 => (1:ℝ))) (u • x)) ∂(ν x))
            / (ν x (shape m (Uij hij) x)) ∂μ from
        lintegral_congr (fun x => by rw [hident x])]
    rw [hQ]
    rw [show (∫ x in Z, (Y''.indicator (fun _ : X3 => (1:ℝ))) x ∂μ) = (μ Y'').toReal from by
      rw [MeasureTheory.setIntegral_indicator hY''b, MeasureTheory.setIntegral_const,
          MeasureTheory.Measure.real_def, smul_eq_mul, mul_one, Set.inter_eq_right.mpr hY''Z]]
    exact ENNReal.ofReal_toReal (ne_of_lt hmuYtop)
  -- Step 2: the integral identity for `f`
  have hB_eq : (∫⁻ x in Z, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
        / (ν x (shape m (Uij hij) x)) ∂μ) = ENNReal.ofReal (∫ x in Z, f x ∂μ) := by
    have hμZtop : μ Z < ⊤ := by
      have h1 : μ Z ≤ 1 := by
        rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ Z)
      exact lt_of_le_of_lt h1 ENNReal.one_lt_top
    haveI : IsFiniteMeasure (μ.restrict Z) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hμZtop)
    let gN : ℕ → X3 → ℝ := fun n x => min (f x) (n : ℝ)
    have hgNmeas : ∀ n, Measurable (gN n) := fun n => hf.min measurable_const
    have hgN0 : ∀ n x, 0 ≤ gN n x := fun n x => le_min (hf0 x) (Nat.cast_nonneg n)
    have hgNb : ∀ n, ∃ C, ∀ x, |gN n x| ≤ C := fun n => ⟨(n:ℝ), fun x => by
      rw [abs_of_nonneg (hgN0 n x)]; exact min_le_right _ _⟩
    have hgNint : ∀ n, Integrable (gN n) (μ.restrict Z) := fun n =>
      Integrable.of_bound (hgNmeas n).aestronglyMeasurable (n:ℝ)
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgN0 n x)]; exact min_le_right _ _))
    have hcNmeas : ∀ n, Measurable (fun x => ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x)) := by
      intro n
      have h : @MeasureTheory.StronglyMeasurable X3 ℝ _ m
          (condExp m (μ.restrict Z) (gN n)) := MeasureTheory.stronglyMeasurable_condExp
      exact (h.measurable.mono hplaque.1 le_rfl).ennreal_ofReal
    have hPN : ∀ n, (fun x => ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x)) =ᵐ[μ.restrict Z]
        (fun x => (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (gN n (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x))) :=
      fun n => ofReal_condExp_eq_ratio hij μ ν X' hν (gN n) (hgNmeas n) (hgN0 n) (hgNb n)
        m Z hplaque
    have hQn : ∀ n, (∫⁻ x in Z, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (gN n (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x)) ∂μ) = ENNReal.ofReal (∫ x in Z, gN n x ∂μ) :=
      fun n => lintegral_ratio_eq hij μ ν X' hν (gN n) (hgNmeas n) (hgN0 n) (hgNb n) m Z hplaque
    have hsup : ∀ x, (⨆ n, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (gN n (u • x)) ∂(ν x)))
        = ∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x) := by
      intro x
      have hmeas : ∀ n, Measurable (fun u : SL3 => ENNReal.ofReal (gN n (u • x))) := fun n =>
        ((hgNmeas n).comp (measurable_smul_x x)).ennreal_ofReal
      have hmono : Monotone (fun n => fun u : SL3 => ENNReal.ofReal (gN n (u • x))) := by
        intro a b hab u
        exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
      have hpt : ∀ u : SL3, (⨆ n, ENNReal.ofReal (gN n (u • x))) = ENNReal.ofReal (f (u • x)) :=
        fun u => iSup_ofReal_min (f (u • x)) (hf0 (u • x))
      calc (⨆ n, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (gN n (u • x)) ∂(ν x)))
          = (⨆ n, ∫⁻ u, ENNReal.ofReal (gN n (u • x))
                ∂((ν x).restrict (shape m (Uij hij) x))) := rfl
        _ = ∫⁻ u, (⨆ n, ENNReal.ofReal (gN n (u • x)))
                ∂((ν x).restrict (shape m (Uij hij) x)) :=
              (MeasureTheory.lintegral_iSup hmeas hmono).symm
        _ = ∫⁻ u, ENNReal.ofReal (f (u • x)) ∂((ν x).restrict (shape m (Uij hij) x)) := by
              apply lintegral_congr; intro u; exact hpt u
        _ = ∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x) := rfl
    have hstep3 : (∫⁻ x in Z, (⨆ n, (∫⁻ u in shape m (Uij hij) x,
            ENNReal.ofReal (gN n (u • x)) ∂(ν x)) / (ν x (shape m (Uij hij) x))) ∂μ)
        = ∫⁻ x in Z, (⨆ n, ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [MeasureTheory.ae_all_iff.mpr (fun n => hPN n)] with x hx
      exact (iSup_congr (fun n => hx n)).symm
    have hstep4 : (∫⁻ x in Z, (⨆ n, ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x)) ∂μ)
        = (⨆ n, ∫⁻ x in Z, ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x) ∂μ) := by
      rw [MeasureTheory.lintegral_iSup_ae (fun n => hcNmeas n) (fun n => by
        have hm : gN n ≤ᵐ[μ.restrict Z] gN (n.succ) :=
          Filter.Eventually.of_forall (fun x =>
            min_le_min_left _ (by exact_mod_cast Nat.le_succ n))
        filter_upwards [MeasureTheory.condExp_mono (hgNint n) (hgNint (n.succ)) hm] with x hx
        exact ENNReal.ofReal_le_ofReal hx)]
    have hstep5 : (⨆ n, ∫⁻ x in Z, ENNReal.ofReal (condExp m (μ.restrict Z) (gN n) x) ∂μ)
        = (⨆ n, ENNReal.ofReal (∫ x in Z, gN n x ∂μ)) := by
      congr 1
      funext n
      exact (MeasureTheory.lintegral_congr_ae (hPN n)).trans (hQn n)
    have hstep6 : (⨆ n, ENNReal.ofReal (∫ x in Z, gN n x ∂μ))
        = ENNReal.ofReal (∫ x in Z, f x ∂μ) := by
      have hofN : ∀ n, ENNReal.ofReal (∫ x in Z, gN n x ∂μ)
          = ∫⁻ x in Z, ENNReal.ofReal (gN n x) ∂μ := by
        intro n
        rw [show (∫ x in Z, gN n x ∂μ) = ∫ x, gN n x ∂(μ.restrict Z) from rfl]
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hgNint n)
              (Filter.Eventually.of_forall (hgN0 n))]
      rw [show (⨆ n, ENNReal.ofReal (∫ x in Z, gN n x ∂μ))
            = (⨆ n, ∫⁻ x in Z, ENNReal.ofReal (gN n x) ∂μ) from by
          congr 1; funext n; exact hofN n]
      rw [← MeasureTheory.lintegral_iSup (μ := μ.restrict Z)
            (f := fun n x => ENNReal.ofReal (gN n x))
            (fun n => (hgNmeas n).ennreal_ofReal)
            (fun a b hab x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab)))]
      rw [show (∫⁻ x in Z, (⨆ n, ENNReal.ofReal (gN n x)) ∂μ)
            = ∫⁻ x in Z, ENNReal.ofReal (f x) ∂μ from by
          apply lintegral_congr; intro x; exact iSup_ofReal_min (f x) (hf0 x)]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint.restrict
            (Filter.Eventually.of_forall hf0)]
    rw [show (∫⁻ x in Z, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
            / (ν x (shape m (Uij hij) x)) ∂μ)
        = ∫⁻ x in Z, (⨆ n, (∫⁻ u in shape m (Uij hij) x,
              ENNReal.ofReal (gN n (u • x)) ∂(ν x))) / (ν x (shape m (Uij hij) x)) ∂μ from by
          apply lintegral_congr; intro x; rw [← hsup x]]
    rw [show (∫⁻ x in Z, (⨆ n, (∫⁻ u in shape m (Uij hij) x,
              ENNReal.ofReal (gN n (u • x)) ∂(ν x))) / (ν x (shape m (Uij hij) x)) ∂μ)
        = ∫⁻ x in Z, (⨆ n, (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (gN n (u • x)) ∂(ν x))
              / (ν x (shape m (Uij hij) x))) ∂μ from by
          apply lintegral_congr; intro x; rw [ENNReal.iSup_div]]
    rw [hstep3, hstep4, hstep5, hstep6]
  -- Step 3: combine
  have hav : ∀ᵐ x ∂(μ.restrict Z), ENNReal.ofReal α *
        (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''} / (ν x (shape m (Uij hij) x)))
      ≤ (N : ENNReal) * ((∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x))) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hXae, MeasureTheory.ae_restrict_mem hZb]
      with x hxX hxZ
    have h := hpoint x ⟨hxZ, hxX⟩
    have h2 := ENNReal.div_le_div_right h (ν x (shape m (Uij hij) x))
    calc ENNReal.ofReal α * (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''}
            / (ν x (shape m (Uij hij) x)))
        = (ENNReal.ofReal α * ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''})
            / (ν x (shape m (Uij hij) x)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      _ ≤ ((N : ENNReal) * ∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
            / (ν x (shape m (Uij hij) x)) := h2
      _ = (N : ENNReal) * ((∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
            / (ν x (shape m (Uij hij) x))) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  have hZpoint : (∫⁻ x in Z, ENNReal.ofReal α *
        (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''} / (ν x (shape m (Uij hij) x))) ∂μ)
      ≤ ∫⁻ x in Z, (N : ENNReal) *
        ((∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x))) ∂μ :=
    lintegral_mono_ae hav
  have hLHS : (∫⁻ x in Z, ENNReal.ofReal α *
        (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''} / (ν x (shape m (Uij hij) x))) ∂μ)
      = ENNReal.ofReal α * μ Y'' := by
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal α)
      (fun x => ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''} / (ν x (shape m (Uij hij) x)))
      ENNReal.ofReal_ne_top]
    rw [hA_eq]
  have hRHS : (∫⁻ x in Z, (N : ENNReal) *
        ((∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x))) ∂μ)
      = (N : ENNReal) * ENNReal.ofReal (∫ x in Z, f x ∂μ) := by
    rw [MeasureTheory.lintegral_const_mul' (N : ENNReal)
      (fun x => (∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
          / (ν x (shape m (Uij hij) x))) (ENNReal.natCast_ne_top N)]
    rw [hB_eq]
  have hmain : ENNReal.ofReal α * μ Y''
      ≤ (N : ENNReal) * ENNReal.ofReal (∫ x in Z, f x ∂μ) :=
    calc ENNReal.ofReal α * μ Y''
        = ∫⁻ x in Z, ENNReal.ofReal α *
            (ν x {u : SL3 | u ∈ shape m (Uij hij) x ∧ u • x ∈ Y''}
              / (ν x (shape m (Uij hij) x))) ∂μ := hLHS.symm
      _ ≤ ∫⁻ x in Z, (N : ENNReal) *
            ((∫⁻ u in shape m (Uij hij) x, ENNReal.ofReal (f (u • x)) ∂(ν x))
              / (ν x (shape m (Uij hij) x))) ∂μ := hZpoint
      _ = (N : ENNReal) * ENNReal.ofReal (∫ x in Z, f x ∂μ) := hRHS
  have hlm : ENNReal.ofReal α * μ Y'' = ENNReal.ofReal (α * (μ Y'').toReal) := by
    rw [ENNReal.ofReal_mul (le_of_lt hα), ENNReal.ofReal_toReal (ne_of_lt hmuYtop)]
  have hrm : (N : ENNReal) * ENNReal.ofReal (∫ x in Z, f x ∂μ)
      = ENNReal.ofReal ((N : ℝ) * ∫ x in Z, f x ∂μ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
  rw [hlm, hrm] at hmain
  have hreal : α * (μ Y'').toReal ≤ (N : ℝ) * ∫ x in Z, f x ∂μ := by
    have hq : 0 ≤ (N : ℝ) * ∫ x in Z, f x ∂μ :=
      mul_nonneg (Nat.cast_nonneg N) (MeasureTheory.integral_nonneg hf0)
    rw [ENNReal.ofReal_le_ofReal_iff hq] at hmain
    exact hmain
  refine le_trans hreal ?_
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0))
    (Nat.cast_nonneg N)


end

end Work.EKLComp
